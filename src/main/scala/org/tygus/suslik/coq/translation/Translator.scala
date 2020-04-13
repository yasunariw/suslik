package org.tygus.suslik.coq.translation

import org.tygus.suslik.coq.language.Expressions._
import org.tygus.suslik.coq.language.Statements._
import org.tygus.suslik.coq.language._
import org.tygus.suslik.coq.logic._
import org.tygus.suslik.language._
import org.tygus.suslik.logic._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications.{Assertion, Goal}
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.OperationalRules._
import org.tygus.suslik.synthesis.rules.LogicalRules._
import org.tygus.suslik.synthesis.rules.UnfoldingRules._

object Translator {
  def runProcedure(el: Procedure, trace: Trace): CProcedure = {
    val cTp = runSSLType(el.tp)
    val cFormals = el.formals.map(runParam)
    val stmt = runStmtFromTrace(trace)
    CProcedure(el.name, cTp, cFormals, stmt, trace.inductive)
  }

  def runFunSpecFromTrace(trace: Trace): CFunSpec = {
    val FunSpec(_, tp, _, _, _, _) = trace.spec
    val root = trace.root.get
    val goal = root.goal
    val pureParams = goal.universalGhosts.map(v => runParam((goal.gamma(v), v))).toList
    CFunSpec(goal.fname, runSSLType(tp), goal.formals.map(runParam), pureParams, runAsn(goal.pre), runAsn(goal.post), trace.inductive)
  }

  def runInductivePredicate(el: InductivePredicate): CInductivePredicate = {
    val cParams = el.params.map(runParam) :+ (CHeapType, CVar("h"))
    val cClauses = el.clauses.zipWithIndex.map { case (c, i) => runClause(s"${el.name}$i", c) }
    CInductivePredicate(el.name, cParams, cClauses)
  }

  def runSSLType(el: SSLType): CoqType = el match {
    case BoolType => CBoolType
    case IntType => CNatType
    case LocType => CPtrType
    case IntSetType => CNatSeqType
    case VoidType => CUnitType
  }

  def runGoal(goal: Goal): CGoal = {
    val pre = runAsn(goal.pre)
    val post = runAsn(goal.post)
    val gamma = goal.gamma.map { case (value, lType) => (CVar(value.name), runSSLType(lType)) }
    val programVars = goal.programVars.map(v => CVar(v.name))
    val universalGhosts = goal.universalGhosts.map(v => CVar(v.name)).toSeq
    CGoal(pre, post, gamma, programVars, universalGhosts, goal.fname)
  }

  def runProofFromTrace(trace: Trace, predicates: PredicateEnv): CProof = {
    val inductive = trace.inductive

    def traverse(goalTrace: GoalTrace, env: CEnvironment): CProofStep = {
      val ruleAppTraceOpt = goalTrace.ruleApps.find(!_.isFail)
      assert(ruleAppTraceOpt.isDefined, s"No successful rule application found for goal ${goalTrace.goal.pp}")
      val ruleAppTrace = ruleAppTraceOpt.get
      assert(ruleAppTrace.alts.nonEmpty, s"No derivation found for rule app ${ruleAppTrace.rule}")
      val altTrace = ruleAppTrace.alts.head
      val subgoals = altTrace.subgoals
      val subderiv = altTrace.alt
      val ruleApp = (ruleAppTrace.rule, subderiv.comp) match {
        case (EmpRule, _) =>
          Some(CEmp)
        case (ReadRule, _) =>
          // special case: Read is followed immediately by Call
          if (subgoals.nonEmpty && subgoals.head.ruleApps.head.rule.isInstanceOf[CallRule.type]) {
            None
          } else {
            Some(CRead)
          }
        case (WriteRuleOld, Prepend(Store(to, _, _))) =>
          Some(CWriteOld(CVar(to.name)))
        case (FreeRule, PrependFree(_, sz)) =>
          Some(CFreeRuleApp(sz))
        case (CallRule, PrependCall(Call(to, fun, args), sub)) =>
          val csub = sub.map { case (k, v) => (CVar(k.name), runExpr(v))}
          Some(CCallRuleApp(env, fun.name, args.map(arg => runExpr(arg).asInstanceOf[CVar]), csub))
        case (Open, MakeOpen(selectors, app)) =>
          Some(COpen(env, selectors.map(runExpr), runHeaplet(app).asInstanceOf[CSApp]))
        case _ =>
          assert(subderiv.subgoals.length <= 1, "Shouldn't be skipping a rule app with multiple subgoals")
          None
      }

      ruleApp match {
        case Some(app) =>
          val nextEnv = app.nextEnvs(env, runGoal(goalTrace.goal))
          CProofStep(app, subgoals.zip(nextEnv).map {
            case (t, env1) => traverse(t, env1)
          })
        case None =>
          traverse(subgoals.head, env)
      }
    }

    val root = trace.root.get

    val initialGoal = runGoal(root.goal)
    val cpreds = predicates.mapValues(runInductivePredicate)
    val spec = runFunSpecFromTrace(trace)
    val env = CEnvironment(initialGoal, spec, Map.empty, cpreds, Seq.empty, inductive)
    val ruleApp = CGhostElim(env)
    val nextEnv = ruleApp.nextEnvs(env, initialGoal)

    CProof(CProofStep(ruleApp, Seq(traverse(root, nextEnv.head))))
  }

  def runStmtFromTrace(trace: Trace): CStatement = {
    def traverse(goalTrace: GoalTrace): CStatement = {
      val subgoals = goalTrace.ruleApps.head.alts.head.subgoals
      goalTrace.ruleApps.head.alts.head.alt.comp match {
        case PureKont =>
          traverse(subgoals.head)
        case Prepend(s) =>
          val stmt = s match {
            case Skip => CSkip
            case Malloc(to, tpe, sz) =>
              CMalloc(CVar(to.name), runSSLType(tpe), sz)
            case Load(to, tpe, from, offset) =>
              CLoad(CVar(to.name), runSSLType(tpe), CVar(from.name), offset)
            case Store(to, offset, expr) =>
              CStore(CVar(to.name), offset, runExpr(expr))
          }
          CSeqComp(stmt, traverse(subgoals.head)).simplify
        case PrependCall(s, _) =>
          val Call(to, fun, args) = s.asInstanceOf[Call]
          val stmt = CCall(to.map { case (v, t) => (CVar(v.name), runSSLType(t)) }, CVar(fun.name), args.map(runExpr))
          CSeqComp(stmt, traverse(subgoals.head)).simplify
        case PrependFree(s, sz) =>
          val free = s.asInstanceOf[Free]
          val base = CFree(CVar(free.v.name)).asInstanceOf[CStatement]
          val stmt = (1 until sz).foldLeft(base)((acc, n) => CSeqComp(CFree(CVar(free.v.name), n), acc))
          CSeqComp(stmt, traverse(subgoals.head)).simplify
        case PrependFromSketch(s) => ???
        case Append(s) => ???
        case MakeSkip =>
          CSkip
        case MakeError =>
          CError
        case MakeMagic =>
          CMagic
        case MakeGuarded(cond) =>
          CGuarded(runExpr(cond), traverse(subgoals.head))
        case MakeOpen(selectors, _) =>
          val stmts = subgoals.map(traverse)
          def mkNestedIf(branches: List[(CExpr, CStatement)]): CStatement = branches match {
            case b :: Nil => b._2
            case b :: rest => CIf(b._1, b._2, mkNestedIf(rest)).simplify
          }
          mkNestedIf(selectors.map(runExpr).zip(stmts).toList)
        case MakeIf(cond) =>
          CIf(runExpr(cond), traverse(subgoals.head), traverse(subgoals.last))
        case MakeAbduceCall(n) =>
          val writes = subgoals.take(n)
          val rest = subgoals.drop(n).head
          writes.foldRight(traverse(rest)) { case (w, r) => CSeqComp(traverse(w), r) }
      }

    }

    trace.root match {
      case Some(goalTrace) =>
        traverse(goalTrace)
      case None =>
        CError
    }
  }

  private def runParam(el: (SSLType, Var)): (CoqType, CVar) = el match {
    case (BoolType, Var(name)) => (CBoolType, CVar(name))
    case (IntType, Var(name)) => (CNatType, CVar(name))
    case (LocType, Var(name)) => (CPtrType, CVar(name))
    case (IntSetType, Var(name)) => (CNatSeqType, CVar(name))
    case (VoidType, Var(name)) => (CUnitType, CVar(name))
  }

  private def runClause(name: String, el: InductiveClause): CInductiveClause = {
    val selector = runExpr(el.selector)
    CInductiveClause(name, selector, runAsn(el.asn))
  }

  private def runExpr(el: Expr): CExpr = el match {
    case Var(name) => CVar(name)
    case BoolConst(value) => CBoolConst(value)
    case IntConst(value) => CNatConst(value)
    case el@UnaryExpr(_, _) => runUnaryExpr(el)
    case el@BinaryExpr(_, _, _) => runBinaryExpr(el)
    case el@OverloadedBinaryExpr(_, _, _) => runOverloadedBinaryExpr(el)
    case SetLiteral(elems) => CSetLiteral(elems.map(e => runExpr(e)))
    case IfThenElse(c, t, e) => CIfThenElse(runExpr(c), runExpr(t), runExpr(e))
  }

  private def runHeaplet(el: Heaplet): CExpr = el match {
    case PointsTo(loc, offset, value) => CPointsTo(runExpr(loc), offset, runExpr(value))
    case SApp(pred, args, tag) => CSApp(pred, args.map(runExpr), tag)
  }

  private def runAsn(el: Assertion): CAssertion =
    CAssertion(runExpr(el.phi), runSFormula(el.sigma))

  private def runSFormula(el: SFormula): CSFormula = {
    val ptss = el.ptss.map(runHeaplet).asInstanceOf[List[CPointsTo]]
    val apps = el.apps.map(runHeaplet).asInstanceOf[List[CSApp]]
    CSFormula("h", apps, ptss)
  }

  private def runUnaryExpr(el: UnaryExpr) : CExpr = el match {
    case UnaryExpr(OpNot, e) => e match {
      case BinaryExpr(OpEq, left, right) => COverloadedBinaryExpr(COpNotEqual, runExpr(left), runExpr(right))
      case _ => CUnaryExpr(COpNot, runExpr(e))
    }
    case UnaryExpr(OpUnaryMinus, e) => ???
  }

  private def runOverloadedBinaryExpr(el: OverloadedBinaryExpr) : CExpr = el match {
    case OverloadedBinaryExpr(OpOverloadedEq, l, r) =>
      COverloadedBinaryExpr(COpOverloadedEq, runExpr(l), runExpr(r))
    case OverloadedBinaryExpr(OpNotEqual, l, r) =>
      COverloadedBinaryExpr(COpNotEqual, runExpr(l), runExpr(r))
    case OverloadedBinaryExpr(OpGt, l, r) =>
      COverloadedBinaryExpr(COpGt, runExpr(l), runExpr(r))
    case OverloadedBinaryExpr(OpGeq, l, r) =>
      COverloadedBinaryExpr(COpGeq, runExpr(l), runExpr(r))
    case OverloadedBinaryExpr(OpGeq, l, r) =>
      COverloadedBinaryExpr(COpGeq, runExpr(l), runExpr(r))
    case OverloadedBinaryExpr(OpOverloadedPlus, l, r) =>
      COverloadedBinaryExpr(COpOverloadedPlus, runExpr(l), runExpr(r))
    case OverloadedBinaryExpr(OpOverloadedMinus, l, r) =>
      COverloadedBinaryExpr(COpOverloadedMinus, runExpr(l), runExpr(r))
    case OverloadedBinaryExpr(OpOverloadedLeq, l, r) =>
      COverloadedBinaryExpr(COpOverloadedLeq, runExpr(l), runExpr(r))
    case OverloadedBinaryExpr(OpOverloadedStar, l, r) =>
      COverloadedBinaryExpr(COpOverloadedStar, runExpr(l), runExpr(r))
  }

  private def runBinaryExpr(el: BinaryExpr) : CExpr = el match {
    case BinaryExpr(OpImplication, l, r) =>
      CBinaryExpr(COpImplication, runExpr(l), runExpr(r))
    case BinaryExpr(OpPlus, l, r) =>
      CBinaryExpr(COpPlus, runExpr(l), runExpr(r))
    case BinaryExpr(OpMinus, l, r) =>
      CBinaryExpr(COpMinus, runExpr(l), runExpr(r))
    case BinaryExpr(OpMultiply, l, r) =>
      CBinaryExpr(COpMultiply, runExpr(l), runExpr(r))
    case BinaryExpr(OpEq, l, r) =>
      CBinaryExpr(COpEq, runExpr(l), runExpr(r))
    case BinaryExpr(OpBoolEq, l, r) =>
      CBinaryExpr(COpBoolEq, runExpr(l), runExpr(r))
    case BinaryExpr(OpLeq, l, r) =>
      CBinaryExpr(COpLeq, runExpr(l), runExpr(r))
    case BinaryExpr(OpLt, l, r) =>
      CBinaryExpr(COpLt, runExpr(l), runExpr(r))
    case BinaryExpr(OpAnd, l, r) =>
      CBinaryExpr(COpAnd, runExpr(l), runExpr(r))
    case BinaryExpr(OpOr, l, r) =>
      CBinaryExpr(COpOr, runExpr(l), runExpr(r))
    case BinaryExpr(OpUnion, l, r) =>
      CBinaryExpr(COpUnion, runExpr(l), runExpr(r))
    case BinaryExpr(OpDiff, l, r) =>
      CBinaryExpr(COpDiff, runExpr(l), runExpr(r))
    case BinaryExpr(OpIn, l, r) =>
      CBinaryExpr(COpIn, runExpr(l), runExpr(r))
    case BinaryExpr(OpSetEq, l, r) =>
      CBinaryExpr(COpSetEq, runExpr(l), runExpr(r))
    case BinaryExpr(OpSubset, l, r) =>
      CBinaryExpr(COpSubset, runExpr(l), runExpr(r))
    case BinaryExpr(OpIntersect, l, r) =>
      CBinaryExpr(COpIntersect, runExpr(l), runExpr(r))
  }
}
