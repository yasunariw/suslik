package org.tygus.suslik.coq.translation

import org.tygus.suslik.coq.language.Expressions._
import org.tygus.suslik.coq.language.Statements._
import org.tygus.suslik.coq.language._
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

  def runFunSpecFromTrace(tp: SSLType, trace: Trace): CFunSpec = {
    val root = trace.root.get
    val goal = root.goal
    val pureParams = goal.universalGhosts.map(v => runParam((goal.gamma(v), v))).toList
    CFunSpec(goal.fname, runSSLType(tp), goal.formals.map(runParam), pureParams, runAsn(goal.pre), runAsn(goal.post))
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

  def runProofFromTrace(trace: Trace): CProof = {
    def next(ruleAppTrace: RuleAppTrace): Option[RuleAppTrace] = {
      assert(ruleAppTrace.alts.nonEmpty, "No derivation found; can only operate on a successful trace")
      val nextSubgoals = ruleAppTrace.alts.head.subgoals
      if (ruleAppTrace.alts.head.subgoals.nonEmpty) {
        Some(nextSubgoals.head.ruleApps.head)
      } else {
        None
      }
    }

    def traverse(ruleAppTrace: Option[RuleAppTrace]): List[CProofStep] = {
      if (ruleAppTrace.isEmpty) return List.empty
      val currTrace = ruleAppTrace.get
      currTrace.rule match {
        case ReadRule =>
          CRead :: traverse(next(currTrace))
        case WriteRuleOld =>
          assert(currTrace.alts.nonEmpty, "No derivation found; can only operate on a successful trace")
          assert(currTrace.alts.head.alt.comp.isInstanceOf[Prepend])
          val Prepend(comp) = currTrace.alts.head.alt.comp.asInstanceOf[Prepend]
          assert(comp.isInstanceOf[Store])
          val store = comp.asInstanceOf[Store]
          CWriteOld(CPointsTo(CVar(store.to.name), store.offset, Mystery)) :: traverse(next(currTrace))
        case EmpRule =>
          CEmp :: traverse(next(currTrace))
        case _ =>
          Console.println(currTrace.rule)
          assert(currTrace.alts.head.subgoals.length <= 1, "Shouldn't be skipping a rule app with multiple subgoals")
          traverse(next(currTrace))
      }
    }

    val formals = if (trace.inductive) {
      trace.root.get.goal.programVars.map(runExpr(_).asInstanceOf[CVar])
    } else List.empty
    val goal = trace.root.get.goal
    val ghosts = goal.universalGhosts.map(runExpr(_).asInstanceOf[CVar]).toList
    val ghostElim = CGhostElim(formals, ghosts, runAsn(goal.pre))

    CProof(ghostElim :: traverse(trace.root.map(_.ruleApps.head)))
  }

  def runStmtFromTrace(trace: Trace): CStatement = {
    def traverse(goalTrace: GoalTrace): CStatement = {
      val subgoals = goalTrace.ruleApps.head.alts.head.subgoals.reverse
      goalTrace.ruleApps.head.alts.head.alt.comp match {
        case PureKont =>
          traverse(subgoals.head)
        case Prepend(s) =>
          CSeqComp(runStmt(s, goalTrace.goal), traverse(subgoals.head)).simplify
        case PrependFromSketch(s) =>
          CSeqComp(runStmt(s, goalTrace.goal), traverse(subgoals.head))
        case Append(s) =>
          CSeqComp(traverse(subgoals.head), runStmt(s, goalTrace.goal)).simplify
        case MakeSkip =>
          CSkip
        case MakeError =>
          CError
        case MakeMagic =>
          CMagic
        case MakeGuarded(cond) =>
          CGuarded(runExpr(cond), traverse(subgoals.head))
        case MakeOpen(selectors) =>
          val stmts = subgoals.map(traverse)
          if (stmts.length == 1) stmts.head else {
            val cond_branches = selectors.zip(stmts).reverse
            val ctail = cond_branches.tail
            val finalBranch = cond_branches.head._2
            ctail.foldLeft(finalBranch) { case (eb, (c, tb)) => CIf(runExpr(c), tb, eb).simplify }
          }
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

  private def runStmt(el: Statement, goal: Goal): CStatement = el match {
    case Skip => CSkip
    case Hole => ???
    case Error => ???
    case Magic => ???
    case Malloc(to, tpe, sz) =>
      CMalloc(CVar(to.name), runSSLType(tpe), sz)
    case Free(v) =>
      val heaplets = FreeRule.findTargetHeaplets(goal)
      if (heaplets.isDefined) {
        return (1 until heaplets.get._1.sz)
          .foldLeft(CFree(CVar(v.name)).asInstanceOf[CStatement])((acc, n) => CSeqComp(CFree(CVar(v.name), n), acc))
      }
      CFree(CVar(v.name))
    case Load(to, tpe, from, offset) =>
      CLoad(CVar(to.name), runSSLType(tpe), CVar(from.name), offset)
    case Store(to, offset, expr) =>
      CStore(CVar(to.name), offset, runExpr(expr))
    case Call(to, fun, args) =>
      CCall(to.map { case (v, t) => (CVar(v.name), runSSLType(t)) }, CVar(fun.name), args.map(runExpr))
    case SeqComp(s1, s2) =>
      CSeqComp(runStmt(s1, goal), runStmt(s2, goal))
    case If(cond, tb, eb) =>
      CIf(runExpr(cond), runStmt(tb, goal), runStmt(eb, goal))
    case Guarded(cond, body) =>
      CGuarded(runExpr(cond), runStmt(body, goal))
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
