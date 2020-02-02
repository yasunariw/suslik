package org.tygus.suslik.coq.translation

import org.tygus.suslik.coq.language.Expressions._
import org.tygus.suslik.coq.language._
import org.tygus.suslik.language._
import org.tygus.suslik.logic._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic.Specifications.Assertion

object Translator {
  def runFunSpec(el: FunSpec, predicateEnv: CPredicateEnv) : CFunSpec = {
    val cParams = el.params.map(runParam)
    def extractPureParams(e: CExpr): Set[(CoqType, CVar)] = {
      val apps : Set[CSApp] = e.collect(_.isInstanceOf[CSApp])
      apps
        .flatMap(app => {
          val vars: Set[CVar] = app.collect(_.isInstanceOf[CVar])
          vars.zip(predicateEnv(app.pred).params).map {
            case (currParam, sigParam) => (sigParam._1, currParam)
          }
        })
        .filter(p => p._1 != CHeapType && !cParams.contains(p))
    }
    val cRType = runSSLType(el.rType)
    val cPre = runAsn(el.pre).simplify
    val cPost = runAsn(el.post).simplify
    val pureParams = extractPureParams(cPre) ++ extractPureParams(cPost)
    CFunSpec(el.name, cRType, cParams, pureParams.toList, cPre, cPost)
  }

  def runInductivePredicate(el: InductivePredicate) : CInductivePredicate = {
    val cParams = el.params.map(runParam) :+ (CHeapType, CVar("h"))
    val cClauses = el.clauses.zipWithIndex.map { case (c, i) => runClause(s"${el.name}$i", c) }
    CInductivePredicate(el.name, cParams, cClauses).refreshExistentials
  }

  def runSSLType(el: SSLType): CoqType = el match {
    case BoolType => CBoolType
    case IntType => CNatType
    case LocType => CPtrType
    case IntSetType => CNatSeqType
    case VoidType => CUnitType
  }

  private def runParam(el: (SSLType, Var)): (CoqType, CVar) = el match {
    case (BoolType, Var(name)) => (CBoolType, CVar(name))
    case (IntType, Var(name)) => (CNatType, CVar(name))
    case (LocType, Var(name)) => (CPtrType, CVar(name))
    case (IntSetType, Var(name)) => (CNatSeqType, CVar(name))
    case (VoidType, Var(name)) => (CUnitType, CVar(name))
  }

  private def runClause(name: String, el: InductiveClause): CInductiveClause =
    CInductiveClause(name, runExpr(el.selector), runAsn(el.asn))

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

  private def runAsn(el: Assertion): CExpr =
    CBinaryExpr(COpAnd, runExpr(el.phi), runSFormula(el.sigma))

  private def runSFormula(el: SFormula): CExpr = {
    val heapVarName = if (el.ptss.isEmpty) "h" else "h'"
    val appsAux: Seq[CExpr] = el.apps.map(app => CSApp(app.pred, app.args.map(arg => runExpr(arg)) :+ CVar(heapVarName), app.tag))
    val apps: Option[CExpr] = appsAux match {
      case Nil => None
      case hd :: tl => Some(tl.foldLeft(hd)((e, acc) => CBinaryExpr(COpAnd, e, acc)))
    }
    val ptss = el.ptss.map(h => runHeaplet(h)) match {
      case Nil => None
      case hd :: tl => Some(CBinaryExpr(COpEq, CVar("h"), (tl ++ Seq(CVar("h'"))).foldLeft(hd)((e, acc) => CBinaryExpr(COpHeapJoin, e, acc))))
    }

    (apps, ptss) match {
      case (Some(cApps), Some(cPtss)) => CBinaryExpr(COpAnd, cPtss, cApps)
      case (None, Some(cPtss)) => cPtss
      case (Some(cApps), None) => cApps
      case _ => CBinaryExpr(COpEq, CVar("h"), CEmpty)
    }
  }

  private def runHeaplet(el: Heaplet): CExpr = el match {
    case PointsTo(loc, offset, value) => CPointsTo(runExpr(loc), offset, runExpr(value))
    case Block(loc, sz) => ???
    case SApp(pred, args, tag) => CSApp(pred, args.map(arg => runExpr(arg)), tag)
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
