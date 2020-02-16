package org.tygus.suslik.coq.language

object Expressions {

  sealed abstract class CExpr extends ProgramPrettyPrinting {
    def collect[R <: CExpr](p: CExpr => Boolean): Set[R] = {

      def collector(acc: Set[R])(exp: CExpr): Set[R] = exp match {
        case v@CVar(_) if p(v) => acc + v.asInstanceOf[R]
        case c@CNatConst(_) if p(c) => acc + c.asInstanceOf[R]
        case c@CBoolConst(_) if p(c) => acc + c.asInstanceOf[R]
        case b@CBinaryExpr(_, l, r) =>
          val acc1 = if (p(b)) acc + b.asInstanceOf[R] else acc
          val acc2 = collector(acc1)(l)
          collector(acc2)(r)
        case u@CUnaryExpr(_, arg) =>
          val acc1 = if (p(u)) acc + u.asInstanceOf[R] else acc
          collector(acc1)(arg)
        case s@CSetLiteral(elems) =>
          val acc1 = if (p(s)) acc + s.asInstanceOf[R] else acc
          elems.foldLeft(acc1)((a,e) => collector(a)(e))
        case i@CIfThenElse(cond, l, r) =>
          val acc1 = if (p(i)) acc + i.asInstanceOf[R] else acc
          val acc2 = collector(acc1)(cond)
          val acc3 = collector(acc2)(l)
          collector(acc3)(r)
        case a@CSApp(_, args, _) =>
          val acc1 = if (p(a)) acc + a.asInstanceOf[R] else acc
          args.foldLeft(acc1)((acc, arg) => collector(acc)(arg))
        case _ => acc
      }

      collector(Set.empty)(this)
    }

    def simplify: CExpr = this match {
      case CBinaryExpr(op, left, right) =>
        if (op == COpAnd) {
          if (left == CBoolConst(true)) return right.simplify
          else if (right == CBoolConst(true)) return left.simplify
        }
        CBinaryExpr(op, left.simplify, right.simplify)
      case CUnaryExpr(op, arg) =>
        CUnaryExpr(op, arg.simplify)
      case CSetLiteral(elems) =>
        CSetLiteral(elems.map(e => e.simplify))
      case CIfThenElse(cond, left, right) =>
        CIfThenElse(cond.simplify, left.simplify, right.simplify)
      case CSApp(pred, args, tag) =>
        CSApp(pred, args.map(_.simplify), tag)
      case other => other
    }

    def vars: Seq[CVar] = collect(_.isInstanceOf[CVar]).toSeq
  }

  case class CVar(name: String) extends CExpr {
    override def pp: String = name
  }

  case class CBoolConst(value: Boolean) extends CExpr {
    override def pp: String = value.toString
  }

  case class CNatConst(value: Int) extends CExpr {
    override def pp: String = value.toString
  }

  case class CSetLiteral(elems: List[CExpr]) extends CExpr {
    override def pp: String = if (elems.isEmpty) "nil" else s"[:: ${elems.map(_.pp).mkString("; ")}]"
    override def ppp: String = if (elems.isEmpty) "nil" else s"[:: ${elems.map(_.ppp).mkString("; ")}]"
  }

  case class CIfThenElse(cond: CExpr, left: CExpr, right: CExpr) extends CExpr {
    override def pp: String = s"if ${cond.pp} then ${left.pp} else ${right.pp}"
    override def ppp: String = s"if ${cond.ppp} then ${left.ppp} else ${right.ppp}"
  }

  case class CBinaryExpr(op: CBinOp, left: CExpr, right: CExpr) extends CExpr {
    override def pp: String = s"${left.pp} ${op.pp} ${right.pp}"
    override def ppp: String = s"${left.ppp} ${op.ppp} ${right.ppp}"
  }

  case class CUnaryExpr(op: CUnOp, e: CExpr) extends CExpr {
    override def pp: String = s"${op.pp} ${e.pp}"
    override def ppp: String = s"${op.ppp} ${e.ppp}"
  }

  case class COverloadedBinaryExpr(op: COverloadedBinOp, left: CExpr, right: CExpr) extends CExpr {
    override def pp: String = s"${left.pp} ${op.pp} ${right.pp}"
    override def ppp: String = s"${left.ppp} ${op.ppp} ${right.ppp}"
  }

  case class CPointsTo(loc: CExpr, offset: Int = 0, value: CExpr) extends CExpr {
    override def pp: String = s"${if (offset == 0) loc.pp else s"${loc.pp} .+ $offset"} :-> ${value.pp}"
    override def ppp: String = s"${if (offset == 0) loc.ppp else s"${loc.ppp} .+ $offset"} :-> ${value.ppp}"
  }

  case object CEmpty extends CExpr {
    override def pp: String = "empty"
  }

  case class CSApp(pred: String, var args: Seq[CExpr], tag: Option[Int] = Some(0)) extends CExpr {
    override def pp: String = s"$pred ${args.map(arg => arg.pp).mkString(" ")}"
    override def ppp: String = s"$pred ${args.map(arg => arg.ppp).mkString(" ")}"
  }

  case class CExists(override val vars: Seq[CVar], e: CExpr) extends CExpr {
    override def pp: String = s"exists ${vars.map(v => v.pp).mkString(" ")}, ${e.pp}"
    override def ppp: String = s"exists ${vars.map(v => v.ppp).mkString(" ")}, ${e.ppp}"
  }

  case class CForAll(override val vars: Seq[CVar], e: CExpr) extends CExpr {
    override def pp: String = s"forall ${vars.map(v => v.pp).mkString(" ")}, ${e.pp}"
    override def ppp: String = s"forall ${vars.map(v => v.ppp).mkString(" ")}, ${e.ppp}"
  }

  sealed abstract class CUnOp extends ProgramPrettyPrinting

  object COpNot extends CUnOp {
    override def pp: String = "not"
  }

  object COpUnaryMinus extends CUnOp

  sealed abstract class COverloadedBinOp extends ProgramPrettyPrinting

  sealed abstract class CBinOp extends COverloadedBinOp

  object COpOverloadedEq extends COverloadedBinOp {
    override def pp: String = "="
  }

  object COpNotEqual extends COverloadedBinOp {
    override def pp: String = "!="
  }

  object COpGt extends COverloadedBinOp {
    override def pp: String = ">"
  }

  object COpGeq extends COverloadedBinOp {
    override def pp: String = ">="
  }

  object COpOverloadedPlus extends COverloadedBinOp {
    override def pp: String = "+"
  }

  object COpOverloadedMinus extends COverloadedBinOp {
    override def pp: String = "-"
  }

  object COpOverloadedLeq extends COverloadedBinOp {
    override def pp: String = "<="
  }

  object COpOverloadedStar extends COverloadedBinOp {
    override def pp: String = "*"
  }

  object COpImplication extends CBinOp {
    override def pp: String = "->"
  }

  object COpPlus extends CBinOp {
    override def pp: String = "+"
  }

  object COpMinus extends CBinOp {
    override def pp: String = "-"
  }

  object COpMultiply extends CBinOp {
    override def pp: String = "*"
  }

  object COpEq extends CBinOp {
    override def pp: String = "="
    override def ppp: String = "=="
  }

  object COpBoolEq extends CBinOp {
    override def pp: String = "="
  }

  object COpLeq extends CBinOp {
    override def pp: String = "<="
  }

  object COpLt extends CBinOp {
    override def pp: String = "<"
  }

  object COpAnd extends CBinOp {
    override def pp: String = "/\\"
  }

  object COpOr extends CBinOp {
    override def pp: String = "\\/"
  }

  object COpHeapJoin extends CBinOp {
    override def pp: String = "\\+"
  }

  object COpUnion extends CBinOp {
    override def pp: String = "++"
  }

  object COpDiff extends CBinOp {
    override def pp: String = "--"
  }

  object COpIn extends CBinOp

  object COpSetEq extends CBinOp {
    override def pp: String = "="
  }

  object COpSubset extends CBinOp

  object COpIntersect extends CBinOp

}