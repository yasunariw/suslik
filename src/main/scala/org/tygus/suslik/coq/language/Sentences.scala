package org.tygus.suslik.coq.language

import org.tygus.suslik.coq.language.Expressions._

case class CInductiveClause(name: String, selector: CExpr, asn: CExpr) extends PrettyPrinting {
  override def pp: String = s"| $name of ${selector.pp} of ${asn.pp}"

  def refreshExistentials(vars: Set[CVar]): CInductiveClause = asn match {
    case CExists(ex, asn1) =>
      val newEx = asn1.collect(_.isInstanceOf[CVar]) ++ ex.toSet -- vars
      if (newEx.isEmpty) this.copy() else CInductiveClause(name, selector, CExists(newEx.toSeq, asn1))
    case _ =>
      val ex = asn.collect(_.isInstanceOf[CVar]) -- vars
      if (ex.isEmpty) this.copy() else CInductiveClause(name, selector, CExists(ex.toSeq, asn))
  }
}

case class CInductivePredicate(name: String, params: CFormals, clauses: Seq[CInductiveClause]) extends PrettyPrinting {
  override def pp: String =
    s"Inductive $name ${params.map{ case (t, v) => s"(${v.pp} : ${t.pp})" }.mkString(" ")} : Prop :=\n${clauses.map(_.pp).mkString("\n")}."

  def refreshExistentials: CInductivePredicate = {
    CInductivePredicate(name, params, clauses.map(_.refreshExistentials(params.map(_._2).toSet)))
  }
}

case class CFunSpec(name: String, rType: CoqType, params: CFormals, pureParams: CFormals, pre: CExpr, post: CExpr) extends PrettyPrinting {
  override def pp: String = {
    (""
      + s"Definition ${name}_type :=\n"
      + s"  forall ${params.map{ case (t, v) => s"(${v.pp} : ${t.pp})" }.mkString(" ")},\n"
      + s"    ${pureParams.map{ case (t, v) => s"{${v.pp} : ${t.pp}}" }.mkString(" ")},\n"
      + s"    STsep (\n"
      + s"      fun h => ${pre.pp},\n"
      + s"      [vfun (_: ${rType.pp}) h => ${post.pp}])."
      )
  }
}