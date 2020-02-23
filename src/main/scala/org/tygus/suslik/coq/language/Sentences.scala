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
    val preEx = pre.vars.filterNot(programVars.contains)
    val postEx = post.vars.filterNot(programVars.contains)
    (""
      + s"Definition ${name}_type ${params.map{ case (t, v) => s"(${v.pp} : ${t.pp})" }.mkString(" ")} :=\n"
      + (if (pureParams.isEmpty) "" else s"  {${pureParams.map{ case (t, v) => s"(${v.pp} : ${t.pp})" }.mkString(" ")}},\n")
      + s"    STsep (\n"
      + s"      fun h => ${if (preEx.isEmpty) pre.pp else CExists(preEx, pre).pp},\n"
      + s"      [vfun (_: ${rType.pp}) h => ${if (postEx.isEmpty) post.pp else CExists(postEx, post).pp}])."
      )
  }

  def vars: Seq[CVar] = programVars ++ pre.vars ++ post.vars

  def programVars: Seq[CVar] = params.map(_._2) ++ pureParams.map(_._2)
}