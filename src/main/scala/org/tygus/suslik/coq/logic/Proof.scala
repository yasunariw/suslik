package org.tygus.suslik.coq.logic

import org.tygus.suslik.coq.language.Expressions._
import org.tygus.suslik.coq.language.{CAssertion, CoqType, PrettyPrinting}
import org.tygus.suslik.util.StringUtil.mkSpaces

case class CGoal(pre: CAssertion,
                 post: CAssertion,
                 gamma: Map[CVar, CoqType],
                 programVars: Seq[CVar],
                 universalGhosts: Seq[CVar],
                 fname: String) {


}

case class CEnvironment(goal: CGoal, vars: Map[String, CExpr], inductive: Boolean)

case class CProofStep(app: CRuleApp, env: CEnvironment, next: Seq[CProofStep]) extends PrettyPrinting {
  override def pp: String = {
    val builder = new StringBuilder()
    val before = app.before(env)
    val op = app.op(env)
    val after = app.after(env)
    if (before.isDefined) {
      builder.append(before.get)
      builder.append("\n")
    }
    if (op.isDefined) {
      builder.append(op.get)
      builder.append("\n")
    }
    if (after.isDefined) {
      builder.append(after.get)
      builder.append("\n")
    }
    builder.toString()
  }
}

case class CProof(root: CProofStep) extends PrettyPrinting {
  override def pp: String = {
    val builder = new StringBuilder()
    def build(step: CProofStep, offset: Int = 0): Unit = {
      builder.append(mkSpaces(offset))
      builder.append(step.pp)
      if (step.next.length == 1) {
        build(step.next.head, offset)
      } else {
        step.next.foreach(n => build(n, offset + 2))
      }
    }
    builder.append("Next Obligation.\n")
    build(root)
    builder.append("Qed.\n")
    builder.toString()
  }
}
