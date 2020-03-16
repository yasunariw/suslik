package org.tygus.suslik.coq.logic

import org.tygus.suslik.coq.language.Expressions.{CPointsTo, CVar}
import org.tygus.suslik.coq.language.{CAssertion, PrettyPrinting}

sealed abstract class CProofStep extends PrettyPrinting {
  def before: String = ""
  def op: String = ""
  def after: String = ""
  override def pp: String = List(before, op, after).filterNot(_.isEmpty).mkString("\n")
}

case class CGhostElim(formals: List[CVar], ghosts: List[CVar], asn: CAssertion) extends CProofStep {
  override def before: String = "ssl_ghostelim_pre."
  override def op: String = {
    if (ghosts.isEmpty) return ""
    val builder = new StringBuilder()
    builder.append("move=>")

    formals match {
      case Nil => builder.append(nestedDestruct(ghosts))
      case _ => builder.append(s"[${nestedDestruct(formals)} ${nestedDestruct(ghosts)}]")
    }
    builder.append("//=.")
    builder.toString()
  }
  override def after: String = {
    val ptss = asn.sigma.ptss
    val apps = asn.sigma.apps

    val hFromPre = if (apps.nonEmpty) {
      val hApps = nestedDestruct(apps.map(app => CVar(s"H${app.pred}")))
      if (ptss.nonEmpty) {
        s"[-> $hApps]"
      } else {
        hApps
      }
    } else if (ptss.nonEmpty) {
      "->"
    }
    val builder = new StringBuilder()
    builder.append("move=>")
    builder.append(hFromPre)
    builder.append(" HValid.")
    builder.toString()
  }

  private def nestedDestruct(items: Seq[CVar]): String = items match {
    case v1 :: Nil =>
      v1.pp
    case v1 :: v2 :: vars1 =>
      vars1.foldLeft(s"[${v1.pp} ${v2.pp}]"){ case (acc, v) => s"[$acc $v]" }
  }
}

sealed abstract class CFailRuleApp extends CProofStep
case object CNoop extends CFailRuleApp
case object CPostInconsistent extends CFailRuleApp
case object CPostInvalid extends CFailRuleApp
case object CAbduceBranch extends CFailRuleApp
case object CHeapUnreachable extends CFailRuleApp

sealed abstract class CLogicalRuleApp extends CProofStep
case object CEmp extends CLogicalRuleApp {
  override def op: String = "ssl_emp."
}
case object CInconsistency extends CLogicalRuleApp
case object CFrame extends CLogicalRuleApp
case object CNilNotLval extends CLogicalRuleApp
case object CStarPartial extends CLogicalRuleApp
case object CSubstLeft extends CLogicalRuleApp
case object CSubstLeftVar extends CLogicalRuleApp

sealed abstract class COperationalRuleApp extends CProofStep
case class CWriteOld(heaplet: CPointsTo) extends COperationalRuleApp {
  override def op: String = "ssl_write."
  override def after: String = s"ssl_write_post ${heaplet.locPP}."
}
case object CWrite extends COperationalRuleApp
case object CRead extends COperationalRuleApp {
  override def op: String = "ssl_read."
}
case object CAlloc extends COperationalRuleApp
case object CFreeStep extends COperationalRuleApp {
  override def op: String = "ssl_dealloc."
}
