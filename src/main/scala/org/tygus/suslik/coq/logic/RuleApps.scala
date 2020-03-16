package org.tygus.suslik.coq.logic

import org.tygus.suslik.coq.language.Expressions._

sealed abstract class CRuleApp {
  def before(env: CEnvironment): Option[String] = None
  def op(env: CEnvironment): Option[String] = None
  def after(env: CEnvironment): Option[String] = None
}


case object CGhostElim extends CRuleApp {
  override def before(env: CEnvironment): Option[String] = Some("ssl_ghostelim_pre.")
  override def op(env: CEnvironment): Option[String] = {
    val goal = env.goal
    val ghosts = goal.universalGhosts
    val formals = if (env.inductive) goal.programVars else Seq.empty
    if (ghosts.isEmpty) return None
    val builder = new StringBuilder()
    builder.append("move=>")
    formals match {
      case Nil => builder.append(nestedDestruct(ghosts))
      case _ => builder.append(s"[${nestedDestruct(formals)} ${nestedDestruct(ghosts)}]")
    }
    builder.append("//=.")
    Some(builder.toString())
  }
  override def after(env: CEnvironment): Option[String] = {
    val pre = env.goal.pre
    val ptss = pre.sigma.ptss
    val apps = pre.sigma.apps

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
    Some(builder.toString())
  }

  private def nestedDestruct(items: Seq[CVar]): Option[String] = {
    if (items.length == 1) {
      Some(items.head.pp)
    } else items match {
      case v1 +: v2 +: items1 =>
        Some(items1.foldLeft(s"[${v1.pp} ${v2.pp}]"){ case (acc, v) => s"[$acc $v]" })
    }
  }
}

sealed abstract class CFailRuleApp extends CRuleApp
case object CNoop extends CFailRuleApp
case object CPostInconsistent extends CFailRuleApp
case object CPostInvalid extends CFailRuleApp
case object CAbduceBranch extends CFailRuleApp
case object CHeapUnreachable extends CFailRuleApp

sealed abstract class CLogicalRuleApp extends CRuleApp
case object CEmp extends CLogicalRuleApp {
  override def op(env: CEnvironment): Option[String] = Some("ssl_emp.")
}
case object CInconsistency extends CLogicalRuleApp
case object CFrame extends CLogicalRuleApp
case object CNilNotLval extends CLogicalRuleApp
case object CStarPartial extends CLogicalRuleApp
case object CSubstLeft extends CLogicalRuleApp
case object CSubstLeftVar extends CLogicalRuleApp

sealed abstract class COperationalRuleApp extends CRuleApp
case class CWriteOld(to: CVar) extends COperationalRuleApp {
  override def op(env: CEnvironment): Option[String] = Some("ssl_write.")
  override def after(env: CEnvironment): Option[String] = Some(s"ssl_write_post ${to.pp}.")
}
case object CWrite extends COperationalRuleApp
case object CRead extends COperationalRuleApp {
  override def op(env: CEnvironment): Option[String] = Some("ssl_read.")
}
case object CAlloc extends COperationalRuleApp
case object CFreeStep extends COperationalRuleApp {
  override def op(env: CEnvironment): Option[String] = Some("ssl_dealloc.")
}
