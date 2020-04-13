package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements.Statement
import org.tygus.suslik.logic.FunSpec
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.rules.UnfoldingRules.InductionRule

object Trace {
  def apply(spec: FunSpec, goal: Goal): Trace = {
    val trace = new Trace(spec)
    trace.root = Some(GoalTrace(goal))
    trace
  }
}

class Trace(val spec: FunSpec) {
  var root: Option[GoalTrace] = None

  def inductive: Boolean = this.root.exists(goal =>
    goal.ruleApps.head.rule match {
      case InductionRule => true
      case _ => false
    })

  def pp: String = {
    def mkSpaces(indent: Integer) : String = " " * indent * 2
    def traverse(n: TraceNode, indent: Integer = 0) : String = n match {
      case g: GoalTrace =>
        val stmt = if (g.stmt.isDefined) g.stmt.get.pp.replaceAll("\\n[ ]*", " ") else "??"
        val goal = s"${g.goal.pre.pp} [[$stmt]] ${g.goal.post.pp}"
        if (g.ruleApps.isEmpty) s"${mkSpaces(indent)}| Goal $goal [FAILED]"
        else s"${mkSpaces(indent)}| Goal $goal\n" +
          g.ruleApps.map(ra => traverse(ra, indent + 1)).mkString(",\n")
      case sd: SubderivationTrace =>
        if (sd.subgoals.isEmpty) s"${mkSpaces(indent)}| No subgoals left [DONE]"
        else s"${mkSpaces(indent)}| Subgoals\n" +
          sd.subgoals.map(sg => traverse(sg, indent + 1)).mkString(",\n")
      case ra: RuleAppTrace =>
        if (ra.alts.isEmpty) s"${mkSpaces(indent)}| RuleApp ${ra.rule.toString} [FAILED]"
        else s"${mkSpaces(indent)}| RuleApp ${ra.rule.toString}\n" +
          ra.alts.map(alt => traverse(alt, indent + 1)).mkString(",\n")
    }
    root match {
      case Some(node) => traverse(node)
      case None => "Uninitialized"
    }
  }

  def pruneInvalidRuleApps: Trace = {
    def traverse(n: TraceNode) : TraceNode = n match {
      case g: GoalTrace =>
        val newG = g.copy()
        newG.stmt = g.stmt
        newG.ruleApps = g.ruleApps.find(!_.isFail).map(traverse).toList.asInstanceOf[List[RuleAppTrace]]
        newG
      case d: SubderivationTrace =>
        val newD = d.copy()
        newD.stmt = d.stmt
        newD.subgoals = d.subgoals.map(traverse).asInstanceOf[List[GoalTrace]]
        newD
      case r: RuleAppTrace =>
        val newR = r.copy()
        newR.alts = r.alts.map(traverse).asInstanceOf[List[SubderivationTrace]]
        newR
    }
    val newTrace = new Trace(spec)
    newTrace.root = root.map(r => traverse(r).asInstanceOf[GoalTrace])
    newTrace
  }
}

sealed abstract class TraceNode

case class GoalTrace(goal: Goal) extends TraceNode {
  var ruleApps: List[RuleAppTrace] = List.empty
  var stmt: Option[Statement] = None
}

case class SubderivationTrace(alt: Subderivation) extends TraceNode {
  var subgoals: List[GoalTrace] = List.empty
  var stmt: Option[Statement] = None
}

case class RuleAppTrace(rule: SynthesisRule) extends TraceNode {
  var alts: List[SubderivationTrace] = List.empty
  var isFail: Boolean = false
}