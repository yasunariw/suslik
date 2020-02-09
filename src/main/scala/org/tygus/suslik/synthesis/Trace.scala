package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements.Statement
import org.tygus.suslik.logic.Specifications.Goal

class Trace {
  var root: Option[GoalTrace] = None

  def init(goal: Goal) : Unit = {
    this.root = Some(GoalTrace(goal))
  }

  def pp: String = {
    def mkSpaces(indent: Integer) : String = " " * indent * 2
    def traverse(n: TraceNode, indent: Integer = 0) : String = n match {
      case g: GoalTrace =>
        if (g.ruleApps.isEmpty) s"${mkSpaces(indent)}| Goal ${g.goal.pre.pp} ${g.goal.post.pp} [FAILED]"
        else s"${mkSpaces(indent)}| Goal ${g.goal.pre.pp} ${g.goal.post.pp}\n" +
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
        newG.ruleApps = g.ruleApps.find(!_.isFail).map(traverse).toList.asInstanceOf[List[RuleAppTrace]]
        newG
      case d: SubderivationTrace =>
        val newD = d.copy()
        newD.subgoals = d.subgoals.map(traverse).asInstanceOf[List[GoalTrace]]
        newD
      case r: RuleAppTrace =>
        val newR = r.copy()
        newR.alts = r.alts.map(traverse).asInstanceOf[List[SubderivationTrace]]
        newR
    }
    val newTrace = new Trace
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