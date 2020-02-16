package org.tygus.suslik.synthesis

import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language.PrettyPrinting
import org.tygus.suslik.logic._

/**
  * A generic class for a deductive rule to be applied
  *
  * @author Ilya Sergey
  */
abstract class SynthesisRule extends PureLogicUtils {
  // Apply the rule and get all possible sub-derivations
  def apply(goal: Goal): Seq[Subderivation]

  def saveApplication(footprint: (Set[Int], Set[Int]),
                      currentDeriv: Derivation,
                      cost: Int = 0): RuleApplication =
    RuleApplication(this, footprint, (currentDeriv.preIndex.length, currentDeriv.postIndex.length), cost)
}

/**
  * Different kinds of rules
  */

// Invertible rule: does not restrict the set of derivations,
// so no need to backtrack in case of failure
trait InvertibleRule

trait AnyPhase {
}

trait UnfoldingPhase {
  def heapletFilter(h: Heaplet): Boolean = {
    h.isInstanceOf[SApp]
  }
}

trait FlatPhase {
  def heapletFilter(h: Heaplet): Boolean = {
    true
  }
}

/**
  * A result of a rule application:
  * consists of sub-goals (rule premises) and
  * a statement producer that assembles the sub-goal results
  */
case class Subderivation(subgoals: Seq[Goal], kont: StmtProducer, comp: StmtComputation)
    extends PrettyPrinting with PureLogicUtils {

  override def pp: String =
    s"${subgoals.size} subgoal(s):\n${subgoals.map { g => s"${g.env.pp}${g.pp}" }.mkString("\n")}"
}




