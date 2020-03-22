package org.tygus.suslik.synthesis

import org.tygus.suslik.Memoization
import org.tygus.suslik.coq.translation.Translator
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.util.{SynLogging, SynStats}

import scala.Console._
import scala.collection.mutable.ListBuffer

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait Synthesis extends SepLogicUtils {

  val log: SynLogging

  import log._

  def synAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SynthesisException(msg)

  def allRules(goal: Goal): List[SynthesisRule]

  def nextRules(goal: Goal, depth: Int): List[SynthesisRule]

  val memo = new Memoization

  def synthesizeProc(spec: FunSpec, env: Environment, sketch: Statement): Option[(Procedure, SynStats)] = {
    implicit val config: SynConfig = env.config
    // Cleanup the memo table
    memo.cleanup()
    val FunSpec(name, tp, formals, pre, post, var_decl) = spec
    val goal = makeNewGoal(pre, post, formals, name, env, sketch, var_decl)
    printLog(List(("Initial specification:", Console.BLACK), (s"${goal.pp}\n", Console.BLUE)))(i = 0, config)
    val stats = new SynStats()
    SMTSolving.init()
    val trace = Trace(spec, goal)
    try {
      synthesize(goal, config.startingDepth, trace.root.get)(stats = stats, rules = nextRules(goal, config.startingDepth)) match {
        case Some(body) =>
          trace.root.get.stmt = Some(body)

          val prunedTrace = trace.pruneInvalidRuleApps
          testPrintln(Translator.runFunSpecFromTrace(prunedTrace).pp)
          val proc = Procedure(name, tp, formals, body)
          testPrintln(prunedTrace.pp)
          testPrintln(Translator.runProcedure(proc, prunedTrace).ppp)
          testPrintln(Translator.runProofFromTrace(prunedTrace, env.predicates).pp)
          Some((proc, stats))
        case None =>
          printlnErr(s"Deductive synthesis failed for the goal\n ${goal.pp},\n depth = ${config.startingDepth}.")
          None
      }
    } catch {
      case SynTimeOutException(msg) =>
        printlnErr(msg)
        None
    }

  }

  private def synthesize(goal: Goal, depth: Int, trace: GoalTrace) // todo: add goal normalization
                        (stats: SynStats,
                         rules: List[SynthesisRule])
                        (implicit ind: Int = 0): Option[Statement] = {
    lazy val res: Option[Statement] = synthesizeInner(goal, depth, trace)(stats, rules)(ind)
    memo.runWithMemo(goal, stats, rules, res)
  }

  private def synthesizeInner(goal: Goal, depth: Int, trace: GoalTrace)
                             (stats: SynStats,
                              rules: List[SynthesisRule])
                             (implicit ind: Int = 0): Option[Statement] = {
    implicit val config: SynConfig = goal.env.config

    if (config.printEnv) {
      printLog(List((s"${goal.env.pp}", Console.MAGENTA)))
    }
    printLog(List((s"${goal.pp}", Console.BLUE)))

    val currentTime = System.currentTimeMillis()
    if (currentTime - goal.env.startTime > config.timeOut) {
      throw SynTimeOutException(s"\n\nThe derivation took too long: more than ${config.timeOut.toDouble / 1000} seconds.\n")
    }

    if (depth < 0) {
      printLog(List(("Reached maximum depth.", RED)))
      return None
    }

    def tryRules(rules: List[SynthesisRule], trace: GoalTrace,
                 appTraceKont: List[RuleAppTrace] => List[RuleAppTrace]): Option[Statement] = rules match {
      case Nil =>
        trace.ruleApps = appTraceKont(Nil)
        None
      case r :: rs =>
        // Try alternative sub-derivations after applying `r`
        @scala.annotation.tailrec
        def tryAlternatives(alts: Seq[Subderivation], altIndex: Int, ruleAppTrace: RuleAppTrace, altTraceKont: List[SubderivationTrace] => List[SubderivationTrace]): Option[Statement] = alts match {
          case Seq(a, as@_*) =>
            if (altIndex > 0) printLog(List((s"${r.toString} Trying alternative sub-derivation ${altIndex + 1}:", MAGENTA)))
            val altTrace = SubderivationTrace(a)
            solveSubgoals(a, altTrace) match {
              case Some(Magic) =>
                stats.bumpUpBacktracing()
                tryAlternatives(as, altIndex + 1, ruleAppTrace, altTrace :: altTraceKont(_)) // This alternative is inconsistent: try other alternatives
              case Some(res) =>
                stats.bumpUpLastingSuccess()
                altTrace.stmt = Some(res)
                ruleAppTrace.alts = altTraceKont(altTrace :: Nil)
                Some(res) // This alternative succeeded
              case None =>
                stats.bumpUpBacktracing()
                tryAlternatives(as, altIndex + 1, ruleAppTrace, altTrace :: altTraceKont(_)) // This alternative failed: try other alternatives
            }
          case Seq() =>
            // All alternatives have failed
            ruleAppTrace.isFail = true
            ruleAppTrace.alts = altTraceKont(Nil)
            if (config.invert && r.isInstanceOf[InvertibleRule]) {
              // Do not backtrack application of this rule: the rule is invertible and cannot be the reason for failure
              printLog(List((s"${r.toString} All sub-derivations failed: invertible rule, do not backtrack.", MAGENTA)))
              None
            } else {
              // Backtrack application of this rule
              stats.bumpUpBacktracing()
              printLog(List((s"${r.toString} All sub-derivations failed: backtrack.", MAGENTA)))
              tryRules(rs, trace, ruleAppTrace :: appTraceKont(_))
            }
        }

        // Solve all sub-goals in a sub-derivation
        def solveSubgoals(s: Subderivation, trace: SubderivationTrace): Option[Statement] = {

          // Optimization: if one of the subgoals failed, to not try the rest!
          // <ugly-imperative-code>
          val results = new ListBuffer[Statement]
          val subgoalTraces = new ListBuffer[GoalTrace]
          import util.control.Breaks._
          breakable {
            for {subgoal <- s.subgoals} {
              val goalTrace = GoalTrace(subgoal)
              synthesize(subgoal, depth - 1, goalTrace)(stats, nextRules(subgoal, depth - 1))(ind + 1) match {
                case Some(s) =>
                  goalTrace.stmt = Some(s)
                  results.append(s)
                  subgoalTraces.append(goalTrace)
                case _ => break
              }
            }
            trace.subgoals = subgoalTraces.toList
          }
          // </ugly-imperative-code>

          val resultStmts = for (r <- results) yield r
          if (resultStmts.size < s.subgoals.size)
          // One of the sub-goals failed: this sub-derivation fails
            None
          else
            handleGuard(s, resultStmts.toList, trace)
        }

        // If stmts is a single guarded statement:
        // if possible, propagate guard to the result of the current goal,
        // otherwise, try to synthesize the else branch and fail if that fails
        def handleGuard(s: Subderivation, stmts: List[Statement], trace: SubderivationTrace): Option[Statement] =
          stmts match {
            case Guarded(cond, thn) :: Nil =>
              s.comp(stmts) match {
                case g@Guarded(_, _) if depth < config.startingDepth => // Can propagate to upper-level goal
                  Some(g)
                case _ => // Cannot propagate: try to synthesize else branch
                  val goal = s.subgoals.head
                  val newPre = goal.pre.copy(phi = goal.pre.phi && cond.not)
                  // Set starting depth to current depth: new subgoal will start at its own starting depth
                  // to disallow producing guarded statements
                  val newConfig = goal.env.config.copy(startingDepth = depth)
                  val newG = goal.copy(newPre, env = goal.env.copy(config = newConfig))
                  val newGTrace = GoalTrace(newG)
                  synthesize(newG, depth, newGTrace)(stats, nextRules(newG, depth - 1))(ind) match {
                    case Some(els) =>
                      newGTrace.stmt = Some(els)
                      Some(s.comp(List(If(cond, thn, els)))) // successfully synthesized else
                    case _ => None // failed to synthesize else
                  }
              }
            case _ => Some(s.comp(stmts))
          }

        // Invoke the rule
        val ruleAppTrace = RuleAppTrace(r)
        val allSubderivations = r(goal)
        val goalStr = s"$r: "

        // Filter out subderivations that violate rule ordering
        def goalInOrder(g: Goal): Boolean = {
          g.deriv.outOfOrder(allRules(goal)) match {
            case None => true
            case Some(app) =>
              //              printLog(List((g.deriv.preIndex.map(_.pp).mkString(", "), BLACK)), isFail = true)
              //              printLog(List((g.deriv.postIndex.map(_.pp).mkString(", "), BLACK)), isFail = true)
              printLog(List((s"$goalStr${RED}Alternative ${g.deriv.applications.head.pp} commutes with earlier ${app.pp}", BLACK)))
              false
          }
        }

        val subderivations = if (config.commute)
          allSubderivations.filter(sub => sub.subgoals.forall(goalInOrder))
        else
          allSubderivations

        if (subderivations.isEmpty) {
          // Rule not applicable: try the rest
          printLog(List((s"$goalStr${RED}FAIL", BLACK)), isFail = true)
          ruleAppTrace.isFail = true
          tryRules(rs, trace, ruleAppTrace :: appTraceKont(_))
        } else {
          // Rule applicable: try all possible sub-derivations
          val subSizes = subderivations.map(s => s"${s.subgoals.size} sub-goal(s)").mkString(", ")
          val succ = s"SUCCESS at depth $ind, ${subderivations.size} alternative(s) [$subSizes]"
          printLog(List((s"$goalStr$GREEN$succ", BLACK)))
          stats.bumpUpSuccessfulRuleApp()
          if (subderivations.size > 1) {
            printLog(List((s"Trying alternative sub-derivation 1:", CYAN)))
          }
          trace.ruleApps = appTraceKont(ruleAppTrace :: Nil)
          tryAlternatives(subderivations, 0, ruleAppTrace, identity)
        }
    }

    tryRules(rules, trace, identity)
  }

  private def getIndent(implicit i: Int): String = if (i <= 0) "" else "|  " * i

  private def printLog(sc: List[(String, String)], isFail: Boolean = false)
                      (implicit i: Int, config: SynConfig): Unit = {
    if (config.printDerivations) {
      if (!isFail || config.printFailed) {
        for ((s, c) <- sc if s.trim.length > 0) {
          print(s"$BLACK$getIndent")
          println(s"$c${s.replaceAll("\n", s"\n$BLACK$getIndent$c")}")
        }
      }
      print(s"$BLACK")
    }
  }

}