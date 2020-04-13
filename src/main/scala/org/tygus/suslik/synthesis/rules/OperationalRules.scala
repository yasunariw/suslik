package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.LanguageUtils
import org.tygus.suslik.LanguageUtils.generateFreshVar
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements.Load
import org.tygus.suslik.language.{Statements, _}
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis._
import sun.reflect.generics.reflectiveObjects.NotImplementedException

/**
  * Operational rules emit statement that operate of flat parts of the heap.
  * @author Nadia Polikarpova, Ilya Sergey
  */

object OperationalRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-operational"

  import Statements._

  /*
  Write rule: create a new write from where it's possible

  Γ ; {φ ; x.f -> l' * P} ; {ψ ; x.f -> l' * Q} ---> S   GV(l) = GV(l') = Ø
  ------------------------------------------------------------------------- [write]
  Γ ; {φ ; x.f -> l * P} ; {ψ ; x.f -> l' * Q} ---> *x.f := l' ; S

  */
  object WriteRuleOld extends SynthesisRule with FlatPhase {

    override def toString: Ident = "[Op: write-old]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre
      val post = goal.post

      // Heaplets have no ghosts
      def noGhosts: Heaplet => Boolean = {
        case PointsTo(x@(Var(_)), _, e) => !goal.isGhost(x) && e.vars.forall(v => !goal.isGhost(v))
        case _ => false
      }

      // When do two heaplets match
      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && noGhosts(hr)

      findMatchingHeaplets(noGhosts, isMatch, goal.pre.sigma, goal.post.sigma) match {
        case None => Nil
        case Some((hl@(PointsTo(x@Var(_), offset, e1)), hr@(PointsTo(_, _, e2)))) =>
          if (e1 == e2) {
            return Nil
          } // Do not write if RHSs are the same

          val newPre = Assertion(pre.phi, goal.pre.sigma - hl)
          val newPost = Assertion(post.phi, goal.post.sigma - hr)
          val subGoal = goal.copy(newPre, newPost)
          val stmt = Store(x, offset, e2)
          val kont: StmtProducer = prepend(stmt, toString)

          List(Subderivation(List(subGoal), kont, Prepend(stmt)))
        case Some((hl, hr)) =>
          ruleAssert(assertion = false, s"Write rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
          Nil
      }
    }

  }


  /*
  Write rule: create a new write from where it's possible

  Γ ; {φ ; P} ; {ψ ; x.f -> Y * Q} ---> S   GV(l) = Ø  Y is fresh
  ------------------------------------------------------------------------- [write]
  Γ ; {φ ; P} ; {ψ ; x.f -> l * Q} ---> S; *x.f := l

  */
  object WriteRule extends SynthesisRule with FlatPhase with InvertibleRule {

    override def toString: Ident = "[Op: write]"

    def apply(goal: Goal): Seq[Subderivation] = {

      val pre = goal.pre
      val post = goal.post

      // Heaplets have no ghosts
      def noGhosts: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, e) => !goal.isGhost(x) && e.vars.forall(v => !goal.isGhost(v))
        case _ => false
      }

      findHeaplet(noGhosts, post.sigma) match {
        case None => Nil
        case Some(h@PointsTo(x@Var(_), offset, l)) =>

          // Same heaplet in pre: no point in writing
          if (pre.sigma.chunks.contains(h)) return Nil

          val y = generateFreshVar(goal)

          val newPost = Assertion(post.phi, (post.sigma - h) ** PointsTo(x, offset, y))
          val subGoal = goal.copy(post = newPost)
          val kont: StmtProducer = append(Store(x, offset, l), toString)
          List(Subderivation(List(subGoal), kont, Append(Store(x, offset, l))))
        case Some(h) =>
          ruleAssert(false, s"Write rule matched unexpected heaplet ${h.pp}")
          Nil
      }
    }
  }
  /*
  Read rule: create a fresh typed read

        y is fresh   Γ,y ; [y/A]{φ ; x -> A * P} ; [y/A]{ψ ; Q} ---> S
      ---------------------------------------------------------------- [read]
             Γ ; {φ ; x.f -> A * P} ; {ψ ; Q} ---> let y := *x.f ; S
  */
  object ReadRule extends SynthesisRule with AnyPhase with InvertibleRule {

    override def toString: Ident = "[Op: read]"

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre
      val post = goal.post
      val gamma = goal.gamma

      def alreadyLoaded(a:Var): Boolean = {
        goal.programVars.exists(b => SMTSolving.valid(goal.pre.phi ==> (a |=| b)))
      }

      def isGhostPoints: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, a@Var(_)) =>
           !goal.isGhost(x) && goal.isGhost(a) && ! alreadyLoaded(a)
        case _ => false
      }

      findHeaplet(isGhostPoints, goal.pre.sigma) match {
        case None => Nil
        case Some(PointsTo(x@Var(_), offset, a@Var(_))) =>
          val y = generateFreshVar(goal, a.name)
          val tpy = goal.getType(a)

          val subGoal = goal.copy(pre.subst(a, y), post = post.subst(a, y)).addProgramVar(y,tpy)
          val stmt = Load(y, tpy, x, offset)
          val kont: StmtProducer = prepend(stmt, toString)
          List(Subderivation(List(subGoal), kont, Prepend(stmt)))
        case Some(h) =>
          ruleAssert(false, s"Read rule matched unexpected heaplet ${h.pp}")
          Nil
      }
    }
  }

  /*
  Alloc rule: allocate memory for an existential block

           X ∈ GV(post) / GV (pre)        y, Ai fresh
         Γ ; {φ ; y -> (A0 .. An) * P} ; {ψ ; [y/X]Q} ---> S
     -------------------------------------------------------------- [alloc]
     Γ ; {φ ; P} ; {ψ ; block(X, n) * Q} ---> let y = malloc(n); S
  */
  object AllocRule extends SynthesisRule with FlatPhase {
    val MallocInitVal = 666

    override def toString: Ident = "[Op: alloc]"

    def findTargetHeaplets(goal: Goal): Option[(Block, Seq[Heaplet])] = {
      def isExistBlock: Heaplet => Boolean = {
        case Block(x@Var(_), _) => goal.isExistential(x)
        case _ => false
      }

      findBlockAndChunks(isExistBlock, _ => true, goal.post.sigma)
    }

    def apply(goal: Goal): Seq[Subderivation] = {

      val pre = goal.pre
      val post = goal.post
      val gamma = goal.gamma
      val deriv = goal.deriv

      findTargetHeaplets(goal) match {
        case None => Nil
        case Some((h@Block(x@Var(_), sz), pts)) =>
          val y = generateFreshVar(goal, x.name)
          val tpy = LocType

          val freshChunks = for {
            off <- 0 until sz
            z = generateFreshVar(goal, s"$$tmp_$off") // without s"$$tmp_$off" all names will be same
          } // yield PointsTo(y, off, z)
            yield PointsTo(y, off, IntConst(MallocInitVal))
          val freshBlock = Block(x, sz).subst(x, y)
          val newPre = Assertion(pre.phi, SFormula(pre.sigma.chunks ++ freshChunks ++ List(freshBlock)))

          val postFootprint = pts.map(p => deriv.postIndex.lastIndexOf(p)).toSet + deriv.postIndex.lastIndexOf(h)
          val ruleApp = saveApplication((Set.empty, postFootprint), deriv)

          val subGoal = goal.copy(newPre, post.subst(x, y), newRuleApp = Some(ruleApp)).addProgramVar(y, tpy)
          val stmt = Malloc(y, tpy, sz)
          val kont: StmtProducer = prepend(stmt, toString)
          List(Subderivation(List(subGoal), kont, Prepend(stmt)))
        case _ => Nil
      }
    }

  }

  /*
  Free rule: free a non-ghost block from the pre-state

                     Γ ; {φ ; P} ; {ψ ; Q} ---> S     GV(li) = Ø
   ------------------------------------------------------------------------ [free]
   Γ ; {φ ; block(x, n) * x -> (l1 .. ln) * P} ; { ψ ; Q } ---> free(x); S
*/
  object FreeRule extends SynthesisRule with FlatPhase {

    override def toString: Ident = "[Op: free]"

    def findTargetHeaplets(goal: Goal): Option[(Block, Seq[Heaplet])] = {
      // Heaplets have no ghosts
      def noGhosts(h: Heaplet): Boolean = h.vars.forall(v => goal.isProgramVar(v))
      def noGhostsAndIsBlock(h: Heaplet): Boolean = h match {
        case b:Block => noGhosts(b)
        case _ => false
      }

      findBlockAndChunks(noGhosts, noGhosts, goal.pre.sigma) // todo: when memoization is off, this line makes synthesis 2x faster, but seems wrong. See comment in `findBlockAndChunks`
//      findBlockAndChunks(noGhostsAndIsBlock, noGhosts, goal.pre.sigma)
    }

    def apply(goal: Goal): Seq[Subderivation] = {
      val pre = goal.pre
      val deriv = goal.deriv

      findTargetHeaplets(goal) match {
        case None => Nil
        case Some((h@Block(x@Var(_), sz), pts)) =>
          val newPre = Assertion(pre.phi, pre.sigma - h - pts)

          // Collecting the footprint
          val preFootprint = pts.map(p => deriv.preIndex.lastIndexOf(p)).toSet + deriv.preIndex.lastIndexOf(h)
          val ruleApp = saveApplication((preFootprint, Set.empty), deriv)

          val subGoal = goal.copy(newPre, newRuleApp = Some(ruleApp))
          val kont: StmtProducer = prepend(Free(x), toString)

          List(Subderivation(List(subGoal), kont, PrependFree(Free(x), sz)))
        case Some(_) => Nil
      }
    }

  }

}