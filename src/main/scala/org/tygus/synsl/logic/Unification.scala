package org.tygus.synsl.logic

import org.tygus.synsl.language.Expressions.Var

object Unification extends SepLogicUtils with PureLogicUtils {

  /**
    * Generate fresh names for variables in `source` that occur in `target`
    */
  private def refreshSource(target: UnificationGoal, source: UnificationGoal): (UnificationGoal, Map[Var, Var]) = {
    val (freshSourceFormula, freshSubst) = source.formula.refresh(target.formula.vars)
    val freshParams = source.params.map(_.subst(freshSubst)).asInstanceOf[Set[Var]]
    (UnificationGoal(freshSourceFormula, freshParams), freshSubst)
  }

  private def genSubst(to: Var, from: Var, taken: Set[Var]): Option[Map[Var, Var]] = {
    if (to == from) Some(Map.empty)
    else if (!taken.contains(from)) Some(Map(from -> to))
    else None
  }

  private def assertNoOverlap(sbst1: Map[Var, Var], sbst2: Map[Var, Var]) {
    assert(sbst1.keySet.intersect(sbst2.keySet).isEmpty, s"Two substitutions overlap:\n:$sbst1\n$sbst2")
  }

  /**
    * Tries to unify two heaplets h1 and h2, assuming h2 has variables that are either free or in taken.
    * If successful, returns a substitution from h2's fresh variables to h1's variables
    */
  private def tryUnify(h1: Heaplet, h2: Heaplet, taken: Set[Var]): Option[Map[Var, Var]] = {
    assert(h1.vars.forall(taken.contains), s"Not all variables of ${h1.pp} are in $taken")
    (h1, h2) match {
      case (PointsTo(x1@Var(_), o1, v1@Var(_)), PointsTo(x2@Var(_), o2, v2@Var(_))) =>
        if (o1 != o2) None else {
          assert(taken.contains(x1))
          assert(taken.contains(v1))
          for {
            m1 <- genSubst(x1, x2, taken)
            _v2 = v2.subst(m1).asInstanceOf[Var]
            m2 <- genSubst(v1, _v2, taken)
          } yield {
            assertNoOverlap(m1, m2)
            m1 ++ m2
          }
        }
      case (Block(x1@Var(_), s1), Block(x2@Var(_), s2)) =>
        if (s1 != s2) None else {
          assert(taken.contains(x1))
          genSubst(x1, x2, taken)
        }
      case (SApp(p1, es1), SApp(p2, es2))
        // Only unify predicates with variables as arguments
        if es1.forall(_.isInstanceOf[Var]) && es2.forall(_.isInstanceOf[Var]) =>
        if (p1 != p2 || es1.size != es2.size) None else {
          val pairs = es1.zip(es2).asInstanceOf[List[(Var, Var)]]
          // Collect the mapping from the predicate parameters
          pairs.foldLeft(Some(Map.empty): Option[Map[Var, Var]]) {
            case (opt, (x1, x2)) => opt match {
              case None => None
              case Some(acc) => genSubst(x1, x2, taken) match {
                case Some(sbst) =>
                  assertNoOverlap(acc, sbst)
                  Some(acc ++ sbst)
                case None => None
              }
            }
          }
        }
      case _ => None
    }
  }


  /**
    * Check that two lists of heaplets have a chance to be unified
    */
  private def checkShapesMatch(cs1: List[Heaplet], cs2: List[Heaplet]): Boolean = {
    val (ps1, ps2) = (cs1.filter(_.isInstanceOf[PointsTo]), cs2.filter(_.isInstanceOf[PointsTo]))
    val (bs1, bs2) = (cs1.filter(_.isInstanceOf[Block]), cs2.filter(_.isInstanceOf[Block]))
    val (as1, as2) = (cs1.filter(_.isInstanceOf[SApp]), cs2.filter(_.isInstanceOf[SApp]))

    // Check sizes
    if (ps1.size != ps2.size) return false
    if (bs1.size != bs2.size) return false
    if (as1.size != as2.size) return false

    // Check matching blocks
    val checkMatchingBlocks = (bs1: List[Heaplet], bs2: List[Heaplet]) =>
      bs1.forall {
        case Block(_, s1) => bs2.exists { case Block(_, s2) => s1 == s2; case _ => false }
        case _ => false
      }

    if (!checkMatchingBlocks(bs1, bs2) || !checkMatchingBlocks(bs2, bs1)) return false

    // Check matching blocks
    val checkMatchingApps = (as1: List[Heaplet], as2: List[Heaplet]) =>
      as1.forall {
        case SApp(x1, xs1) =>
          as2.exists { case SApp(x2, xs2) => x1 == x2 && xs1.size == xs2.size; case _ => false }
        case _ => false
      }
    if (!checkMatchingApps(as1, as2) || !checkMatchingApps(as2, as1)) return false

    true
  }

  /**
    * The result is a mapping of variables in the `source` to the variables in the `target`,
    * with the constraint that parameters of the former are not instantiated with the ghosts
    * of the latter (instantiating ghosts with anything is fine).
    */
  def unify(target: UnificationGoal, source: UnificationGoal): Option[(Assertion, Map[Var, Var])] = {
    // Make sure that all variables in target are fresh wrt. source
    val (freshSource, freshSubst) = refreshSource(target, source)

    val tFormula = target.formula
    val targetChunks = tFormula.sigma.chunks
    val sFormula = freshSource.formula
    val sourceChunks = sFormula.sigma.chunks
    val takenVars = tFormula.vars

    if (!checkShapesMatch(targetChunks, sourceChunks)) return None

    /**
      * Check that substitution does not substitutes ghosts for params
      */
    def checkSubstWF(sbst: Map[Var, Var]) = {
      val tParams = target.params
      val tGhosts = target.ghosts
      assert(tParams.intersect(tGhosts).isEmpty, s"Non empty sets: $tParams, $tGhosts")
      val sParams = freshSource.params
      val sGhosts = freshSource.ghosts
      assert(sParams.intersect(sGhosts).isEmpty, s"Non empty sets: $sParams, $sGhosts")
      sbst.forall { case (from, to) =>
        // If "to" is a ghost (in the target), the "from" also should be a ghost (in the source)
        (!tGhosts.contains(to) || sGhosts.contains(from)) &&
          // If "from" is a parameter (in the source), the "to" also should be a parameter (in the target)
          (!sParams.contains(from) || tParams.contains(to))
      }
    }

    /**
      * Tries to find amoungst chunks a heaplet h', which can be unified with the heaplet h.
      * If successful, returns a substitution and a list of remaining heaplets
      */
    def findChunkAndUnify(h: Heaplet, chunks: List[Heaplet]): Option[(Map[Var, Var], List[Heaplet])] = {
      val iter = chunks.iterator
      while (iter.hasNext) {
        val candidate = iter.next()
        tryUnify(h, candidate, takenVars) match {
          case Some(sbst) if checkSubstWF(sbst) => // found a good substitution
            // Return it and remaining chunks with the applied substitution
            val remainingHeapletsAdapted = chunks.filter(_ != candidate).map(_.subst(sbst))
            return Some(sbst, remainingHeapletsAdapted)
          case _ => // Do nothing
        }
      }
      None
    }

    // Invariant: none of the keys in acc are present in sourceChunks
    def unifyGo(targetChunks: List[Heaplet], sourceChunks: List[Heaplet], acc: Map[Var, Var]): Option[Map[Var, Var]] = targetChunks match {
      case Nil =>
        // No more source chunks to unify
        if (sourceChunks.isEmpty) Some(acc) else None
      case tc :: tcss => findChunkAndUnify(tc, sourceChunks) match {
        case None => None
        // Could not find a matching heaplet
        case Some((sbst, scsUpdated)) =>
          assertNoOverlap(acc, sbst)
          unifyGo(tcss, scsUpdated, acc ++ sbst)
      }
    }

    // Lazily try all permutations of source chunks
    // Ugly imperative stuff below
    val iter = targetChunks.permutations
    while (iter.hasNext) {
      val tChunks = iter.next()
      unifyGo(tChunks, sourceChunks, Map.empty) match {
        case Some(newSubst) =>
          // Found unification, see if it captures all variables in the pure part
          val newAssertion = sFormula.subst(newSubst)
          if (newAssertion.vars.forall(tFormula.vars.contains(_))) {
            // No free variables after substitution => successful unification
            /*
            TODO: Check via external prover that the new target pure part is implied by the source pure part, i.e.,
             sFormula.phi implies newAssertion.phi
             */
            return Some((newAssertion, compose(freshSubst, newSubst)))
          }
        // Otherwise, continue
        case None =>
      }
    }
    None
  }

  def compose(subst1: Map[Var, Var], subst2: Map[Var, Var]) : Map[Var, Var] = {
    subst1.map { case (k, v) => k -> subst2.getOrElse(v, v) }
  }

  def ppSubst(m: Map[Var, Var]): String = {
    s"{${m.map{case (k, v) => s"${k.pp} -> ${v.pp}"}.mkString("; ")}}"
  }
}

/**
  * A parameterized formula, for which unification produces the substitution
  */
case class UnificationGoal(formula: Assertion, params: Set[Var]) {
  def ghosts: Set[Var] = formula.vars -- params

  override def toString: String = s"(${params.map(_.pp).mkString(", ")}) ${formula.pp}"
}