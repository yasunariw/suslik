package org.tygus.suslik.coq

import org.tygus.suslik.coq.language.Expressions.CVar

package object language {
  type CGamma = Map[CVar, CoqType]
  type CFormals = Seq[(CoqType, CVar)]
  type CPredicateEnv = Map[String, CInductivePredicate]
}
