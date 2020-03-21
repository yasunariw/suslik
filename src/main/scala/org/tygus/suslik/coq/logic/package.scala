package org.tygus.suslik.coq

import org.tygus.suslik.coq.language.Expressions.CVar

package object logic {
  type ProofContext = Map[CVar, ProofContextItem]
}
