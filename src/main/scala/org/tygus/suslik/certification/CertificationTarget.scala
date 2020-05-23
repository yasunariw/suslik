package org.tygus.suslik.certification

import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.synthesis.Trace

trait CertificationTarget {
  val name: String
  def certify(proc: Procedure, trace: Trace, env: Environment): Certificate
}
