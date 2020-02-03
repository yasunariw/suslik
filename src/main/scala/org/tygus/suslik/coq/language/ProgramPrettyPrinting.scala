package org.tygus.suslik.coq.language

trait ProgramPrettyPrinting extends PrettyPrinting {
  def ppp: String = this.pp
}
