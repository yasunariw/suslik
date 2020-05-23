package org.tygus.suslik.certification.targets.coq

import org.tygus.suslik.certification.CertificationTarget
import org.tygus.suslik.certification.targets.coq.translation.Translator
import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.synthesis.Trace

import scala.io.Source

object Coq extends CertificationTarget {
  val name: String = "Coq"

  def certify(proc: Procedure, trace: Trace, env: Environment): CoqCertificate = {
    val builder = new StringBuilder
    val headersFile = "htt-tactics.v"
    val headers = Source.fromFile(headersFile)
    for (line <- headers.getLines) builder.append(s"$line\n")
    headers.close()
    for (label <- (trace.spec.pre.sigma.apps ++ trace.spec.post.sigma.apps).distinct.map(_.pred)) {
      val predicate = env.predicates(label)
      builder.append(Translator.runInductivePredicate(predicate.resolveOverloading(env)).pp)
      builder.append("\n")
    }
    builder.append(Translator.runFunSpecFromTrace(trace).pp)
    builder.append("\n")
    builder.append(Translator.runProcedure(proc, trace).ppp)
    builder.append("\n")
    builder.append(Translator.runProofFromTrace(trace, env.predicates).pp)

    CoqCertificate(builder.toString(), proc.name)
  }
}
