package org.tygus.suslik.coq.translation

import org.tygus.suslik.language.Statements.Procedure
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.synthesis.Trace

import scala.io.Source

trait Certifiable {
  def certify(proc: Procedure, trace: Trace, env: Environment): String = {
    val builder = new StringBuilder
    builder.append(trace.pp)
    builder.append("\n")
    builder.append("Synthesized Certificate:\n")
    val headersFile = "htt-tactics.v"
    val headers = Source.fromFile(headersFile)
    for (line <- headers.getLines) builder.append(line)
    headers.close()
    for (label <- (trace.spec.pre.sigma.apps ++ trace.spec.post.sigma.apps).distinct.map(_.pred)) {
      val predicate = env.predicates(label)
      builder.append(Translator.runInductivePredicate(predicate.resolveOverloading(env)).pp)
    }
    builder.append(Translator.runFunSpecFromTrace(trace).pp)
    builder.append(Translator.runProcedure(proc, trace).ppp)
    builder.append(Translator.runProofFromTrace(trace, env.predicates).pp)

    builder.toString()
  }
}
