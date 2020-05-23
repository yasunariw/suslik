package org.tygus.suslik.coq

import org.scalatest.{FunSpec, Matchers}
import org.tygus.suslik.synthesis.{SynConfig, Synthesis, SynthesisRunnerUtil, defaultConfig}
import org.tygus.suslik.synthesis.instances.PhasedSynthesis

/**
  * @author Yasunari Watanabe
  */

class CertificationTests extends FunSpec with Matchers with SynthesisRunnerUtil {

  val synthesis: Synthesis = new PhasedSynthesis

  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig): Unit =
    it(s"certifies that it $desc") {
      synthesizeFromSpec(testName, in, out, params.copy(certify = true))
    }

  describe("SL-based synthesizer with certification") {
    runAllTestsFromDir("certification")
  }

}