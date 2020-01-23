package org.tygus.suslik.coq.translation

import java.io.File

import org.tygus.suslik.logic.Resolver._
import org.tygus.suslik.parsing.SSLParser
import org.tygus.suslik.synthesis.{SynConfig, Synthesis, SynthesisException, SynthesisRunnerUtil, defaultConfig}
import org.tygus.suslik.synthesis.SynthesisRunner._
import org.tygus.suslik.synthesis.instances.PhasedSynthesis
import org.tygus.suslik.util.{SynLogLevels, SynLogging, SynStatUtil}

object TranslationRunner extends SynthesisRunnerUtil {

  override implicit val log : SynLogging = SynLogLevels.Test
  import log._

  def main(args: Array[String]): Unit = {
    handleInput(args)
  }

  private def getParentDir(filePath: String): String = {
    val file = new File(filePath)
    if (!file.exists()) {
      "."
    }
    else file.getParentFile.getAbsolutePath
  }

  private def handleInput(args: Array[String]): Unit = {
    val file = args(0)
    val synConfig = SynConfig()
    val config = RunConfig(synConfig, file)
    val dir = getParentDir(file)
    val fName = new File(file).getName
    runSingleTestFromDir(dir, fName, synConfig)
  }

  override val synthesis: Synthesis = new PhasedSynthesis()

  import synthesis._

  override def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig): Unit = {
    if (params.printStats) {
      println(desc)
      println()
    }
    try {
      synthesizeFromSpec(testName, in, out, params)
    } catch {
      case SynthesisException(msg) =>
        System.err.println("Synthesis failed:")
        System.err.println(msg)
    }
  }

  override def synthesizeFromSpec(testName: String, text: String, out: String = noOutputCheck, params: SynConfig = defaultConfig) : Unit = {
    val parser = new SSLParser
    val res = parser.parseGoalSYN(text)
    if (!res.successful) {
      throw SynthesisException(s"Failed to parse the input:\n$res")
    }

    val prog = res.get
    // assert(prog.predicates.nonEmpty)
    val (specs, env, body) = resolveProgram(prog)

    if (specs.lengthCompare(1) != 0) {
      throw SynthesisException("Expected a single synthesis goal")
    }

    val lseg = env.predicates("lseg")
    val cLseg = Translator.runInductivePredicate(lseg.resolveOverloading(env))
    testPrintln(cLseg.pp)

    val spec = specs.head
    val time1 = System.currentTimeMillis()
    val sresult = synthesizeProc(spec, env.copy(config = params), body)
    val time2 = System.currentTimeMillis()
    val delta = time2 - time1

    SynStatUtil.log(testName, delta, params, spec, sresult)

    sresult match {
      case Some((rr, stats)) =>
        val result = rr.pp
        if (params.printStats) {
          testPrintln(s"\n[$testName]:", Console.MAGENTA)
          testPrintln(params.pp)
          testPrintln(s"${spec.pp}\n", Console.BLUE)
          testPrintln(s"Successfully synthesised in $delta milliseconds:", Console.GREEN)
          testPrintln(s"Number of backtrackings ${stats.numBack}")
          testPrintln(s"Lasting successful rule applications: ${stats.numLasting}")
          testPrintln(s"Total successful rule applications: ${stats.numSucc}")
          testPrintln(s"Final size of SMT cache: ${stats.smtCacheSize}")
          testPrintln(s"Number of saved negative results: ${stats.numSavedResultsNegative}")
          testPrintln(s"Number of saved positive results: ${stats.numSavedResultsPositive}")
          testPrintln(s"Number of recalled negative results: ${stats.numRecalledResultsNegative}")
          testPrintln(s"Number of recalled positive results: ${stats.numRecalledResultsPositive}")
          testPrintln(result)
          testPrintln("-----------------------------------------------------")
        } else {
          println(result)
        }
        if (out != noOutputCheck) {
          val tt = out.trim.lines.toList
          val res = result.trim.lines.toList
          if (params.assertSuccess && res != tt) {
            throw SynthesisException(s"\nThe expected output\n$tt\ndoesn't match the result:\n$res")
          }
        }
      case None =>
        throw SynthesisException(s"Failed to synthesise:\n$sresult")
    }
  }
}
