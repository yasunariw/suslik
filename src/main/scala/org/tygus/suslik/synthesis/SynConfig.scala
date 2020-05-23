package org.tygus.suslik.synthesis

import java.io.File

import org.tygus.suslik.certification.CertificationTarget
import org.tygus.suslik.language.PrettyPrinting

/**
  * @author Ilya Sergey
  */

sealed trait InputFormat
case object dotSyn extends InputFormat
case object dotSus extends InputFormat

case class SynConfig(
                      // Synthesis params
                      startingDepth: Int        = 100,
                      maxOpenDepth: Int         = 1,
                      maxCloseDepth: Int        = 1,
                      branchAbduction: Boolean  = false,
                      phased: Boolean           = true,
                      invert: Boolean           = true,
                      fail: Boolean             = true,
                      commute: Boolean          = true,
                      // Timeout and logging
                      printStats: Boolean = true,
                      printDerivations: Boolean = false,
                      printFailed: Boolean      = false,
                      printTags: Boolean        = false,
                      printEnv: Boolean         = false,
                      assertSuccess: Boolean    = true,
                      logToFile: Boolean        = true,
                      memoization: Boolean        = true,
                      timeOut: Long             = DEFAULT_TIMEOUT*100,
                      inputFormat: InputFormat = dotSyn,
                      // Certification
                      certTarget: CertificationTarget = null,
                      certDest: File = null,
                      printCertTrace: Boolean = false
                    ) extends PrettyPrinting {

  override def pp: String =
    ( (if (maxOpenDepth == defaultConfig.maxOpenDepth) Nil else List(s"maxOpenDepth = $maxOpenDepth")) ++
      (if (maxCloseDepth == defaultConfig.maxCloseDepth) Nil else List(s"maxCloseDepth = $maxCloseDepth")) ++
      (if (branchAbduction == defaultConfig.branchAbduction) Nil else List(s"branchAbduction = $branchAbduction")) ++
      (if (phased == defaultConfig.phased) Nil else List(s"phased = $phased")) ++
      (if (invert == defaultConfig.invert) Nil else List(s"invert = $invert")) ++
      (if (fail == defaultConfig.fail) Nil else List(s"fail = $fail")) ++
      (if (commute == defaultConfig.commute) Nil else List(s"commute = $commute")) ++
      (if (certTarget == defaultConfig.certTarget) Nil else List(s"certTarget = ${certTarget.name}")) ++
      (if (certDest == defaultConfig.certDest) Nil else List(s"certDest = ${certDest.getCanonicalPath}")) ++
      (if (printCertTrace == defaultConfig.printCertTrace) Nil else List(s"printCertTrace = $printCertTrace"))
      ).mkString(", ")
}

case class SynTimeOutException(msg: String) extends Exception(msg)

case class SynthesisException(msg: String) extends Exception(msg)
case class SymbolicExecutionError(msg: String) extends Exception(msg)


