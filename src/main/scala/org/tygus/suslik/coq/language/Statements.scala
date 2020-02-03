package org.tygus.suslik.coq.language

import org.tygus.suslik.util.StringUtil._

object Statements {
  import Expressions._

  sealed abstract class CStatement extends ProgramPrettyPrinting {
    override def pp: String = {
      val builder = new StringBuilder

      def build(s: CStatement, offset: Int = 2) : Unit = {
        s match {
          case CSkip =>
            builder.append(mkSpaces(offset))
            builder.append("ret tt")
          case CHole => ???
          case CError => ???
          case CMagic => ???
          case CMalloc(to, _, sz) =>
            builder.append(mkSpaces(offset))
            builder.append(s"${to.ppp} <-- allocb ${to.ppp} $sz")
          case CFree(v) =>
            builder.append(mkSpaces(offset))
            builder.append(s"dealloc ${v.ppp}")
          case CStore(to, off, e) =>
            builder.append(mkSpaces(offset))
            val t = if (off <= 0) to.ppp else s"(${to.ppp} .+ $off)"
            builder.append(s"$t ::= ${e.ppp}")
          case CLoad(to, tpe, from, off) =>
            builder.append(mkSpaces(offset))
            val f = if (off <= 0) from.ppp else s"(${from.ppp} .+ $off)"
            builder.append(s"${to.ppp} <-- !$f")
          case CCall(tt, fun, args) =>
            builder.append(mkSpaces(offset))
            val function_call = s"${fun.ppp} ${args.map(_.ppp).mkString(" ")}"
            // TODO: handle return types
            builder.append(function_call)
          case CSeqComp(s1, s2) =>
            build(s1, offset)
            s1 match {
              case _: ReturnsValue => builder.append(";\n")
              case _ => builder.append(";;\n")
            }
            build(s2, offset)
          case CIf(cond, tb, eb) =>
            builder.append(mkSpaces(offset))
            builder.append(s"if ${cond.ppp}\n")
            builder.append(mkSpaces(offset))
            builder.append(s"then\n")
            build(tb, offset + 2)
            builder.append("\n")
            builder.append(mkSpaces(offset)).append(s"else\n")
            build(eb, offset + 2)
            builder.append("\n")
          case CGuarded(cond, body) => ???
        }
      }

      build(this)
      builder.toString()
    }
  }

  trait ReturnsValue

  case object CSkip extends CStatement

  case object CHole extends CStatement

  case object CError extends CStatement

  case object CMagic extends CStatement

  case class CMalloc(to: CVar, tpe: CoqType, sz: Int = 1) extends CStatement with ReturnsValue

  case class CFree(v: CVar) extends CStatement

  case class CLoad(to: CVar, tpe: CoqType, from: CVar, offset: Int = 0) extends CStatement with ReturnsValue

  case class CStore(to: CVar, offset: Int, e: CExpr) extends CStatement

  case class CCall(to: Option[(CVar, CoqType)], fun: CVar, args: Seq[CExpr]) extends CStatement

  case class CIf(cond: CExpr, tb: CStatement, eb: CStatement) extends CStatement

  case class CSeqComp(s1: CStatement, s2: CStatement) extends CStatement

  case class CGuarded(cond: CExpr, body: CStatement) extends CStatement

  case class CProcedure(name: String, tp: CoqType, formals: Seq[(CoqType, CVar)], body: CStatement) extends CStatement {
    override def pp: String = {
      (""
        + s"Program Definition $name : ${name}_type :=\n"
        + s"  Fix (fun ($name : ${name}_type) ${formals.map(f => f._2.ppp).mkString(" ")} =>\n"
        + s"    Do (\n"
        + s"${body.ppp}"
        + s"    ))."
        ).stripMargin
    }
  }
}
