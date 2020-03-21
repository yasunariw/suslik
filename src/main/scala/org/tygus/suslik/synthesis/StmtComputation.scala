package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Expressions.{Expr, PFormula, Var}
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.SApp

sealed abstract class StmtComputation {
  def apply(stmts: Seq[Statement]): Statement
}

case object PureKont extends StmtComputation {
  override def apply(stmts: Seq[Statement]): Statement = stmts.head
}

case class Prepend(s: Statement) extends StmtComputation {
  override def apply(stmts: Seq[Statement]): Statement = {
    val rest = stmts.head
    SeqComp(s, rest).simplify
  }
}

case class PrependCall(s: Statement, sub: Map[Var, Expr]) extends StmtComputation {
  override def apply(stmts: Seq[Statement]): Statement = {
    val rest = stmts.head
    SeqComp(s, rest).simplify
  }
}

case class PrependFromSketch(s: Statement) extends StmtComputation {
  override def apply(stmts: Seq[Statement]): Statement = {
    val rest = stmts.head
    SeqComp(s, rest)
  }
}

case class Append(s: Statement) extends StmtComputation {
  override def apply(stmts: Seq[Statement]): Statement = {
    val rest = stmts.head
    SeqComp(rest, s).simplify
  }
}

case object MakeSkip extends StmtComputation {
  override def apply(stmts: Seq[Statement]): Statement = Skip
}

case object MakeError extends StmtComputation {
  override def apply(stmts: Seq[Statement]): Statement = Error
}

case object MakeMagic extends StmtComputation {
  override def apply(stmts: Seq[Statement]): Statement = Magic
}

case class MakeGuarded(cond: Expr) extends StmtComputation {
  override def apply(stmts: Seq[Statement]): Statement = Guarded(cond, stmts.head)
}

case class MakeOpen(selectors: Seq[PFormula], app: SApp) extends StmtComputation {
  override def apply(stmts: Seq[Statement]): Statement = {
    def mkNestedIf(branches: List[(Expr, Statement)]): Statement = branches match {
      case b :: Nil => b._2
      case b :: rest => If(b._1, b._2, mkNestedIf(rest)).simplify
    }
    mkNestedIf(selectors.zip(stmts).toList)
  }
}

case class MakeIf(cond: Expr) extends StmtComputation {
  override def apply(stmts: Seq[Statement]): Statement = If(cond, stmts.head, stmts.last)
}

case class MakeAbduceCall(n: Int) extends StmtComputation {
  override def apply(stmts: Seq[Statement]): Statement = {
    val writes = stmts.take(n)
    val rest = stmts.drop(n).head
    writes.foldRight(rest) { case (w, r) => SeqComp(w, r) }
  }
}