package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Expressions.{Expr, PFormula, Var}
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.SApp

sealed abstract class StmtComputation {
  def run(stmts: Seq[Statement]): Statement
}

case object PureKont extends StmtComputation {
  override def run(stmts: Seq[Statement]): Statement = stmts.head
}

case class Prepend(s: Statement) extends StmtComputation {
  override def run(stmts: Seq[Statement]): Statement = {
    val rest = stmts.head
    SeqComp(s, rest).simplify
  }
}

case class PrependCall(s: Statement, sub: Map[Var, Expr]) extends StmtComputation {
  override def run(stmts: Seq[Statement]): Statement = {
    val rest = stmts.head
    SeqComp(s, rest).simplify
  }
}

case class PrependFromSketch(s: Statement) extends StmtComputation {
  override def run(stmts: Seq[Statement]): Statement = {
    val rest = stmts.head
    SeqComp(s, rest)
  }
}

case class Append(s: Statement) extends StmtComputation {
  override def run(stmts: Seq[Statement]): Statement = {
    val rest = stmts.head
    SeqComp(rest, s).simplify
  }
}

case object MakeSkip extends StmtComputation {
  override def run(stmts: Seq[Statement]): Statement = Skip
}

case object MakeError extends StmtComputation {
  override def run(stmts: Seq[Statement]): Statement = Error
}

case object MakeMagic extends StmtComputation {
  override def run(stmts: Seq[Statement]): Statement = Magic
}

case class MakeGuarded(cond: Expr) extends StmtComputation {
  override def run(stmts: Seq[Statement]): Statement = Guarded(cond, stmts.head)
}

case class MakeOpen(selectors: Seq[PFormula], app: SApp) extends StmtComputation {
  override def run(stmts: Seq[Statement]): Statement = {
    if (stmts.length == 1) stmts.head else {
      val cond_branches = selectors.zip(stmts).reverse
      val ctail = cond_branches.tail
      val finalBranch = cond_branches.head._2
      ctail.foldLeft(finalBranch) { case (eb, (c, tb)) => If(c, tb, eb).simplify }
    }
  }
}

case class MakeIf(cond: Expr) extends StmtComputation {
  override def run(stmts: Seq[Statement]): Statement = If(cond, stmts.head, stmts.last)
}

case class MakeAbduceCall(n: Int) extends StmtComputation {
  override def run(stmts: Seq[Statement]): Statement = {
    val writes = stmts.take(n)
    val rest = stmts.drop(n).head
    writes.foldRight(rest) { case (w, r) => SeqComp(w, r) }
  }
}