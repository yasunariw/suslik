package org.tygus.suslik.certification.targets.vst.logic

import org.tygus.suslik.certification.targets.vst.Types._
import org.tygus.suslik.certification.targets.vst.logic.Formulae.VSTHeaplet
import org.tygus.suslik.certification.targets.vst.translation.Translation.TranslationException
import org.tygus.suslik.certification.translation.{CardConstructor, CardNull, CardOf, GenericPredicate, GenericPredicateClause}
import org.tygus.suslik.language.{Ident, PrettyPrinting}

object ProofTerms {

  trait PureFormula extends PrettyPrinting

  /**
    * Represents helper lemmas and operations that are required to make VST handle the predicate automatically
    * */
  trait VSTPredicateHelper extends PrettyPrinting

  /** predicate encoding that C-parameter (of type val) is a valid pointer */
  case class IsValidPointerOrNull(name: String) extends PureFormula {
    override def pp: String =
      s"is_pointer_or_null(${name})"
  }

  /** predicate encoding that C-parameter (of type val) is a valid int */
  case class IsValidInt(name: String) extends PureFormula {
    override def pp: String =
      s"ssl_is_valid_int(${name})"
  }

  /** prop predicate encoding that a given propositional expression is true
    * */
  case class IsTrueProp(expr: Expressions.ProofCExpr) extends PureFormula {
    override def pp: String = {
      s"${expr.pp}"
    }
  }

  /** prop predicate encoding that a given boolean expression is true */
  case class IsTrue(expr: Expressions.ProofCExpr) extends PureFormula {
    override def pp: String = {
      s"(is_true ${expr.pp_as_c_value})"
    }
  }

  case class FormalCondition(
                              pure_constraints: List[PureFormula],
                              spatial_constraints: List[VSTHeaplet]
                            )

  /**
    * Type encoding VST-compliant formal specifications of a C Function
    *
    * @param name               name of the function
    * @param c_params           parameters of the function
    * @param formal_params      parameters of the specification
    * @param existensial_params existential params of the function
    * @param precondition       precondtion for the function
    * @param postcondition      post condition of the function
    */
  case class FormalSpecification(
                                  name: Ident,
                                  c_params: Seq[(Ident, VSTCType)],
                                  formal_params: Seq[(Ident, VSTType)],
                                  existensial_params: Seq[(Ident, VSTType)],
                                  precondition: FormalCondition,
                                  postcondition: FormalCondition,
                                ) extends PrettyPrinting {

    def params: List[(Ident, VSTType)] = (c_params ++ formal_params).toList

    override def pp: String = {
      val formal_args = formal_params.map({ case (var_name, var_type) => s"${var_name}: ${var_type.pp}" })
      val c_args = c_params.map({ case (var_name, _) => s"${var_name}: val" })
      val FormalCondition(pre_pure_constraints, pre_spatial_constraints) = precondition
      val FormalCondition(post_pure_constraints, post_spatial_constraints) = postcondition
      s"""Definition ${name}_spec :=
         |  DECLARE _${name}
         |   WITH ${(c_args ++ formal_args).mkString(", ")}
         |   PRE [ ${c_params.map({ case (_, var_type) => s"${as_vst_type(var_type)}" }).mkString(", ")} ]
         |   PROP( ${pre_pure_constraints.map(_.pp).mkString("; ")} )
         |   PARAMS(${c_params.map({ case (var_name, _) => var_name }).mkString("; ")})
         |   SEP (${pre_spatial_constraints.map(_.pp).mkString("; ")})
         |   POST[ tvoid ]${
        existensial_params match {
          case Nil => ""
          case _ =>
            "\n" ++
              existensial_params.map({ case (param_name, param_type) => s"|   EX ${param_name}: ${param_type.pp}," }).mkString("\n")
        }
      }
         |   PROP( ${post_pure_constraints.map(_.pp).mkString("; ")} )
         |   LOCAL()
         |   SEP (${post_spatial_constraints.map(_.pp).mkString("; ")}).
         |""".stripMargin
    }

    def as_vst_type(var_type: VSTCType) = var_type match {
      case CoqIntValType => "tint"
      case CoqPtrValType => "(tptr (Tunion _sslval noattr))"
      case _ => throw TranslationException(s"Attempt to convert invalid type ${var_type.pp} as a VST type term.")
    }
  }

  /** represents a clause of the VST predicate,
    *
    * @param pure            are the pure assertions
    * @param spatial         are the spatial assertions
    * @param sub_constructor are the subconstructors
    * */
  case class VSTPredicateClause(override val pure: List[Expressions.ProofCExpr],
                                override val spatial: List[VSTHeaplet],
                                sub_constructor: Map[String, CardConstructor])
  extends GenericPredicateClause[Expressions.ProofCExpr, VSTHeaplet](pure, spatial, sub_constructor)
  /**
    * represents a VST inductive predicate defined in a format that satisfies Coq's termination checker
    *
    * The idea is to conver the cardinality constraints produced by suslik into an inductive datatype
    * with the expectation that each clause of the suslik predicate maps to a unique constructor
    *
    * Constructors are identified by their cardinality, and each suslik predicate maps to a unique cardinality datatype
    *
    * @param name    is the name of the predicate
    * @param params  is the list of arguments to the predicate
    * @param clauses is the mapping from cardinality constructors to clauses
    * */
  case class VSTPredicate(override val name: Ident,
                          override val params: List[(String, VSTType)],
                          override val existentials: List[(String, VSTType)],
                          override val clauses: Map[CardConstructor, VSTPredicateClause])
    extends GenericPredicate[Expressions.ProofCExpr, VSTHeaplet, VSTType](name, params, existentials, clauses) {

    /** returns any helper lemmas that need to be constructed for the helper */
    def get_helpers: List[VSTPredicateHelper] = {
      val local_facts = VSTPredicateHelper.LocalFacts(this)
      params.flatMap({
        case (param, CoqPtrValType) =>
          val valid_lemma = VSTPredicateHelper.ValidPointer(name, this.formalParams, param)
          List(
            valid_lemma, VSTPredicateHelper.HintResolve(valid_lemma.lemma_name, "valid_pointer")
          )
        case _ => List()
      }) ++ List(
        local_facts,
        VSTPredicateHelper.HintResolve(local_facts.lemma_name, "saturate_local")
      )
    }

    /** pretty print the constructor */
    def ppPredicate: String = {
      val predicate_definition =
        s"""Fixpoint ${name} ${params.map({ case (name, proofType) => s"(${name}: ${proofType.pp})" }).mkString(" ")} (self_card: ${inductiveName}) : mpred := match self_card with
           ${
          clauses.map({ case (constructor, pclause@VSTPredicateClause(pure, spatial, sub_constructor)) =>
            s"|    | ${constructorName(constructor)} ${
              expandArgs(sub_constructor)(constructor.constructor_args)
            } => ${
              val clause_existentials: List[(String, VSTType)] = findExistentials(constructor)(pclause)
              val str = clause_existentials.map({ case (name, ty) => s"|      EX ${name} : ${ty.pp}," }).mkString("\n")
              clause_existentials match {
                case Nil => ""
                case ::(_, _) => "\n" + str + "\n"
              }
            } ${
              (pure.map(v => s"!!${v.pp}")
                ++
                List((spatial match {
                  case Nil => List("emp")
                  case v => v.map(_.pp)
                }).mkString(" * "))).mkString(" && ")
            }"
          }).mkString("\n")
        }
           |end.
           |""".stripMargin
      s"${predicate_definition}"
    }

    /**
      * For a given clause of the predicate and its associated constructor,
      * return the list of existential variables used in the body of the clause
      *
      * @param cons    a constructor matching some clause of the predicate
      * @param pclause the corresponding clause of the predicate
      * @return the list of pairs of (variable, variable_type) of all the existential variables in this clause
      * */
    def findExistentials(cons: CardConstructor)(pclause: GenericPredicateClause[Expressions.ProofCExpr, VSTHeaplet]): List[(String, VSTType)] = {
      val param_map = params.toMap
      val exist_map: Map[String, VSTType] = existentials.toMap
      val card_map = cons.constructor_args
      pclause match {
        case VSTPredicateClause(pure, spatial, sub_clauses) =>
          val clause_card_map = (card_map ++ sub_clauses.flatMap({ case (_, cons) => cons.constructor_args })).toSet

          def to_variables(exp: Expressions.ProofCExpr): List[String] = exp match {
            case Expressions.ProofCVar(name, typ) =>
              param_map.get(name) match {
                case None if !clause_card_map.contains(name) => List(name)
                case _ => List()
              }
            case Expressions.ProofCIntSetLiteral(elems) => elems.flatMap(to_variables)
            case Expressions.ProofCIfThenElse(cond, left, right) =>
              to_variables(cond) ++ to_variables(left) ++ to_variables(right)
            case Expressions.ProofCBinaryExpr(op, left, right) =>
              to_variables(left) ++ to_variables(right)
            case Expressions.ProofCUnaryExpr(op, e) =>
              to_variables(e)
            case _ => List()
          }

          def to_variables_heap(heap: VSTHeaplet): List[String] = heap match {
            case Formulae.CDataAt(loc, elems) =>
              to_variables(loc) ++ elems.flatMap(elem => to_variables(elem))
            case Formulae.CSApp(pred, args, card) =>
              args.flatMap(to_variables).toList
          }

          (pure.flatMap(to_variables) ++ spatial.flatMap(to_variables_heap): List[String])
            .toSet
            .map((v: String) => (v, exist_map(v))).toList
      }
    }
  }

  object VSTPredicateHelper {

    case class ValidPointer(predicate: String, args: List[String], ptr: String) extends VSTPredicateHelper {
      override def pp: String =
        s"Lemma ${lemma_name} ${args.mkString(" ")}: ${predicate} ${args.mkString(" ")} |-- valid_pointer ${ptr}. Proof. Admitted."

      def lemma_name: String = s"${predicate}_${ptr}_valid_pointerP"
    }

    case class HintResolve(lemma_name: String, hint_db: String) extends VSTPredicateHelper {
      override def pp: String =
        s"Hint Resolve ${lemma_name} : ${hint_db}."
    }

    case class LocalFacts(predicate: VSTPredicate) extends VSTPredicateHelper {

      override def pp: String = {

        def constructor_to_equality_term(vl: String, cons: CardConstructor) =
          if (cons.constructor_args.isEmpty) {
            s"${vl} = ${predicate.constructorName(cons)}"
          } else {
            s"exists ${cons.constructor_args.mkString(" ")}, ${vl} = ${predicate.constructorName(cons)} ${cons.constructor_args.mkString(" ")}"
          }

        /** Converts a predicate clause into a clause that mutually exclusively matches the clause
          *
          * Note: !!ASSUMPTION!! We assume that the first pure term of the predicate mutually exclusively matches the clause
          * */
        def predicate_to_determininant_term(clause: VSTPredicateClause): String =
          clause.pure.head.pp

        /** *
          * Converts a predicate clause into a corresponding fact.
          *
          * NOTE: !!!ASSUMPTION!!! We assume that the first clause of the vst predicate is mutually exclusive - i.e
          * if the first clause holds, then no other clause can hold.
          */
        def clause_fact(cardConstructor: CardConstructor, predicate: VSTPredicateClause): String =
          s"((${predicate_to_determininant_term(predicate)}) -> (${constructor_to_equality_term(predicate.cardinalityParam, cardConstructor)}))"


        s"""Lemma ${lemma_name} ${predicate.formalParams.mkString(" ")} :
           |  ${predicate.name} ${predicate.formalParams.mkString(" ")}|-- !!(${
          (
            predicate.clauses.toList.map({ case (cons, pred) => clause_fact(cons, pred) }) ++
              predicate.params.flatMap({ case (param, CoqPtrValType) => Some(s"(is_pointer_or_null ${param})") case _ => None })
            ).mkString("/\\")
        }). Proof. Admitted.""".stripMargin
      }

      def lemma_name: String = s"${predicate.name}_local_factsP"

    }

  }


}
