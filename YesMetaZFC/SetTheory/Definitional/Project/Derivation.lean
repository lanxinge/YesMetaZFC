import YesMetaZFC.SetTheory.Language
import YesMetaZFC.Model.SetTheory.Theory
import YesMetaZFC.Logic.FirstOrder.Derivation.Consistency

/-!
# Project 集合论的内在类型一阶翻译

Project 句子直接翻译到纯集合论签名 `ℒ`。目标项与公式的排序、bound scope 和
free closure 全部由类型索引保证；翻译只接受源语法已有的 `FreeClosed` 证书，
因此不再产生 `TermWellSorted`、`FormulaScoped` 或 admissibility 证明义务。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project

open Logic FirstOrder

set_option autoImplicit false

/-- 深度 `depth` 的单排序 bound 上下文。 -/
abbrev fo_bound_context (depth : Nat) :
    FirstOrder.SortContext ℒ :=
  List.replicate depth SetSort.set

/-- `Fin` 深度索引直接解释为同深度内在变量。 -/
def fo_bound_variable :
    {depth : Nat} → Fin depth →
      FirstOrder.Variable (fo_bound_context depth) SetSort.set
  | 0, entry => Fin.elim0 entry
  | _ + 1, entry =>
      Fin.cases FirstOrder.Variable.here
        (fun previous =>
          FirstOrder.Variable.there (fo_bound_variable previous)) entry

/-- 自由闭合的 Project 项直接翻译为纯集合论内在项。 -/
def fo_term {depth : Nat} (term : Term depth)
    (hClosed : term.freeSupport = []) :
    FirstOrder.Term ℒ (fo_bound_context depth) [] SetSort.set :=
  match term with
  | .bound entry =>
      .bvar (fo_bound_variable entry)
  | .free id => by
      change id :: [] = [] at hClosed
      cases hClosed

/-- 纯集合论中的内在隶属原子。 -/
def fo_mem {bound : FirstOrder.SortContext ℒ}
    (left right : FirstOrder.Term ℒ bound [] SetSort.set) :
    FirstOrder.Formula ℒ bound [] :=
  .rel RelationSymbol.membership
    (.cons left (.cons right .nil))

/-- 自由闭合的 Project 公式直接翻译为纯集合论内在公式。 -/
def fo_formula :
    {availableStage depth : Nat} →
      (formula : Formula availableStage depth) →
      formula.FreeClosed →
        FirstOrder.Formula ℒ (fo_bound_context depth) []
  | _, _, .falsum, _ =>
      .falsum
  | _, _, .truth, _ =>
      .truth
  | _, _, .mem left right, hClosed => by
      simp only [Formula.FreeClosed] at hClosed
      exact fo_mem
        (fo_term left hClosed.1)
        (fo_term right hClosed.2)
  | _, _, .atom .extensionalEq _ arguments, hClosed => by
      simp only [Formula.FreeClosed] at hClosed
      exact .equal
        (fo_term (arguments 0) (hClosed 0))
        (fo_term (arguments 1) (hClosed 1))
  | _, _, .atom .subset _ arguments, hClosed => by
      simp only [Formula.FreeClosed] at hClosed
      exact .forallE SetSort.set <|
        .imp
          (fo_mem
            (.bvar .here)
            ((fo_term (arguments 0) (hClosed 0)).weakenBound
              SetSort.set))
          (fo_mem
            (.bvar .here)
            ((fo_term (arguments 1) (hClosed 1)).weakenBound
              SetSort.set))
  | _, _, .neg body, hClosed => by
      simp only [Formula.FreeClosed] at hClosed
      exact .neg (fo_formula body hClosed)
  | _, _, .conj left right, hClosed => by
      simp only [Formula.FreeClosed] at hClosed
      exact .conj
        (fo_formula left hClosed.1)
        (fo_formula right hClosed.2)
  | _, _, .disj left right, hClosed => by
      simp only [Formula.FreeClosed] at hClosed
      exact .disj
        (fo_formula left hClosed.1)
        (fo_formula right hClosed.2)
  | _, _, .imp left right, hClosed => by
      simp only [Formula.FreeClosed] at hClosed
      exact .imp
        (fo_formula left hClosed.1)
        (fo_formula right hClosed.2)
  | _, _, .iff left right, hClosed => by
      simp only [Formula.FreeClosed] at hClosed
      exact .iff
        (fo_formula left hClosed.1)
        (fo_formula right hClosed.2)
  | _, _, .forallE body, hClosed => by
      simp only [Formula.FreeClosed] at hClosed
      exact .forallE SetSort.set (fo_formula body hClosed)
  | _, _, .existsE body, hClosed => by
      simp only [Formula.FreeClosed] at hClosed
      exact .existsE SetSort.set (fo_formula body hClosed)

/-- Project 句子的纯集合论闭句像。 -/
def fo_sentence (sentence : Sentence) :
    FirstOrder.Sentence ℒ :=
  fo_formula sentence.formula sentence.freeClosed

/-- Project 理论的纯集合论闭句像。 -/
def fo_theory (T : Theory) :
    FirstOrder.Theory ℒ :=
  fun target =>
    ∃ source, T source ∧ target = fo_sentence source

/-- 原始 Project 理论中的可推导性。 -/
def Derives (T : Theory) (sentence : Sentence) : Prop :=
  FirstOrder.Derives (fo_theory T) [] (fo_sentence sentence)

/-- 原始 Project 理论的一致性。 -/
def Consistent (T : Theory) : Prop :=
  FirstOrder.Derives.Consistent (fo_theory T) ([] : FirstOrder.Context ℒ [])

end Project
end Definitional
end SetTheory
end YesMetaZFC
