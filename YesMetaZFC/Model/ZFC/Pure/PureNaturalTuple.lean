import YesMetaZFC.Model.ZFC.Pure.PureStructuralCodeBounds

/-! # 内部自然数元组

固定长度的 Kuratowski 元组用于收集递归关系。长度是公式的外部有限元数，
元组各坐标仍遍历模型内部的全部自然数。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalTuple
open PureModel PureNaturalInduction PureArithmeticSpecifications
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}
noncomputable abbrev E (hℳ : Theory.Models ℳ theory) := PureSyntaxStage.expansion hℳ
open PureSyntaxOperator (pair pair_injective pair_mem_product)

def term {bound free : SortContext S} : List (Term S bound free s) → Term S bound free s
  | [] => empty_set_term
  | head :: tail => ordered_pair_term head (term tail)

noncomputable def value (hℳ : Theory.Models ℳ theory) : List (Carrier ℳ) → Carrier ℳ
  | [] => zero hℳ
  | head :: tail => PureSyntaxOperator.pair hℳ head (value hℳ tail)

theorem eval (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (fields : List (Term S bound free s)) :
    (term fields).eval env = value hℳ (fields.map (fun t => t.eval env)) := by
  induction fields with
  | nil => exact PureSyntaxOperator.zero_eq hℳ
  | cons head tail ih =>
    change PureSyntaxOperator.pair hℳ (head.eval env) ((term tail).eval env) = _
    rw [ih]; rfl

theorem injective (hℳ : Theory.Models ℳ theory) {first second : List (Carrier ℳ)}
    (hLength : first.length = second.length) (hValue : value hℳ first = value hℳ second) : first = second := by
  induction first generalizing second with
  | nil => cases second <;> first | rfl | contradiction
  | cons head tail ih =>
    cases second with
    | nil => contradiction
    | cons other rest =>
      obtain ⟨rfl,hTail⟩ := pair_injective hℳ hValue
      exact congrArg (List.cons head) (ih (Nat.succ.inj hLength) hTail)

noncomputable def ambient (hℳ : Theory.Models ℳ theory) : Nat → Carrier ℳ
  | 0 => omega hℳ
  | n + 1 => (PureSyntaxOperator.E hℳ).function .cartesianProduct (.cons (omega hℳ) (.cons (ambient hℳ n) .nil))

theorem bounded (hℳ : Theory.Models ℳ theory) (fields : List (Carrier ℳ))
    (hFields : ∀ field ∈ fields, membership ℳ field (omega hℳ)) :
    membership ℳ (value hℳ fields) (ambient hℳ fields.length) := by
  induction fields with
  | nil => exact zero_mem hℳ
  | cons head tail ih =>
    exact pair_mem_product hℳ (hFields head (by simp)) (ih (fun field hf => hFields field (by simp [hf])))
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureNaturalTuple
