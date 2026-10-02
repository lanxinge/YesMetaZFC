import YesMetaZFC.Logic.FirstOrder.LevyHierarchy
import YesMetaZFC.Logic.FirstOrder.Metatheory.Propositional

/-! # 无函数纯关系语言中闭 Δ₀ 公式的边界

无函数符号时不存在闭项，因而无参数最外层有界量词也没有界项。
若关系符号均有参数，闭 Δ₀ 公式可由纯逻辑判定；该结论不依赖任何集合论公理。
-/
namespace YesMetaZFC.Automation.FunctionFreeDelta0
open Logic Logic.FirstOrder
set_option autoImplicit false
universe u v w
variable {σ : Signature.{u,v,w}}

theorem no_closed_term (hFunction : σ.FuncSymbol → False)
    {sort : σ.SortSymbol} (term : Term σ [] [] sort) : False := by
  cases term with
  | bvar entry => cases entry
  | fvar entry => cases entry
  | app symbol _ => exact hFunction symbol

theorem exists_not_delta0 (ℬ : Formula.LevyBound σ) (hFunction : σ.FuncSymbol → False)
    (sort : σ.SortSymbol) (body : Formula σ [sort] []) :
    ¬ Formula.IsDelta0 ℬ (.existsE sort body) := by
  intro h
  cases h with
  | bounded_exists bound _ => exact no_closed_term hFunction bound
  | guarded_exists bound _ _ => exact no_closed_term hFunction bound

theorem forall_not_delta0 (ℬ : Formula.LevyBound σ) (hFunction : σ.FuncSymbol → False)
    (sort : σ.SortSymbol) (body : Formula σ [sort] []) :
    ¬ Formula.IsDelta0 ℬ (.forallE sort body) := by
  intro h
  cases h with
  | bounded_forall bound _ => exact no_closed_term hFunction bound

/-- 无零元关系和函数的签名中，任意闭 Δ₀ 公式或其否定都有普通逻辑推导。 -/
theorem closed_decided (ℬ : Formula.LevyBound σ) (hFunction : σ.FuncSymbol → False)
    (hRelation : ∀ symbol, σ.relDomain symbol ≠ []) (T : Theory σ)
    (formula : Sentence σ) (hDelta : Formula.IsDelta0 ℬ formula) :
    Derives T [] formula ∨ Derives T [] (.neg formula) := by
  cases formula with
  | falsum => exact Or.inr (by derive_prop)
  | truth => exact Or.inl (by derive_prop)
  | rel symbol arguments =>
    cases hDomain : σ.relDomain symbol with
    | nil => exact False.elim (hRelation symbol hDomain)
    | cons sort rest =>
      rw [hDomain] at arguments
      cases arguments with
      | cons first _ => exact False.elim (no_closed_term hFunction first)
  | equal left _ => exact False.elim (no_closed_term hFunction left)
  | neg body =>
    have hBody : Formula.IsDelta0 ℬ body := by cases hDelta; assumption
    rcases closed_decided ℬ hFunction hRelation T body hBody with h | h
    · exact Or.inr (by derive_prop)
    · exact Or.inl h
  | conj left right =>
    have hLeft : Formula.IsDelta0 ℬ left := by cases hDelta; assumption
    have hRight : Formula.IsDelta0 ℬ right := by cases hDelta; assumption
    rcases closed_decided ℬ hFunction hRelation T left hLeft with hLeft | hLeft
    · rcases closed_decided ℬ hFunction hRelation T right hRight with hRight | hRight
      · exact Or.inl (.conj_intro hLeft hRight)
      · exact Or.inr (by derive_prop)
    · exact Or.inr (by derive_prop)
  | disj left right =>
    have hLeft : Formula.IsDelta0 ℬ left := by cases hDelta; assumption
    have hRight : Formula.IsDelta0 ℬ right := by cases hDelta; assumption
    rcases closed_decided ℬ hFunction hRelation T left hLeft with hLeft | hLeft
    · exact Or.inl (by derive_prop)
    · rcases closed_decided ℬ hFunction hRelation T right hRight with hRight | hRight
      · exact Or.inl (by derive_prop)
      · exact Or.inr (by derive_prop)
  | imp left right =>
    have hLeft : Formula.IsDelta0 ℬ left := by cases hDelta; assumption
    have hRight : Formula.IsDelta0 ℬ right := by cases hDelta; assumption
    rcases closed_decided ℬ hFunction hRelation T left hLeft with hLeft | hLeft
    · rcases closed_decided ℬ hFunction hRelation T right hRight with hRight | hRight
      · exact Or.inl (by derive_prop)
      · exact Or.inr (by derive_prop)
    · exact Or.inl (by derive_prop)
  | iff left right =>
    have hLeft : Formula.IsDelta0 ℬ left := by cases hDelta; assumption
    have hRight : Formula.IsDelta0 ℬ right := by cases hDelta; assumption
    rcases closed_decided ℬ hFunction hRelation T left hLeft with hLeft | hLeft
    · rcases closed_decided ℬ hFunction hRelation T right hRight with hRight | hRight
      · exact Or.inl (by derive_prop)
      · exact Or.inr (by derive_prop)
    · rcases closed_decided ℬ hFunction hRelation T right hRight with hRight | hRight
      · exact Or.inr (by derive_prop)
      · exact Or.inl (by derive_prop)
  | forallE sort body => exact False.elim (forall_not_delta0 ℬ hFunction sort body hDelta)
  | existsE sort body => exact False.elim (exists_not_delta0 ℬ hFunction sort body hDelta)
termination_by sizeOf formula

end YesMetaZFC.Automation.FunctionFreeDelta0
