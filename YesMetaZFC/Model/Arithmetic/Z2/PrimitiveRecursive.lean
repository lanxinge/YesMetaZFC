import YesMetaZFC.Model.Arithmetic.PrimitiveRecursive.Totality
import YesMetaZFC.Model.Arithmetic.Z2.Reduct

/-! # Z₂ 内部的原始递归全函数图

集合见证来自原模型集域中的理解公理，不把该集域替换为宿主幂集。
程序固定在外部，输入输出遍历整个内部数域。
-/
namespace YesMetaZFC.Model.Arithmetic.Z2.PrimitiveRecursive
open Logic FirstOrder Logic.Arithmetic.Z2
open Logic.Arithmetic.PrimitiveRecursive
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}
variable (hZ₂ : Theory.Models ℳ theory_m)
include hZ₂

theorem graph_m (c : code_m) : ∃ X : set_l ℳ, ∀ x y : num_l ℳ,
    mem_l (Arithmetic.Pairing.value_l (ℳ := reduct_m ℳ) x y) X ↔
      Arithmetic.PrimitiveRecursive.relation_l (ℳ := reduct_m ℳ) c x y := by
  let φ : OpenFormula Logic.Arithmetic.signature_m [.num] :=
    .existsE .num (.existsE .num (.conj
      (Logic.Arithmetic.Pairing.graph_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))
      (Logic.Arithmetic.PrimitiveRecursive.graph_m c (.bvar (.there .here)) (.bvar .here))))
  obtain ⟨X, hX⟩ := comprehension_m hZ₂ (Logic.Arithmetic.PA.Translation.formula_m φ) Env.empty
  have hφ (p : num_l ℳ) : (Logic.Arithmetic.PA.Translation.formula_m φ).satisfies (Env.empty.pushFree p) ↔
      ∃ x y, Arithmetic.Pairing.value_l (ℳ := reduct_m ℳ) x y = p ∧
        Arithmetic.PrimitiveRecursive.relation_l (ℳ := reduct_m ℳ) c x y := by
    refine (formula_sat_m (Γ := []) (Δ := [Logic.Arithmetic.sort_m.num]) (Env.empty.pushFree p) φ).trans ?_
    simp only [φ, Formula.satisfies, Arithmetic.Pairing.graph_sat_m,
      Arithmetic.PrimitiveRecursive.graph_sat_m]
    rfl
  refine ⟨X, ?_⟩
  intro x y
  rw [hX, hφ]
  constructor
  · rintro ⟨a, b, h, hc⟩
    obtain ⟨rfl, rfl⟩ := Arithmetic.PA.Pairing.injective_m (reduct_models_m hZ₂) a b x y h
    exact hc
  · intro h; exact ⟨x, y, rfl, h⟩

theorem function_m (c : code_m) : ∃ X : set_l ℳ,
    (∀ x y : num_l ℳ, mem_l (Arithmetic.Pairing.value_l (ℳ := reduct_m ℳ) x y) X ↔
      Arithmetic.PrimitiveRecursive.relation_l (ℳ := reduct_m ℳ) c x y) ∧
    ∀ x : num_l ℳ, ∃ y : num_l ℳ, mem_l (Arithmetic.Pairing.value_l (ℳ := reduct_m ℳ) x y) X ∧
      ∀ z : num_l ℳ, mem_l (Arithmetic.Pairing.value_l (ℳ := reduct_m ℳ) x z) X → z = y := by
  obtain ⟨X, hX⟩ := graph_m hZ₂ c
  refine ⟨X, hX, ?_⟩
  intro x
  obtain ⟨y, hy, h⟩ := Arithmetic.PrimitiveRecursive.exists_unique_m (reduct_models_m hZ₂) c x
  exact ⟨y, (hX x y).mpr hy, fun z hz => h z ((hX x z).mp hz)⟩

theorem unique_m (c : code_m) {X Y : set_l ℳ}
    (hX : ∀ x y, mem_l (Arithmetic.Pairing.value_l (ℳ := reduct_m ℳ) x y) X ↔
      Arithmetic.PrimitiveRecursive.relation_l (ℳ := reduct_m ℳ) c x y)
    (hY : ∀ x y, mem_l (Arithmetic.Pairing.value_l (ℳ := reduct_m ℳ) x y) Y ↔
      Arithmetic.PrimitiveRecursive.relation_l (ℳ := reduct_m ℳ) c x y) : X = Y := by
  apply (ext_m hZ₂ X Y).mpr
  intro n
  obtain ⟨x, y, rfl⟩ := Arithmetic.PA.Pairing.surjective_m (reduct_models_m hZ₂) n
  exact (hX x y).trans (hY x y).symm

end YesMetaZFC.Model.Arithmetic.Z2.PrimitiveRecursive
