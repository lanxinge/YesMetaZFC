import YesMetaZFC.Model.Arithmetic.PrimitiveRecursive.Totality
import YesMetaZFC.Model.Arithmetic.Z2.Reduct

/-! # Z₂ 内部的原始递归全函数图

集合见证来自原模型的理解公理。配对码显式量化，不选择模型数或内部集合。
-/
namespace YesMetaZFC.Model.Arithmetic.Z2.PrimitiveRecursive
open Logic FirstOrder Logic.Arithmetic.Z2
open Logic.Arithmetic.PrimitiveRecursive
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}
variable (hZ₂ : Theory.Models ℳ theory_m)
include hZ₂

theorem graph_m (c : code_m) : ∃ X : set_l ℳ, ∀ x y p : num_l ℳ,
    Arithmetic.Pairing.graph_l (ℳ := reduct_m ℳ) x y p →
      (mem_l p X ↔ Arithmetic.PrimitiveRecursive.relation_l (ℳ := reduct_m ℳ) c x y) := by
  let φ : OpenFormula Logic.Arithmetic.signature_m [.num] :=
    .existsE .num (.existsE .num (.conj
      (Logic.Arithmetic.Pairing.graph_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))
      (Logic.Arithmetic.PrimitiveRecursive.graph_m c (.bvar (.there .here)) (.bvar .here))))
  obtain ⟨X, hX⟩ := comprehension_m hZ₂ (Logic.Arithmetic.PA.Translation.formula_m φ) Env.empty
  have hφ (p : num_l ℳ) : (Logic.Arithmetic.PA.Translation.formula_m φ).satisfies (Env.empty.pushFree p) ↔
      ∃ x y, Arithmetic.Pairing.graph_l (ℳ := reduct_m ℳ) x y p ∧
        Arithmetic.PrimitiveRecursive.relation_l (ℳ := reduct_m ℳ) c x y := by
    refine (formula_sat_m (Γ := []) (Δ := [Logic.Arithmetic.sort_m.num]) (Env.empty.pushFree p) φ).trans ?_
    simp only [φ, Formula.satisfies, Arithmetic.Pairing.graph_sat_m,
      Arithmetic.PrimitiveRecursive.graph_sat_m]
    rfl
  refine ⟨X, ?_⟩
  intro x y p hp
  rw [hX, hφ]
  constructor
  · rintro ⟨a, b, h, hc⟩
    obtain ⟨rfl, rfl⟩ := Arithmetic.PA.Pairing.injective_m (reduct_models_m hZ₂) a b x y h hp
    exact hc
  · intro h; exact ⟨x, y, hp, h⟩

theorem function_m (c : code_m) : ∃ X : set_l ℳ,
    (∀ x y p : num_l ℳ, Arithmetic.Pairing.graph_l (ℳ := reduct_m ℳ) x y p →
      (mem_l p X ↔ Arithmetic.PrimitiveRecursive.relation_l (ℳ := reduct_m ℳ) c x y)) ∧
    ∀ x : num_l ℳ, ∃ y p : num_l ℳ,
      Arithmetic.Pairing.graph_l (ℳ := reduct_m ℳ) x y p ∧ mem_l p X ∧
      ∀ z q : num_l ℳ, Arithmetic.Pairing.graph_l (ℳ := reduct_m ℳ) x z q → mem_l q X → z = y := by
  obtain ⟨X, hX⟩ := graph_m hZ₂ c
  refine ⟨X, hX, ?_⟩
  intro x
  obtain ⟨y, hy, h⟩ := Arithmetic.PrimitiveRecursive.exists_unique_m (reduct_models_m hZ₂) c x
  obtain ⟨p, hp⟩ := Arithmetic.Pairing.total_m (ℳ := reduct_m ℳ) x y
  exact ⟨y, p, hp, (hX x y p hp).mpr hy, fun z q hq hz => h z ((hX x z q hq).mp hz)⟩

theorem unique_m (c : code_m) {X Y : set_l ℳ}
    (hX : ∀ x y p, Arithmetic.Pairing.graph_l (ℳ := reduct_m ℳ) x y p →
      (mem_l p X ↔ Arithmetic.PrimitiveRecursive.relation_l (ℳ := reduct_m ℳ) c x y))
    (hY : ∀ x y p, Arithmetic.Pairing.graph_l (ℳ := reduct_m ℳ) x y p →
      (mem_l p Y ↔ Arithmetic.PrimitiveRecursive.relation_l (ℳ := reduct_m ℳ) c x y)) : X = Y := by
  apply (ext_m hZ₂ X Y).mpr
  intro p
  obtain ⟨x, y, hp⟩ := Arithmetic.PA.Pairing.surjective_m (reduct_models_m hZ₂) p
  exact (hX x y p hp).trans (hY x y p hp).symm

end YesMetaZFC.Model.Arithmetic.Z2.PrimitiveRecursive
