import YesMetaZFC.Logic.Arithmetic.FiniteRange
import YesMetaZFC.Model.FirstOrder.SubstitutionSemantics

/-! # 有限值域模板的参数与语义对应 -/
namespace YesMetaZFC.Model.Arithmetic.FiniteRange
open Logic FirstOrder
set_option autoImplicit false
universe u v w z
variable {σ : Signature.{u, v, w}} {s : σ.SortSymbol} {Δ : SortContext σ}
variable {ℳ : Structure.{u, v, w, z} σ}

theorem insert_sat_m (φ : OpenFormula σ (s :: s :: Δ)) (η : Env ℳ [] Δ)
    (n i a : ℳ.Carrier s) :
    (Logic.Arithmetic.FiniteRange.insert_m φ).satisfies (((η.pushFree n).pushFree i).pushFree a) ↔
      φ.satisfies ((η.pushFree i).pushFree a) := by
  unfold Logic.Arithmetic.FiniteRange.insert_m Formula.renameFree
  rw [Formula.satisfies_rename]
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro t v; cases v
  · intro t v; cases v with
    | here => rfl
    | there v => cases v <;> rfl

theorem bound_sat_m (φ : OpenFormula σ (s :: s :: Δ)) (η : Env ℳ [] Δ) (n : ℳ.Carrier s)
    (L : ∀ {Θ : SortContext σ}, Term σ [] Θ s → Term σ [] Θ s → OpenFormula σ Θ)
    (R : ℳ.Carrier s → ℳ.Carrier s → Prop)
    (hL : ∀ (η : Env ℳ [] (s :: s :: s :: s :: Δ)) (t u : Term σ [] (s :: s :: s :: s :: Δ) s),
      (L t u).satisfies η ↔ R (t.eval η) (u.eval η)) :
    (Logic.Arithmetic.FiniteRange.bound_m φ L).satisfies (η.pushFree n) ↔
      ∃ b, ∀ i a, R i n → φ.satisfies ((η.pushFree i).pushFree a) → R a b := by
  simp only [Logic.Arithmetic.FiniteRange.bound_m, Formula.satisfies_existsFreeTop,
    Formula.satisfies_forallFreeTop, Formula.satisfies, hL, insert_sat_m]
  rfl

theorem function_sat_m (φ : OpenFormula σ (s :: Δ)) (η : Env ℳ [] Δ) :
    (Logic.Arithmetic.FiniteRange.function_m φ).satisfies η ↔
      ∃ a, φ.satisfies (η.pushFree a) ∧ ∀ c, φ.satisfies (η.pushFree c) → c = a := by
  have h (a c : ℳ.Carrier s) :
      (φ.renameFree (VariableRenaming.lift (VariableRenaming.weaken s))).satisfies
        ((η.pushFree a).pushFree c) ↔ φ.satisfies (η.pushFree c) := by
    unfold Formula.renameFree
    rw [Formula.satisfies_rename]
    apply Iff.of_eq
    apply congrArg (fun η => φ.satisfies η)
    apply Env.ext
    · intro t v; cases v
    · intro t v; cases v <;> rfl
  simp only [Logic.Arithmetic.FiniteRange.function_m, Formula.satisfies_existsFreeTop,
    Formula.satisfies, Formula.satisfies_forallFreeTop, h]
  rfl

theorem segment_sat_m (φ : OpenFormula σ (s :: s :: Δ)) (η : Env ℳ [] Δ) (n : ℳ.Carrier s)
    (L : ∀ {Θ : SortContext σ}, Term σ [] Θ s → Term σ [] Θ s → OpenFormula σ Θ)
    (R : ℳ.Carrier s → ℳ.Carrier s → Prop)
    (hL : ∀ (η : Env ℳ [] (s :: s :: Δ)) (t u : Term σ [] (s :: s :: Δ) s),
      (L t u).satisfies η ↔ R (t.eval η) (u.eval η)) :
    (Logic.Arithmetic.FiniteRange.segment_m φ L).satisfies (η.pushFree n) ↔
      ∀ i, R i n → ∃ a, φ.satisfies ((η.pushFree i).pushFree a) ∧
        ∀ c, φ.satisfies ((η.pushFree i).pushFree c) → c = a := by
  simp only [Logic.Arithmetic.FiniteRange.segment_m, Formula.satisfies_forallFreeTop,
    Formula.satisfies, hL, function_sat_m, insert_sat_m]
  rfl

end YesMetaZFC.Model.Arithmetic.FiniteRange
