import YesMetaZFC.Logic.Arithmetic.Sequence
import YesMetaZFC.Model.Arithmetic.FiniteRange

/-! # 有限图编码模板的语义 -/
namespace YesMetaZFC.Model.Arithmetic.Sequence
open Logic FirstOrder
set_option autoImplicit false
universe u v w z
variable {σ : Signature.{u, v, w}} {s : σ.SortSymbol} {Δ : SortContext σ}
variable {ℳ : Structure.{u, v, w, z} σ}

theorem code_sat_m (φ : OpenFormula σ (s :: s :: Δ)) (η : Env ℳ [] Δ) (n : ℳ.Carrier s)
    (L : ∀ {Θ}, Term σ [] Θ s → Term σ [] Θ s → OpenFormula σ Θ)
    (G : ∀ {Θ}, Term σ [] Θ s → Term σ [] Θ s → Term σ [] Θ s → Term σ [] Θ s → OpenFormula σ Θ)
    (l : ℳ.Carrier s → ℳ.Carrier s → Prop)
    (g : ℳ.Carrier s → ℳ.Carrier s → ℳ.Carrier s → ℳ.Carrier s → Prop)
    (hL : ∀ {Θ} (η : Env ℳ [] Θ) (a b), (L a b).satisfies η ↔ l (a.eval η) (b.eval η))
    (hG : ∀ {Θ} (η : Env ℳ [] Θ) (a b c d), (G a b c d).satisfies η ↔ g (a.eval η) (b.eval η) (c.eval η) (d.eval η)) :
    (Logic.Arithmetic.Sequence.code_m φ L G).satisfies (η.pushFree n) ↔
      ∃ b c, ∀ i, l i n → ∀ a, g b c i a ↔ φ.satisfies ((η.pushFree i).pushFree a) := by
  simp only [Logic.Arithmetic.Sequence.code_m, Formula.satisfies_existsFreeTop,
    Formula.satisfies_forallFreeTop, Formula.satisfies, hL, hG, FiniteRange.insert_sat_m]
  apply exists_congr
  intro b
  apply exists_congr
  intro c
  constructor
  · intro h i hi a
    exact h i a hi
  · intro h i a hi
    exact h i hi a

end YesMetaZFC.Model.Arithmetic.Sequence
