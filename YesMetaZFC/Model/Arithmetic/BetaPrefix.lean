import YesMetaZFC.Logic.Arithmetic.BetaPrefix
import YesMetaZFC.Model.Arithmetic.FiniteRange

/-! # 前缀模板的逐参数语义

排序、原参数及关系解释全部显式；适用于 PA 数参数和 Z₂ 混合参数。
-/
namespace YesMetaZFC.Model.Arithmetic.Beta
open Logic FirstOrder
set_option autoImplicit false
universe u v w z
variable {σ : Signature.{u, v, w}} {s : σ.SortSymbol} {Δ : SortContext σ}
variable {ℳ : Structure.{u, v, w, z} σ}

theorem prefix_sat_m (φ : OpenFormula σ (s :: s :: Δ)) (η : Env ℳ [] Δ)
    (n c j : ℳ.Carrier s)
    (L E : ∀ {Θ}, Term σ [] Θ s → Term σ [] Θ s → OpenFormula σ Θ)
    (D V : ∀ {Θ}, Term σ [] Θ s → Term σ [] Θ s → Term σ [] Θ s → OpenFormula σ Θ)
    (R : ∀ {Θ}, Term σ [] Θ s → Term σ [] Θ s → Term σ [] Θ s → Term σ [] Θ s → OpenFormula σ Θ)
    (l e : ℳ.Carrier s → ℳ.Carrier s → Prop)
    (d v : ℳ.Carrier s → ℳ.Carrier s → ℳ.Carrier s → Prop)
    (r : ℳ.Carrier s → ℳ.Carrier s → ℳ.Carrier s → ℳ.Carrier s → Prop)
    (hL : ∀ {Θ} (η : Env ℳ [] Θ) (a b), (L a b).satisfies η ↔ l (a.eval η) (b.eval η))
    (hE : ∀ {Θ} (η : Env ℳ [] Θ) (a b), (E a b).satisfies η ↔ e (a.eval η) (b.eval η))
    (hD : ∀ {Θ} (η : Env ℳ [] Θ) (a b c), (D a b c).satisfies η ↔ d (a.eval η) (b.eval η) (c.eval η))
    (hV : ∀ {Θ} (η : Env ℳ [] Θ) (a b c), (V a b c).satisfies η ↔ v (a.eval η) (b.eval η) (c.eval η))
    (hR : ∀ {Θ} (η : Env ℳ [] Θ) (a b c d), (R a b c d).satisfies η ↔ r (a.eval η) (b.eval η) (c.eval η) (d.eval η)) :
    (Logic.Arithmetic.Beta.prefix_m φ L E D V R).satisfies (((η.pushFree c).pushFree n).pushFree j) ↔
      ∃ b M, (∀ i, l i j → d c i M) ∧ (∀ i, l i n → e j i → v c i M) ∧
        ∀ i, l i j → ∀ a, φ.satisfies ((η.pushFree i).pushFree a) → r b c i a := by
  simp only [Logic.Arithmetic.Beta.prefix_m, Formula.satisfies_existsFreeTop,
    Formula.satisfies_forallFreeTop, Formula.satisfies, hL, hE, hD, hV, hR, FiniteRange.insert_sat_m]
  apply exists_congr
  intro b
  apply exists_congr
  intro M
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  constructor
  · intro h i hi a
    exact h i a hi
  · intro h i a hi
    exact h i hi a

end YesMetaZFC.Model.Arithmetic.Beta
