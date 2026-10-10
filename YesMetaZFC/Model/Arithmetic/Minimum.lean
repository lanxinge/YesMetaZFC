import YesMetaZFC.Logic.Arithmetic.Minimum
import YesMetaZFC.Model.FirstOrder.SubstitutionSemantics

/-! # 最小元模板的逐公式语义

新比较变量插在候选前，原参数不变；本层不要求任何算术模型公理。
-/
namespace YesMetaZFC.Model.Arithmetic.Minimum
open Logic FirstOrder
set_option autoImplicit false
universe u v w z

theorem candidate_sat_m {σ : Signature.{u, v, w}} {s : σ.SortSymbol}
    {Δ : SortContext σ} {ℳ : Structure.{u, v, w, z} σ}
    (η : Env ℳ [] Δ) (n : ℳ.Carrier s)
    (φ : OpenFormula σ (s :: Δ)) (R : OpenFormula σ (s :: s :: Δ)) :
    (Logic.Arithmetic.Minimum.candidate_m φ R).satisfies (η.pushFree n) ↔
      φ.satisfies (η.pushFree n) ∧ ∀ m, R.satisfies ((η.pushFree n).pushFree m) →
        ¬φ.satisfies (η.pushFree m) := by
  have h (m : ℳ.Carrier s) :
      (φ.renameFree (VariableRenaming.lift (VariableRenaming.weaken s))).satisfies
        ((η.pushFree n).pushFree m) ↔ φ.satisfies (η.pushFree m) := by
    unfold Formula.renameFree
    rw [Formula.satisfies_rename]
    apply Iff.of_eq
    apply congrArg (fun η => φ.satisfies η)
    apply Env.ext
    · intro t v; cases v
    · intro t v; cases v <;> rfl
  simp only [Logic.Arithmetic.Minimum.candidate_m, Formula.satisfies,
    Formula.satisfies_forallFreeTop, h]

end YesMetaZFC.Model.Arithmetic.Minimum
