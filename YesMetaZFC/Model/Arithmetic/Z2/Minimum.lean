import YesMetaZFC.Model.Arithmetic.Z2.Order
import YesMetaZFC.Model.Arithmetic.PA.Minimum

/-! # Z₂ 模型中的混合参数可定义最小元

公式允许数／集量词和任意有限混合参数。共享的最小化论证只消费
PA 数域约化的序规律；本模块另外给出实际 Z₂ 公式所需的归纳实例。
-/
namespace YesMetaZFC.Model.Arithmetic.Z2
open Logic FirstOrder Logic.Arithmetic.Z2
set_option autoImplicit false
universe u

variable {ℳ : Structure.{0, 0, 0, u} signature_m}

theorem minimum_m (hZ₂ : Theory.Models ℳ theory_m)
    {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ)) (η : Env ℳ [] Δ)
    (hφ : ∃ n : num_l ℳ, φ.satisfies (η.pushFree n)) :
    ∃ n : num_l ℳ, φ.satisfies (η.pushFree n) ∧
      ∀ m : num_l ℳ, lt_l m n → ¬φ.satisfies (η.pushFree m) := by
  apply Arithmetic.PA.minimum_rule_m (reduct_models_m hZ₂)
    (fun n => φ.satisfies (η.pushFree n)) ?_ hφ
  intro h₀ h₁
  let χ := φ.renameFree (VariableRenaming.lift (VariableRenaming.weaken sort_m.num))
  let ψ : Formula signature_m [] (.num :: Δ) :=
    (Formula.imp (le_m (.fvar .here) (.fvar (.there .here))) (.neg χ)).forallFreeTop sort_m.num
  have hχ (n m : num_l ℳ) : χ.satisfies ((η.pushFree n).pushFree m) ↔
      φ.satisfies (η.pushFree m) := by
    unfold χ Formula.renameFree
    rw [Formula.satisfies_rename]
    apply Iff.of_eq
    apply congrArg (fun η => φ.satisfies η)
    apply Env.ext
    · intro s v; cases v
    · intro s v; cases v <;> rfl
  have hψ (n : num_l ℳ) : ψ.satisfies (η.pushFree n) ↔
      ∀ m : num_l ℳ, le_l m n → ¬φ.satisfies (η.pushFree m) := by
    simp only [ψ, Formula.satisfies_forallFreeTop, Formula.satisfies, le_sat_m, hχ]
    rfl
  exact induct_m hZ₂ ψ η (fun n => ∀ m, le_l m n → ¬φ.satisfies (η.pushFree m)) hψ h₀ h₁

/-- 非空内部数集的最小元；不把集域等同于外部幂集。 -/
theorem minimum_set_m (hZ₂ : Theory.Models ℳ theory_m) (X : set_l ℳ)
    (hX : ∃ n, mem_l n X) : ∃ n, mem_l n X ∧ ∀ m, lt_l m n → ¬mem_l m X :=
  minimum_m hZ₂ (mem_m (.fvar .here) (.fvar (.there .here))) (Env.empty.pushFree X) hX

end YesMetaZFC.Model.Arithmetic.Z2
