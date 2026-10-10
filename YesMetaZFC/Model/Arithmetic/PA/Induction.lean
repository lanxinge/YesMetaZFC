import YesMetaZFC.Logic.Arithmetic.PA.Axioms
import YesMetaZFC.Model.Arithmetic.Structure
import YesMetaZFC.Model.Interpretation.ModelClosure

/-! # PA 归纳模式的精确模型语义

量词遍历模型的整个数域，包括可能的非标准数。只有实际公式及其参数环境
能够进入归纳；最后的宿主谓词接口仍要求同一公式的逐点语义对应。
-/
namespace YesMetaZFC.Model.Arithmetic
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u

variable {ℳ : Structure.{0, 0, 0, u} signature_m} {Δ : SortContext signature_m}

theorem next_sat_m (φ : Formula signature_m [] (.num :: Δ))
    (η : Env ℳ [] Δ) (n : num_l ℳ) :
    Formula.satisfies (η.pushFree n) (φ.substituteFree PA.next_m) ↔
      Formula.satisfies (η.pushFree (succ_l n)) φ := by
  rw [Formula.satisfies_substituteFree]
  apply Iff.of_eq
  apply congrArg (fun η => Formula.satisfies η φ)
  apply Env.ext
  · intro s v; cases v
  · intro s v; cases v <;> rfl

/-- 归纳公式恰好表达基例、全数域后继闭包与全数域结论。 -/
theorem induction_sat_m (φ : Formula signature_m [] (.num :: Δ)) (η : Env ℳ [] Δ) :
    Formula.satisfies η (PA.induction_m φ) ↔
      ((Formula.satisfies (η.pushFree (zero_l ℳ)) φ ∧
        ∀ n, Formula.satisfies (η.pushFree n) φ →
          Formula.satisfies (η.pushFree (succ_l n)) φ) →
        ∀ n, Formula.satisfies (η.pushFree n) φ) := by
  simp only [PA.induction_m, Formula.satisfies, Formula.satisfies_instantiateFreeTop,
    Formula.satisfies_forallFreeTop, next_sat_m]
  rfl

theorem induction_m (hPA : Theory.Models ℳ PA.theory_m)
    (φ : Formula signature_m [] (.num :: Δ)) (η : Env ℳ [] Δ)
    (h₀ : Formula.satisfies (η.pushFree (zero_l ℳ)) φ)
    (h₁ : ∀ n, Formula.satisfies (η.pushFree n) φ →
      Formula.satisfies (η.pushFree (succ_l n)) φ) :
    ∀ n, Formula.satisfies (η.pushFree n) φ := by
  have h := (Automation.ModelClosure.forall_close_iff (PA.induction_m φ)).mp
    (hPA _ (PA.axiom_m.induction φ)) η
  exact (induction_sat_m φ η).mp h ⟨h₀, h₁⟩

/-- 参数 P 是语义缩写，不是任意外部谓词归纳公理。 -/
theorem induct_m (hPA : Theory.Models ℳ PA.theory_m)
    (φ : Formula signature_m [] (.num :: Δ)) (η : Env ℳ [] Δ) (P : num_l ℳ → Prop)
    (hP : ∀ n, Formula.satisfies (η.pushFree n) φ ↔ P n)
    (h₀ : P (zero_l ℳ)) (h₁ : ∀ n, P n → P (succ_l n)) : ∀ n, P n := by
  have h := induction_m hPA φ η ((hP _).mpr h₀)
    (fun n hn => (hP _).mpr (h₁ n ((hP n).mp hn)))
  exact fun n => (hP n).mp (h n)

end YesMetaZFC.Model.Arithmetic
