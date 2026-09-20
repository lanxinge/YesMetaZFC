import YesMetaZFC.Logic.Arithmetic.Z2.Induction
import YesMetaZFC.Model.Arithmetic.Z2.Structure
import YesMetaZFC.Model.Interpretation.ModelClosure
import YesMetaZFC.Model.FirstOrder.Soundness

/-! # 完整理解及公式归纳的任意模型语义

数域与集域均取模型的整个载体。新集合槽的语义与其值无关，
所以理解见证没有出现在原公式的参数中。
-/
namespace YesMetaZFC.Model.Arithmetic.Z2
open Logic FirstOrder Logic.Arithmetic.Z2
set_option autoImplicit false
universe u

variable {ℳ : Structure.{0, 0, 0, u} signature_m} {Δ : SortContext signature_m}

/-- 集合等同由模型内部的全数域成员关系判定，不假定集域就是外部幂集。 -/
theorem ext_m (hZ₂ : Theory.Models ℳ theory_m) (X Y : set_l ℳ) :
    X = Y ↔ ∀ n : num_l ℳ, mem_l n X ↔ mem_l n Y := by
  constructor
  · intro h; subst Y; exact fun _ => Iff.rfl
  · exact (hZ₂ _ axiom_m.extensionality) X Y

theorem insert_sat_m (φ : Formula signature_m [] (.num :: Δ)) (η : Env ℳ [] Δ)
    (X : set_l ℳ) (n : num_l ℳ) :
    Formula.satisfies ((η.pushFree X).pushFree n) (insert_m φ) ↔
      Formula.satisfies (η.pushFree n) φ := by
  unfold insert_m Formula.renameFree
  rw [Formula.satisfies_rename]
  apply Iff.of_eq
  apply congrArg (fun η => Formula.satisfies η φ)
  apply Env.ext
  · intro s v; cases v
  · intro s v; cases v <;> rfl

theorem comprehension_sat_m (φ : Formula signature_m [] (.num :: Δ)) (η : Env ℳ [] Δ) :
    Formula.satisfies η (comprehension_m φ) ↔
      ∃ X : set_l ℳ, ∀ n : num_l ℳ, mem_l n X ↔ Formula.satisfies (η.pushFree n) φ := by
  simp only [comprehension_m, Formula.satisfies_existsFreeTop,
    Formula.satisfies_forallFreeTop, Formula.satisfies, insert_sat_m]
  rfl

theorem comprehension_m (hZ₂ : Theory.Models ℳ theory_m)
    (φ : Formula signature_m [] (.num :: Δ)) (η : Env ℳ [] Δ) :
    ∃ X : set_l ℳ, ∀ n : num_l ℳ, mem_l n X ↔ Formula.satisfies (η.pushFree n) φ := by
  have h := (Automation.ModelClosure.forall_close_iff
    (Logic.Arithmetic.Z2.comprehension_m φ)).mp (hZ₂ _ (axiom_m.comprehension φ)) η
  exact (comprehension_sat_m φ η).mp h

theorem next_sat_m (φ : Formula signature_m [] (.num :: Δ)) (η : Env ℳ [] Δ) (n : num_l ℳ) :
    Formula.satisfies (η.pushFree n) (φ.substituteFree next_m) ↔
      Formula.satisfies (η.pushFree (succ_l n)) φ := by
  rw [Formula.satisfies_substituteFree]
  apply Iff.of_eq
  apply congrArg (fun η => Formula.satisfies η φ)
  apply Env.ext
  · intro s v; cases v
  · intro s v; cases v <;> rfl

theorem induction_sat_m (φ : Formula signature_m [] (.num :: Δ)) (η : Env ℳ [] Δ) :
    Formula.satisfies η (induction_m φ) ↔
      ((Formula.satisfies (η.pushFree (zero_l ℳ)) φ ∧
        ∀ n, Formula.satisfies (η.pushFree n) φ →
          Formula.satisfies (η.pushFree (succ_l n)) φ) →
        ∀ n, Formula.satisfies (η.pushFree n) φ) := by
  simp only [induction_m, Formula.satisfies, Formula.satisfies_instantiateFreeTop,
    Formula.satisfies_forallFreeTop, next_sat_m]
  rfl

theorem induction_m (hZ₂ : Theory.Models ℳ theory_m)
    (φ : Formula signature_m [] (.num :: Δ)) (η : Env ℳ [] Δ)
    (h₀ : Formula.satisfies (η.pushFree (zero_l ℳ)) φ)
    (h₁ : ∀ n, Formula.satisfies (η.pushFree n) φ →
      Formula.satisfies (η.pushFree (succ_l n)) φ) :
    ∀ n, Formula.satisfies (η.pushFree n) φ := by
  have h := (induction_derives_m (Γ := []) (fun h => h) φ).sound hZ₂ η
    (by intro ψ hψ; cases hψ)
  exact (induction_sat_m φ η).mp h ⟨h₀, h₁⟩

/-- 只有具有给定对象公式定义的宿主谓词才能使用此归纳接口。 -/
theorem induct_m (hZ₂ : Theory.Models ℳ theory_m)
    (φ : Formula signature_m [] (.num :: Δ)) (η : Env ℳ [] Δ) (P : num_l ℳ → Prop)
    (hP : ∀ n, Formula.satisfies (η.pushFree n) φ ↔ P n)
    (h₀ : P (zero_l ℳ)) (h₁ : ∀ n, P n → P (succ_l n)) : ∀ n, P n := by
  have h := induction_m hZ₂ φ η ((hP _).mpr h₀)
    (fun n hn => (hP _).mpr (h₁ n ((hP n).mp hn)))
  exact fun n => (hP n).mp (h n)

end YesMetaZFC.Model.Arithmetic.Z2
