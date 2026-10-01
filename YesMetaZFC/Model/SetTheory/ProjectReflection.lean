import YesMetaZFC.Model.SetTheory.Countable
import YesMetaZFC.Model.SetTheory.ProjectElementary

/-! # 任意外延结构的带参数可数反射

有限指定对象先作为壳的生成参数，再直接使用原纯语言初等性。构造不要求源模型
外部良基、可数或标准，也不改变其 universe。
-/

namespace YesMetaZFC.SetTheory.Definitional.Project.FirstOrderSemantics
open Logic.FirstOrder
universe u

theorem countable_parameters_l (M : SetTheory.Structure.{u}) (hE : Extensional M) {n}
    (a : Fin n → M.Domain) : ∃ A : Substructure_m (model_l M), A.Elementary_m ∧
      (∀ i, A.carrier .set (a i)) ∧ Extensional (reduct A.structure_m) ∧
        ∃ e : Nat → (reduct A.structure_m).Domain, Function.Surjective e := by
  obtain ⟨d⟩ := M.nonempty
  let f (k : Nat) : M.Domain := if h : k < n then a ⟨k, h⟩ else d
  obtain ⟨A, hA, ha, e, he⟩ := SetTheory.countable_elementary_l (model_l M) f
  refine ⟨A, hA, ?_, ?_, e, he⟩
  · intro i
    simpa only [f, dif_pos i.isLt] using ha i.val
  · exact submodel_extensional_l A hA hE

/-- 有限原赋值的全部自由闭合公式及任意原理论，在同一个实际可数模型中反射。 -/
theorem countable_env_l (M : SetTheory.Structure.{u}) (hE : Extensional M) {n} (ρ : SetTheory.Env M n) :
    ∃ N : SetTheory.Structure.{u}, Extensional N ∧ (∀ T : SetTheory.Theory, N.Models T ↔ M.Models T) ∧
      ∃ η : SetTheory.Env N n,
        (∀ φ : Project.Formula 1 n, φ.FreeClosed → (Project.Formula.satisfies ρ φ ↔ Project.Formula.satisfies η φ)) ∧
        ∃ e : Nat → N.Domain, Function.Surjective e := by
  obtain ⟨A, hA, ha, hN, e, he⟩ := countable_parameters_l M hE ρ.bound
  let N := reduct A.structure_m
  let η : SetTheory.Env N n := ⟨fun i => ⟨ρ.bound i, ha i⟩, fun _ => e 0⟩
  refine ⟨N, hN, fun T => submodel_models_l A hA hE T, η, ?_, e, he⟩
  intro φ hφ
  have tr := submodel_formula_l A hA hE hN φ hφ η
  have hs := formula_correct (ℳ := model_l M) hE φ hφ (native_env_l (ℳ := model_l M) ρ) ρ.free
  have ht := formula_correct (ℳ := model_l M) hE φ hφ (native_env_l (submodel_env_l A η)) (submodel_env_l A η).free
  have heq : native_env_l (submodel_env_l A η) = native_env_l (ℳ := model_l M) ρ := rfl
  rw [project_native_l (ℳ := model_l M) ρ] at hs
  rw [project_native_l (submodel_env_l A η)] at ht
  rw [heq] at ht
  exact hs.symm.trans (ht.trans tr.symm)

/-- 可数模型中的原公式后果反射到任意模型；指定理论随同有限参数一起保持。 -/
theorem countable_consequence_l {Γ : SetTheory.Theory} {n} (φ ψ : Project.Formula 1 n)
    (hφ : φ.FreeClosed) (hψ : ψ.FreeClosed)
    (valid : ∀ N : SetTheory.Structure.{u}, N.Models Γ → ∀ e : Nat → N.Domain,
      Function.Surjective e → ∀ η : SetTheory.Env N n, Project.Formula.satisfies η φ →
        Project.Formula.satisfies η ψ)
    {M : SetTheory.Structure.{u}} (hM : M.Models Γ) (ρ : SetTheory.Env M n)
    (h : Project.Formula.satisfies ρ φ) : Project.Formula.satisfies ρ ψ := by
  obtain ⟨N, _, hTheory, η, tr, e, he⟩ := countable_env_l M hM.1 ρ
  exact (tr ψ hψ).mpr (valid N ((hTheory Γ).mpr hM) e he η ((tr φ hφ).mp h))

end YesMetaZFC.SetTheory.Definitional.Project.FirstOrderSemantics
