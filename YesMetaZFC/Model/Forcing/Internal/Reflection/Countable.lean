import YesMetaZFC.Model.Forcing.TwoStep.Basic
import YesMetaZFC.Model.Forcing.Internal.Extension.Generic
import YesMetaZFC.Model.SetTheory.ProjectReflection

/-! # 任意地模型的力迫公式可数反射

初等子模型同时包含偏序、条件与全部名称参数，故原内部力迫公式逐式反射。
可数性只属于构造出的子模型，不加入原地模型的调用前提。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

/-- 同时反射原偏序、正条件、名称赋值和全部原公式的力迫关系。 -/
theorem countable_forcing_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {n p}
    (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i)) (hp : M.mem p B) (hz : p ≠ z) :
    ∃ N : SetTheory.Structure.{u}, ∃ B' R' z' p' : N.Domain, ∃ η : Env N n,
      N.Models ZF ∧ (∀ T : SetTheory.Theory, M.Models T → N.Models T) ∧
        N.mem p' B' ∧ p' ≠ z' ∧ Cond_order_d N B' R' z' ∧
        (∀ t : Term n, Name_d N B' (t.eval η)) ∧
        (∀ φ : Formula 1 n, φ.FreeClosed → (Forces_d M B R z φ ρ p ↔ Forces_d N B' R' z' φ η p')) ∧
        ∃ e : Nat → N.Domain, Function.Surjective e := by
  let σ := fenv_l ρ B R z p
  obtain ⟨A, hA, ha, hE, e, he⟩ := FirstOrderSemantics.countable_parameters_l M hZF.1 σ.bound
  let N := FirstOrderSemantics.reduct A.structure_m
  have theory (T : SetTheory.Theory) (hM : M.Models T) : N.Models T :=
    (FirstOrderSemantics.submodel_models_l A hA hZF.1 T).mpr hM
  have hN := theory ZF hZF
  let a (i : Fin (n+4)) : N.Domain := ⟨σ.bound i, ha i⟩
  let B' := a ⟨3, by omega⟩
  let R' := a ⟨2, by omega⟩
  let z' := a ⟨1, by omega⟩
  let p' := a ⟨0, by omega⟩
  have hB : B'.val = B := rfl
  have hR : R'.val = R := rfl
  have hz' : z'.val = z := rfl
  have hp' : p'.val = p := rfl
  have tr {k} (φ : Formula 1 k) (hφ : φ.FreeClosed) (δ : Env N k) :=
    FirstOrderSemantics.submodel_formula_l A hA hZF.1 hE φ hφ δ
  have hn (s : N.Domain) : Name_d N B' s ↔ Name_d M B s.val := by
    let δ := (⟨fun _ => B', fun _ => B'⟩ : Env N 1).push s
    exact (name_sat_l N hN.1 δ (.bound 1) .newest).symm.trans
      ((tr _ (name_m_freeClosed _ _ rfl rfl) δ).trans
        (name_sat_l M hZF.1 (FirstOrderSemantics.submodel_env_l A δ) (.bound 1) .newest))
  let δ := ((⟨fun _ => B', fun _ => B'⟩ : Env N 1).push R').push z'
  have hO : Cond_order_d N B' R' z' :=
    (cond_order_sat_l hN.1 δ (.bound 2) (.bound 1) .newest).mp
      ((tr _ (cond_order_m_freeClosed _ _ _ rfl rfl rfl) δ).mpr
        ((cond_order_sat_l hZF.1 (FirstOrderSemantics.submodel_env_l A δ) _ _ _).mpr O))
  obtain ⟨t, ht⟩ := KP.exists_empty (ZF.modelsKP hN)
  have htN := name_empty_l N (KP.exists_pair (ZF.modelsKP hN)) B' t ht
  let η : Env N n := ⟨fun i => a (param_shift_l i), fun _ => t⟩
  have hη i : (η.bound i).val = ρ.bound i := by
    change (fenv_l ρ B R z p).bound (param_shift_l i) = ρ.bound i
    exact congrArg (fun ξ : Env M n => ξ.bound i) (fenv_param_l M ρ B R z p)
  have hηN : ∀ s : Term n, Name_d N B' (s.eval η) := by
    intro s
    cases s with
    | free _ => exact htN
    | bound i => exact (hn (η.bound i)).mpr ((hη i).symm ▸ hρ i)
  refine ⟨N, B', R', z', p', η, hN, theory, hp, ?_, hO, hηN, ?_, e, he⟩
  · exact fun h => hz (congrArg (fun s : N.Domain => s.val) h)
  · intro φ hφ
    have h := tr (force_code_m φ) (force_code_closed_l φ hφ) (fenv_l η B' R' z' p')
    have hc : Forces_d N B' R' z' φ η p' ↔
        Forces_d M B R z φ (FirstOrderSemantics.submodel_env_l A η) p := by
      simpa only [Forces_d, Code_d, fenv_l, FirstOrderSemantics.submodel_env_push_l, hB, hR, hz', hp'] using! h
    exact (hc.trans (forces_env_l (B := B) (R := R) (z := z) hZF.1 φ hφ
      (FirstOrderSemantics.submodel_env_l A η) ρ (fun i => hη i) p)).symm

end YesMetaZFC.Model.Forcing.Internal
