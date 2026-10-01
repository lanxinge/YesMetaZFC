import YesMetaZFC.Model.Forcing.TwoStep.Proper.Selection

/-! # 任意地模型中的二步主加强装配

反射完整的二步装配、properness 和给定条件，然后调用已经实现的名称选择。
反射回来的结论是原模型内实际存在的 N 与加强条件，不要求原模型外部可数、
良基或标准，也不把泛型的外部存在性作为调用参数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T t W C S : M.Domain}

/-- 给定可数种子和任意二步条件，自动构造包含种子的可数 N 及二步 N 主加强。 -/
theorem two_step_master_extension_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
    {ω E x} (hω : M.IsOmega ω)
    (hP : Proper_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R z)
    (hE : M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) E ω)
    (h : Two_step_d M B R z b A T W C S) (hW : Name_pool_d M B A t W)
    (L : Cond_order_d M C S C) (hT : Name_d M B T) (hx : M.mem x C)
    (hNext : Forces_d M B R z (proper_exists_m .newest (.bound 1)) (ord_env_l M A T) b) :
    ∃ N y, M.MemberSubset E N ∧ M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) N ω ∧
      Below_d M C S C y x ∧ Mstr_d M C S C N y := by
  let ρ₀ : Env M 7 := ((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push A).push T).push t
  let ρ : Env M 13 := (((((ρ₀.push W).push C).push S).push ω).push E).push x
  let es : Fin 2 → Term 13 := Fin.cases (.bound 8) (fun _ => .bound 7)
  let φ : Formula 1 13 :=
    .conj (cond_order_m (.bound 12) (.bound 11) (.bound 10))
    (.conj (Formula.isOmega (.bound 2))
    (.conj (proper_m (.bound 2) (.bound 12) (.bound 11) (.bound 10))
    (.conj (Formula.cardinalLessOrEqual kpair_convention_l (.bound 1) (.bound 2))
    (.conj (two_step_m (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7)
      (.bound 5) (.bound 4) (.bound 3))
    (.conj (name_pool_m (.bound 12) (.bound 8) (.bound 6) (.bound 5))
    (.conj (cond_order_m (.bound 4) (.bound 3) (.bound 4))
    (.conj (name_m (.bound 12) (.bound 7))
    (.conj (.mem .newest (.bound 4))
      (force_at_m (proper_exists_m .newest (.bound 1)) es (.bound 12) (.bound 11) (.bound 10) (.bound 9))))))))))
  let ψ : Formula 1 13 := .existsE (.existsE
    (.conj (Formula.subset (.bound 3) (.bound 1))
    (.conj (Formula.cardinalLessOrEqual kpair_convention_l (.bound 1) (.bound 4))
    (.conj (below_m (.bound 6) (.bound 5) (.bound 6) .newest (.bound 2))
      (mstr_m (.bound 6) (.bound 5) (.bound 6) (.bound 1) .newest)))))
  have hes : ∀ i, (es i).freeSupport = [] := Fin.cases rfl (fun _ => rfl)
  have hφ : φ.FreeClosed := by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed, hes]
  have hψ : ψ.FreeClosed := by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed]
  have fenv (K : SetTheory.Structure.{u}) (hK : Extensional K) (η : Env K 13) :
      Forces_d K (η.bound 12) (η.bound 11) (η.bound 10) (proper_exists_m .newest (.bound 1))
        ⟨fun i => (es i).eval η, η.free⟩ (η.bound 9) ↔
      Forces_d K (η.bound 12) (η.bound 11) (η.bound 10) (proper_exists_m .newest (.bound 1))
        (ord_env_l K (η.bound 8) (η.bound 7)) (η.bound 9) :=
    forces_env_l hK _ (proper_exists_m_freeClosed _ _ rfl rfl) _ _ (Fin.cases rfl (fun _ => rfl)) _
  have raw (K : SetTheory.Structure.{u}) (hK : K.Models ZFC) (η : Env K 13) :
      Formula.satisfies η φ ↔
      let I := kpair_interpretation_l K hK.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hK)))
      Cond_order_d K (η.bound 12) (η.bound 11) (η.bound 10) ∧ K.IsOmega (η.bound 2) ∧
      Proper_d I (η.bound 2) (η.bound 12) (η.bound 11) (η.bound 10) ∧
      K.CardinalLessOrEqual I (η.bound 1) (η.bound 2) ∧
      Two_step_d K (η.bound 12) (η.bound 11) (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 7)
        (η.bound 5) (η.bound 4) (η.bound 3) ∧
      Name_pool_d K (η.bound 12) (η.bound 8) (η.bound 6) (η.bound 5) ∧
      Cond_order_d K (η.bound 4) (η.bound 3) (η.bound 4) ∧ Name_d K (η.bound 12) (η.bound 7) ∧
      K.mem (η.bound 0) (η.bound 4) ∧
      Forces_d K (η.bound 12) (η.bound 11) (η.bound 10) (proper_exists_m .newest (.bound 1))
        (ord_env_l K (η.bound 8) (η.bound 7)) (η.bound 9) := by
    let I := kpair_interpretation_l K hK.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hK)))
    simp only [φ, Formula.satisfies_conj_iff, cond_order_sat_l hK.1, Formula.satisfies_isOmega_iff,
      proper_sat_l I hK.1, Formula.satisfies_cardinalLessOrEqual_iff I hK.1, two_step_sat_l hK.1,
      name_pool_sat_l K hK.1, name_sat_l K hK.1, Formula.satisfies_mem_iff, force_at_sat_l]
    iterate 9 apply and_congr Iff.rfl
    exact fenv K hK.1 η
  have result (K : SetTheory.Structure.{u}) (hK : K.Models ZFC) (η : Env K 13) :
      Formula.satisfies η ψ ↔
      let I := kpair_interpretation_l K hK.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hK)))
      ∃ N y, K.MemberSubset (η.bound 1) N ∧ K.CardinalLessOrEqual I N (η.bound 2) ∧
        Below_d K (η.bound 4) (η.bound 3) (η.bound 4) y (η.bound 0) ∧
        Mstr_d K (η.bound 4) (η.bound 3) (η.bound 4) N y := by
    let I := kpair_interpretation_l K hK.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hK)))
    simp only [ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
      Formula.satisfies_cardinalLessOrEqual_iff I hK.1, below_sat_l K hK.1, mstr_sat_l K hK.1]
    rfl
  apply (result M hZFC ρ).mp
  apply FirstOrderSemantics.countable_consequence_l (Γ := ZFC) φ ψ hφ hψ
    (fun K hK e he η hraw => ?_) hZFC ρ ((raw M hZFC ρ).mpr ⟨O, hω, hP, hE, h, hW, L, hT, hx, hNext⟩)
  obtain ⟨O', hω', hP', hE', h', hW', L', hT', hx', hNext'⟩ := (raw K hK η).mp hraw
  obtain ⟨p, s, hxp, _, hp, _⟩ := (h'.conditions _).mp hx'
  have hA' : Name_d K (η.bound 12) (η.bound 8) := ⟨η.bound 5, h'.root, h'.closed⟩
  have hn : ∀ v : Term 2, Name_d K (η.bound 12) (v.eval (ord_env_l K (η.bound 8) (η.bound 7))) := by
    intro v
    cases v with
    | free _ => exact hT'
    | bound i => exact Fin.cases hA' (fun _ => hT') i
  have hf := (forces_regular_l O' (ZFC.models_zf_l hK) _ _ hn).1 _ p h'.base hp hNext'
  exact (result K hK η).mpr (two_step_countable_master_l O' hK e he hω' hP' hE' h' hW' L' hT' hx' hxp hf)

end YesMetaZFC.Model.Forcing.Internal
