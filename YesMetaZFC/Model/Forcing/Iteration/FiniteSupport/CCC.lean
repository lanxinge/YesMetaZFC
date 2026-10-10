import YesMetaZFC.Model.Forcing.Iteration.FiniteSupport.CCCBound

/-! # 有限支撑极限的 CCC 保持

极限阶段之前的每个偏序满足 CCC，则极限也满足 CCC。证明对全部内部有限大小
界作可数覆盖，不假定索引的外部共尾性，也不强化到 Knaster 条件。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

/-- 实际有限支撑阶段系统在非零极限指标处保存 CCC。 -/
theorem row_stage_ccc_l (hZFC : M.Models ZFC) {γ F H e ω δ P V}
    (h : Row_system_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) γ F H e)
    (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hS : Row_system_supp_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) false ω F)
    (hP : Entry_d M δ P F) (hV : Entry_d M δ V H)
    (hc : ∀ α B R, M.mem α δ → Entry_d M α B F → Entry_d M α R H →
      Ccc_d M (kpair_interpretation_l M hZFC.1
        (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R B) :
    Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω P V P := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨α, hα⟩ := hδ.2.1
  have hαγ := h.conditions.1.transitive δ ((h.conditions.2.2 δ).mpr ⟨P, hP⟩) α hα
  obtain ⟨B, hB⟩ := (h.conditions.2.2 α).mp hαγ
  obtain ⟨R, hR⟩ := (h.relations.2.2 α).mp hαγ
  intro A ha
  let ρ : Env M 1 := ⟨fun _ => α, fun _ => α⟩
  let φ : BinarySchema 1 := { body := row_tail_bound_m (.bound 2) .newest (.bound 1) }
  have hφ n p : φ.denote ρ n p ↔ Row_tail_bound_d I α p n := row_tail_bound_sat_l I hZF.1 _ _ _ _
  obtain ⟨f, hf⟩ := ZF.exists_identityBijection hZF I ω
  apply ZFC.countable_cover_l I hZFC hω φ ρ ⟨f, hf.1⟩
  · intro n hn D hD
    apply row_bounded_ccc_l hZFC h hω hδ hS hP hV hc n hn α B R D hα hB hR
      ⟨fun p hp => ha.1 p ((hD p).mp hp).1,
        fun p q hp hq hpq => ha.2 p q ((hD p).mp hp).1 ((hD q).mp hq).1 hpq⟩
    exact fun p hp => (hφ n p).mp ((hD p).mp hp).2
  · intro p hp
    obtain ⟨D, hD, n, hn, f, hf⟩ := hS δ P hP p (ha.1 p hp).1
    obtain ⟨T, hT⟩ := row_tail_exists_l hZF α p
    obtain ⟨g, hg⟩ := ZF.exists_inclusionInjection hZF I
      (show M.MemberSubset T D from fun i hi => (hD i).mpr ((hT i).mp hi).1)
    exact ⟨n, hn, (hφ n p).mpr ⟨T, hT, ZF.exists_compositionInjection hZF I hg hf⟩⟩

/-- 统一有限支撑极限构造直接消费全部旧阶段的 CCC 证书。 -/
theorem row_limit_ccc_l (hZFC : M.Models ZFC) {δ F H e ω D V}
    (h : Row_system_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) δ F H e)
    (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hS : Row_system_supp_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) false ω F)
    (hl : Row_limit_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) false ω δ F H δ D V)
    (hc : ∀ α B R, Entry_d M α B F → Entry_d M α R H →
      Ccc_d M (kpair_interpretation_l M hZFC.1
        (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R B) :
    Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω D V D := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨σ, P, W, hs, ht, he⟩ := row_limit_l hZF h hω false hS
  obtain ⟨hσ, hP, hW⟩ := row_limit_unique_l I hZF.1 hs hl
  subst σ
  subst P
  subst W
  obtain ⟨μ, hμ⟩ := KP.exists_successor (ZF.modelsKP hZF) δ
  obtain ⟨F', H', h', hF', hH', hS'⟩ := row_system_extend_l (ZF.modelsKP hZF) h hμ ht
    (fun α B R hB hR => (he α B R hB hR).1)
  apply row_stage_ccc_l hZFC h' hω hδ
    (hS' I false ω hS (fun p hp => ((hl.conditions p).mp hp).2.1))
    ((hF' δ D).mpr (Or.inr ⟨rfl, rfl⟩)) ((hH' δ V).mpr (Or.inr ⟨rfl, rfl⟩))
  intro α B R hα hB hR
  have old {X J K} (hj : ∀ i p, Entry_d M i p J ↔ Entry_d M i p K ∨ (i = δ ∧ p = X))
      {a} (ha : Entry_d M α a J) : Entry_d M α a K := by
    rcases (hj α a).mp ha with ha | ⟨he, _⟩
    · exact ha
    · exact False.elim (KP.mem_irrefl_d (ZF.modelsKP hZF) δ (he ▸ hα))
  exact hc α B R (old hF' hB) (old hH' hR)

end YesMetaZFC.Model.Forcing.Internal
