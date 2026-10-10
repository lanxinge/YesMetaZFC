import YesMetaZFC.Model.Forcing.Iteration.Fusion.Basic

/-! # 实际可数支撑条件的共尾前缀表示

由现有极限条件自动生成模型内的相容前缀图。随后融合严格恢复原条件，给出
融合接口的通用实际实例；输入可以来自任意已构造的可数支撑迭代。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

theorem row_fusion_restrict_l (hZF : M.Models ZF) {δ F H e ω D V J q}
    (h : Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F H e)
    (hl : Row_limit_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) true ω δ F H δ D V)
    (hq : M.mem q D) (hJ : M.MemberSubset J δ)
    (hcof : ∀ i, M.mem i δ → ∃ α, M.mem α J ∧ M.mem i α) : ∃ Q,
    Row_fusion_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F J Q ∧
    ∀ α p, Entry_d M α p Q ↔ M.mem α J ∧
      M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) p q α := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 1 := ⟨fun _ => q, fun _ => q⟩
  let φ : BinarySchema 1 := { body := Formula.isRestriction kpair_convention_l .newest (.bound 2) (.bound 1) }
  have hφ α p : φ.denote ρ α p ↔ M.IsRestrictionOf I p q α := Formula.satisfies_isRestriction_iff I _ _ _ _
  have total α (_ : M.mem α J) : ∃ p, φ.denote ρ α p := by
    obtain ⟨p, hp⟩ := ZF.exists_restriction hZF I q α
    exact ⟨p, (hφ α p).mpr hp⟩
  have unique α (_ : M.mem α J) p r (hp : φ.denote ρ α p) (hr : φ.denote ρ α r) : p = r :=
    ((hφ α p).mp hp).eq hZF.1 ((hφ α r).mp hr)
  obtain ⟨X, hX⟩ := ZF.exists_functionalImageOn hZF φ ρ J total unique
  obtain ⟨Q, hQ, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun α p hα hp => (hX p).mpr ⟨α, hα, hp⟩)
  have edge α p : Entry_d M α p Q ↔ M.mem α J ∧ M.IsRestrictionOf I p q α :=
    (he α p).trans (and_congr_right fun _ => hφ α p)
  refine ⟨Q, ⟨hQ.1, hQ.2.1, hJ, hcof, ?_, ?_⟩, edge⟩
  · intro α p hp
    obtain ⟨hα, hpq⟩ := (edge α p).mp hp
    obtain ⟨B, hB⟩ := (h.conditions.2.2 α).mp (hJ α hα)
    exact ⟨B, hB, row_lim_prefix_l I hZF.1 ((hl.conditions q).mp hq) hB hpq⟩
  · intro α β p r hp hr hαβ
    exact ((edge β r).mp hr).2.trans ((edge α p).mp hp).2 hαβ

/-- 共尾前缀图的实际并恢复原条件，同时给出任一早期前缀上的加强关系。 -/
theorem row_fusion_reconstruct_l (hZF : M.Models ZF) {δ F H e ω D V J q}
    (h : Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F H e)
    (hω : M.IsOmega ω)
    (hS : Row_system_supp_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) true ω F)
    (hl : Row_limit_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) true ω δ F H δ D V)
    (hq : M.mem q D) (hJ : M.MemberSubset J δ)
    (hcof : ∀ i, M.mem i δ → ∃ α, M.mem α J ∧ M.mem i α) : ∃ Q,
    Row_fusion_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F J Q ∧
    (∀ v, M.mem v q ↔ ∃ α p, Entry_d M α p Q ∧ M.mem v p) ∧
    ∀ α p, Entry_d M α p Q → M.IsRestrictionOf
      (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) p q α ∧ Entry_d M q p V := by
  obtain ⟨Q, hQ, he⟩ := row_fusion_restrict_l hZF h hl hq hJ hcof
  have qr := ((hl.conditions q).mp hq).1
  refine ⟨Q, hQ, fun v => ⟨fun hv => ?_, ?_⟩, fun α p hp => ?_⟩
  · obtain ⟨i, s, his⟩ := qr.graph v hv
    obtain ⟨α, hα, hiα⟩ := hcof i (qr.domain i s ⟨v, his, hv⟩)
    obtain ⟨p, hp⟩ := (hQ.domain α).mp hα
    obtain ⟨w, hw, hwp⟩ := (((he α p).mp hp).2.2 i s).mpr ⟨hiα, v, his, hv⟩
    exact ⟨α, p, hp, kpair_unique_l M hZF.1 hw his ▸ hwp⟩
  · rintro ⟨α, p, hp, hv⟩
    have hr := ((he α p).mp hp).2
    obtain ⟨i, s, his⟩ := hr.1 v hv
    obtain ⟨w, hw, hwq⟩ := ((hr.2 i s).mp ⟨v, his, hv⟩).2
    exact kpair_unique_l M hZF.1 hw his ▸ hwq
  · obtain ⟨B, hB, _⟩ := hQ.conditions α p hp
    obtain ⟨R, hR⟩ := (h.relations.2.2 α).mp ((h.conditions.2.2 α).mpr ⟨B, hB⟩)
    have hpre := ((he α p).mp hp).2
    exact ⟨hpre, (row_lim_link_l hZF h hω hl hB hR (hS α B hB)).below q p hq hpre⟩

end YesMetaZFC.Model.Forcing.Internal
