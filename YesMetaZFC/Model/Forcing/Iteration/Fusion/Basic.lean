import YesMetaZFC.Model.Forcing.Iteration.Fusion.Syntax

/-! # 内部可数前缀族的精确融合

取条件族值域的实际并。序数指标可比与前缀一致性保证并图单值，模型内可数并
保证支撑可数。共尾性使每个阶段限制都已由族中的某个前缀决定。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

/-- 可数共尾前缀族有唯一融合条件，精确保留全部前缀并低于每个前缀条件。 -/
theorem row_fusion_l (hZFC : M.Models ZFC) {δ F H e ω D V J Q}
    (h : Row_system_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) δ F H e)
    (hω : M.IsOmega ω)
    (hS : Row_system_supp_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) true ω F)
    (hl : Row_limit_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) true ω δ F H δ D V)
    (hf : Row_fusion_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) δ F J Q)
    (hJ : M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) J ω) : ∃ q,
    M.mem q D ∧ (∀ v, M.mem v q ↔ ∃ α p, Entry_d M α p Q ∧ M.mem v p) ∧
    (∀ α p, Entry_d M α p Q → M.IsRestrictionOf
      (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) p q α ∧ Entry_d M q p V) ∧
    ∀ r, M.mem r D → (∀ α p, Entry_d M α p Q → M.IsRestrictionOf
      (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) p r α) → r = q := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨X, hX⟩ := ZF.exists_range_of_setFunction hZF I hf.function hf.domain
  obtain ⟨q, hq⟩ := KP.exists_union (ZF.modelsKP hZF) X
  have mem v : M.mem v q ↔ ∃ α p, Entry_d M α p Q ∧ M.mem v p := by
    rw [hq v]
    exact ⟨fun ⟨p, hp, hv⟩ => (hX p).mp hp |>.elim fun α hα => ⟨α, p, hα, hv⟩,
      fun ⟨α, p, hp, hv⟩ => ⟨p, (hX p).mpr ⟨α, hp⟩, hv⟩⟩
  have edge i s : Entry_d M i s q ↔ ∃ α p, Entry_d M α p Q ∧ Entry_d M i s p := by
    constructor
    · rintro ⟨v, hv, hvq⟩
      obtain ⟨α, p, hp, hvp⟩ := (mem v).mp hvq
      exact ⟨α, p, hp, v, hv, hvp⟩
    · rintro ⟨α, p, hp, v, hv, hvp⟩
      exact ⟨v, hv, (mem v).mpr ⟨α, p, hp, hvp⟩⟩
  have idx {α p} (hp : Entry_d M α p Q) : M.mem α δ := hf.subset α ((hf.domain α).mpr ⟨p, hp⟩)
  have row {α p} (hp : Entry_d M α p Q) : Row_d M α p := by
    obtain ⟨B, hB, hpB⟩ := hf.conditions α p hp
    obtain ⟨R, hR⟩ := (h.relations.2.2 α).mp (idx hp)
    exact (h.stages α B R hB hR).rows p hpB
  have pre α p (hp : Entry_d M α p Q) : M.IsRestrictionOf I p q α := by
    refine ⟨(row hp).graph, fun i s => ⟨fun his => ⟨(row hp).domain i s his, (edge i s).mpr ⟨α, p, hp, his⟩⟩, ?_⟩⟩
    rintro ⟨hiα, his⟩
    obtain ⟨β, r, hr, hir⟩ := (edge i s).mp his
    rcases h.conditions.1.wellOrder.linear.compare α (idx hp) β (idx hr) with he | he | he
    · exact ((hf.coherent α β p r hp hr (fun j hj => (he j).mp hj)).2 i s).mpr ⟨hiα, hir⟩
    · exact ((hf.coherent α β p r hp hr ((h.conditions.1.mem (idx hr)).transitive.memberSubset he)).2 i s).mpr ⟨hiα, hir⟩
    · exact ((hf.coherent β α r p hr hp ((h.conditions.1.mem (idx hp)).transitive.memberSubset he)).2 i s).mp hir |>.2
  have qr : Row_d M δ q := by
    refine ⟨fun v hv => ?_, fun i s t his hit => ?_, fun i s his => ?_⟩
    · obtain ⟨α, p, hp, hvp⟩ := (mem v).mp hv
      exact (row hp).graph v hvp
    · obtain ⟨α, p, hp, hip⟩ := (edge i s).mp his
      obtain ⟨β, hβ, hiβ⟩ := hf.cofinal i (h.conditions.1.transitive α (idx hp) i ((row hp).domain i s hip))
      obtain ⟨r, hr⟩ := (hf.domain β).mp hβ
      exact (row hr).functional i s t (((pre β r hr).2 i s).mpr ⟨hiβ, his⟩)
        (((pre β r hr).2 i t).mpr ⟨hiβ, hit⟩)
    · obtain ⟨α, p, hp, hip⟩ := (edge i s).mp his
      exact h.conditions.1.transitive α (idx hp) i ((row hp).domain i s hip)
  have hQ : M.IsSetFunctionFromTo I Q J X := ⟨hf.function, hf.domain, fun α hα => by
    obtain ⟨p, hp⟩ := (hf.domain α).mp hα
    exact ⟨p, (hX p).mpr ⟨α, hp⟩, hp⟩⟩
  obtain ⟨f, hfX⟩ := ZFC.surjection_bound_l I hZFC hQ (fun p hp => by
    obtain ⟨α, hp⟩ := (hX p).mp hp
    exact ⟨α, (hf.domain α).mpr ⟨p, hp⟩, hp⟩)
  obtain ⟨g, hg⟩ := hJ
  obtain ⟨C, hC, hc⟩ := row_countable_coords_l hZFC hω (ZF.exists_compositionInjection hZF I hfX hg)
    (fun p hp => by
      obtain ⟨α, hp⟩ := (hX p).mp hp
      obtain ⟨B, hB, hpB⟩ := hf.conditions α p hp
      exact hS α B hB p hpB)
  have qs : Row_supp_d I true ω q := by
    refine ⟨C, fun i => (hC i).trans ⟨?_, ?_⟩, hc⟩
    · rintro ⟨p, hp, s, his⟩
      obtain ⟨α, hp⟩ := (hX p).mp hp
      exact ⟨s, (edge i s).mpr ⟨α, p, hp, his⟩⟩
    · rintro ⟨s, his⟩
      obtain ⟨α, p, hp, hip⟩ := (edge i s).mp his
      exact ⟨p, (hX p).mpr ⟨α, hp⟩, s, hip⟩
  have qD : M.mem q D := by
    refine (hl.conditions q).mpr ⟨qr, qs, fun α B hB => ?_⟩
    obtain ⟨β, hβ, hαβ⟩ := hf.cofinal α ((h.conditions.2.2 α).mpr ⟨B, hB⟩)
    obtain ⟨p, hp⟩ := (hf.domain β).mp hβ
    obtain ⟨C, hC, hpC⟩ := hf.conditions β p hp
    obtain ⟨R, hR⟩ := (h.relations.2.2 α).mp ((h.conditions.2.2 α).mpr ⟨B, hB⟩)
    obtain ⟨S, hT⟩ := (h.relations.2.2 β).mp (idx hp)
    have sub := (h.conditions.1.mem (idx hp)).transitive.memberSubset hαβ
    obtain ⟨a, ha, hap⟩ := (h.links α β B R C S hB hR hC hT sub).restrict p hpC
    refine ⟨a, ha, hap.1, fun i s => (hap.2 i s).trans ?_⟩
    exact ⟨fun ⟨hi, his⟩ => ⟨hi, (((pre β p hp).2 i s).mp his).2⟩,
      fun ⟨hi, his⟩ => ⟨hi, ((pre β p hp).2 i s).mpr ⟨sub i hi, his⟩⟩⟩
  refine ⟨q, qD, mem, fun α p hp => ?_, fun r hr hh => ?_⟩
  · obtain ⟨B, hB, _⟩ := hf.conditions α p hp
    obtain ⟨R, hR⟩ := (h.relations.2.2 α).mp (idx hp)
    exact ⟨pre α p hp, (row_lim_link_l hZF h hω hl hB hR (hS α B hB)).below q p qD (pre α p hp)⟩
  · apply row_ext_l hZF.1 ((hl.conditions r).mp hr).1 qr
    intro i s
    constructor <;> intro his
    · obtain ⟨α, hα, hiα⟩ := hf.cofinal i (((hl.conditions r).mp hr).1.domain i s his)
      obtain ⟨p, hp⟩ := (hf.domain α).mp hα
      exact (((pre α p hp).2 i s).mp (((hh α p hp).2 i s).mpr ⟨hiα, his⟩)).2
    · obtain ⟨α, hα, hiα⟩ := hf.cofinal i (qr.domain i s his)
      obtain ⟨p, hp⟩ := (hf.domain α).mp hα
      exact (((hh α p hp).2 i s).mp (((pre α p hp).2 i s).mpr ⟨hiα, his⟩)).2

end YesMetaZFC.Model.Forcing.Internal
