import YesMetaZFC.Model.Forcing.Iteration.Limit.Basic
import YesMetaZFC.SetTheory.Card.FiniteOrdinal

/-! # 有限支撑极限的直接并刻画

有限定义域在某个早期坐标域中有界，故其在该处的限制就是原条件。
条件集与序关系都精确等于阶段直接并；空阶段集须排除，因为零极限含空条件。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

/-- 任一有限支撑极限条件已属于某个早期阶段。 -/
theorem row_lim_bounded_l (hZF : M.Models ZF) {δ F H e ω σ p}
    (h : Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F H e)
    (hω : M.IsOmega ω) (hσ : M.IsUnionOf σ δ) (hne : ∃ α, M.mem α δ)
    (hp : Row_lim_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) false ω σ F p) :
    ∃ α B, Entry_d M α B F ∧ M.mem p B := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨D, hD, hd⟩ := hp.2.1
  obtain ⟨α, hα, hDα⟩ := ZF.finite_union_bound_l I hZF hω h.conditions.1 hσ hne hd
    (fun i hi => (hD i).mp hi |>.elim fun s hs => hp.1.domain i s hs)
  obtain ⟨B, hB⟩ := (h.conditions.2.2 α).mp hα
  have hpp : M.IsRestrictionOf I p p α := ⟨hp.1.graph, fun i s =>
    ⟨fun hs => ⟨hDα i ((hD i).mpr ⟨s, hs⟩), hs⟩, And.right⟩⟩
  exact ⟨α, B, hB, row_lim_prefix_l I hZF.1 hp hB hpp⟩

/-- 非空阶段系统的有限支撑极限，条件与序逐一等于早期阶段的直接并。 -/
theorem row_limit_union_l (hZF : M.Models ZF) {δ F H e ω σ D V}
    (h : Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F H e)
    (hω : M.IsOmega ω) (hne : ∃ α, M.mem α δ)
    (hS : Row_system_supp_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) false ω F)
    (hl : Row_limit_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) false ω δ F H σ D V) :
    (∀ p, M.mem p D ↔ ∃ α B, Entry_d M α B F ∧ M.mem p B) ∧
    (∀ p q, Entry_d M p q V ↔ ∃ α B R,
      Entry_d M α B F ∧ Entry_d M α R H ∧ M.mem p B ∧ M.mem q B ∧ Entry_d M p q R) := by
  have link α B R (hB : Entry_d M α B F) (hR : Entry_d M α R H) :=
    row_lim_link_l hZF h hω hl hB hR (hS α B hB)
  have mem p : M.mem p D ↔ ∃ α B, Entry_d M α B F ∧ M.mem p B := by
    constructor
    · exact fun hp => row_lim_bounded_l hZF h hω hl.sup hne ((hl.conditions p).mp hp)
    · rintro ⟨α, B, hB, hp⟩
      obtain ⟨R, hR⟩ := (h.relations.2.2 α).mp ((h.conditions.2.2 α).mpr ⟨B, hB⟩)
      exact (link α B R hB hR).mem p hp
  refine ⟨mem, fun p q => ⟨fun hpq => ?_, ?_⟩⟩
  · obtain ⟨α, B, hB, hp⟩ := (mem p).mp ((hl.relation p q).mp hpq).1
    obtain ⟨β, C, hC, hq⟩ := (mem q).mp ((hl.relation p q).mp hpq).2.1
    have hα := (h.conditions.2.2 α).mpr ⟨B, hB⟩
    have hβ := (h.conditions.2.2 β).mpr ⟨C, hC⟩
    obtain ⟨R, hR⟩ := (h.relations.2.2 α).mp hα
    obtain ⟨S, hT⟩ := (h.relations.2.2 β).mp hβ
    have in_stage γ Q T (hQ : Entry_d M γ Q F) (hT : Entry_d M γ T H)
        (hp : M.mem p Q) (hq : M.mem q Q) : ∃ α B R,
          Entry_d M α B F ∧ Entry_d M α R H ∧ M.mem p B ∧ M.mem q B ∧ Entry_d M p q R :=
      ⟨γ, Q, T, hQ, hT, hp, hq, ((link γ Q T hQ hT).order p q hp hq).mp hpq⟩
    rcases h.conditions.1.wellOrder.linear.compare α hα β hβ with he | he | he
    · have he := hZF.1.eq_of_same_members α β he
      subst β
      have he := h.conditions.2.1.2 α B C hB hC
      subst C
      exact in_stage α B R hB hR hp hq
    · exact in_stage β C S hC hT
        ((h.links α β B R C S hB hR hC hT ((h.conditions.1.mem hβ).transitive.memberSubset he)).mem p hp) hq
    · exact in_stage α B R hB hR hp
        ((h.links β α C S B R hC hT hB hR ((h.conditions.1.mem hα).transitive.memberSubset he)).mem q hq)
  · rintro ⟨α, B, R, hB, hR, hp, hq, hpq⟩
    exact ((link α B R hB hR).order p q hp hq).mpr hpq

end YesMetaZFC.Model.Forcing.Internal
