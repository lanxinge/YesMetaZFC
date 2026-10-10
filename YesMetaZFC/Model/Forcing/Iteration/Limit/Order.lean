import YesMetaZFC.Model.Forcing.Iteration.Limit.Syntax

/-! # 实际有限支撑与可数支撑极限偏序

索引集为内部序数 δ，极限坐标域取 σ=⋃δ。所有可能的条件图条目已经出现在
某个阶段条件中，故两次取并给出实际集合界，再从其幂集按原公式分离。
有最后阶段时此处取其坐标域；δ 是极限序数时 σ=δ。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

/-- 由模型内的阶段序列实际装配支撑极限，返回精确条件式、序关系及共同顶。 -/
theorem row_lim_order_l (hZF : M.Models ZF) {δ F H e ω σ}
    (h : Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F H e)
    (hω : M.IsOmega ω) (hσ : M.IsUnionOf σ δ) (k : Bool) : ∃ D V,
      Row_limit_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω δ F H σ D V ∧
      Row_stage_d M σ D V e := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨X, hX⟩ := ZF.exists_range_of_setFunction hZF I h.conditions.2.1 h.conditions.2.2
  obtain ⟨Y, hY⟩ := KP.exists_union (ZF.modelsKP hZF) X
  obtain ⟨Z, hZ⟩ := KP.exists_union (ZF.modelsKP hZF) Y
  have bounded p (hp : Row_lim_d I k ω σ F p) : M.MemberSubset p Z := by
    intro v hv
    obtain ⟨i, s, his⟩ := hp.1.graph v hv
    obtain ⟨α, hα, hiα⟩ := (hσ i).mp (hp.1.domain i s ⟨v, his, hv⟩)
    obtain ⟨B, hB⟩ := (h.conditions.2.2 α).mp hα
    obtain ⟨a, ha, hap⟩ := hp.2.2 α B hB
    obtain ⟨w, hw, hwa⟩ := (hap.2 i s).mpr ⟨hiα, v, his, hv⟩
    have hva := (kpair_unique_l M hZF.1 hw his) ▸ hwa
    exact (hZ v).mpr ⟨a, (hY a).mpr ⟨B, (hX B).mpr ⟨α, hB⟩, ha⟩, hva⟩
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF Z
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push σ).push F
  let φ : UnarySchema 3 := { body := row_lim_m k (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨D, hD'⟩ := ZF.separation_exists_d hZF φ ρ P
  have hD p : M.mem p D ↔ Row_lim_d I k ω σ F p := by
    refine (hD' p).trans ?_
    rw [row_lim_sat_l I hZF.1]
    exact ⟨And.right, fun hp => ⟨(hP p).mpr (bounded p hp), hp⟩⟩
  let η : Env M 1 := ⟨fun _ => H, fun _ => H⟩
  let ψ : BinarySchema 1 := { body := row_lim_le_m (.bound 2) (.bound 1) .newest }
  obtain ⟨V, hGraph, hV'⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ η D
  have hV p q : Entry_d M p q V ↔ M.mem p D ∧ M.mem q D ∧ Row_lim_le_d I H p q :=
    (hV' p q).trans (and_congr_right fun _ => and_congr_right fun _ => row_lim_le_sat_l I hZF.1 _ _ _ _)
  have pre {p α B a} (hp : M.mem p D) (hB : Entry_d M α B F) (ha : M.IsRestrictionOf I a p α) : M.mem a B :=
    row_lim_prefix_l I hZF.1 ((hD p).mp hp) hB ha
  have stage α R (hR : Entry_d M α R H) : ∃ B, Entry_d M α B F ∧ Row_stage_d M α B R e := by
    obtain ⟨B, hB⟩ := (h.conditions.2.2 α).mp ((h.relations.2.2 α).mpr ⟨R, hR⟩)
    exact ⟨B, hB, h.stages α B R hB hR⟩
  have O : Cond_order_d M D V D := {
    refl := by
      intro p hp
      refine (hV p p).mpr ⟨hp, hp, fun α R hR a b ha hb => ?_⟩
      obtain ⟨B, hB, hs⟩ := stage α R hR
      have he := ha.eq hZF.1 hb
      subst b
      exact hs.order.refl a (pre hp hB ha)
    trans := by
      intro p q r hp hq hr hpq hqr
      refine (hV p r).mpr ⟨hp, hr, fun α R hR a c ha hc => ?_⟩
      obtain ⟨B, hB, hs⟩ := stage α R hR
      obtain ⟨b, hb, hbq⟩ := ((hD q).mp hq).2.2 α B hB
      exact hs.order.trans a b c (pre hp hB ha) hb (pre hr hB hc)
        (((hV p q).mp hpq).2.2 α R hR a b ha hbq)
        (((hV q r).mp hqr).2.2 α R hR b c hbq hc)
    zero := by
      intro p _ hp
      exact False.elim (KP.mem_irrefl_d (ZF.modelsKP hZF) D ((hV p D).mp hp).2.1) }
  have er α : M.IsRestrictionOf I e e α := ⟨(row_empty_l M (α := α) h.empty).graph, fun i s =>
    ⟨fun ⟨v, _, hv⟩ => False.elim (h.empty v hv), And.right⟩⟩
  have heD : M.mem e D := by
    refine (hD e).mpr ⟨row_empty_l M h.empty, row_supp_empty_l I hZF hω h.empty k, fun α B hB => ?_⟩
    obtain ⟨R, hR⟩ := (h.relations.2.2 α).mp ((h.conditions.2.2 α).mpr ⟨B, hB⟩)
    exact ⟨e, (h.stages α B R hB hR).base, er α⟩
  refine ⟨D, V, ⟨hσ, hD, hGraph.1, hV⟩, ⟨O, heD, ?_, fun p hp => ((hD p).mp hp).1⟩⟩
  intro p hp
  refine (hV p e).mpr ⟨hp, heD, fun α R hR a b ha hb => ?_⟩
  obtain ⟨B, hB, hs⟩ := stage α R hR
  have he := hb.eq hZF.1 (er α)
  subst b
  exact hs.top a (pre hp hB ha)

end YesMetaZFC.Model.Forcing.Internal
