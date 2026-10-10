import YesMetaZFC.Model.Forcing.Iteration.Limit.Order

/-! # 支撑极限的阶段投影与前缀提升

在被替换阶段以前，拼接条件就是新前缀的限制；在其后，限制与拼接交换。
两段论证分别使用旧投影的单调性和旧阶段的实际提升，无需极限保存假设。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

theorem row_lim_link_l (hZF : M.Models ZF) {δ F H e ω σ k D V α B R}
    (h : Row_system_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) δ F H e)
    (hω : M.IsOmega ω)
    (hLimit : Row_limit_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω δ F H σ D V)
    (hB : Entry_d M α B F) (hR : Entry_d M α R H)
    (hSupp : ∀ p, M.mem p B → Row_supp_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) k ω p) :
    Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  have hσ := hLimit.sup
  have hD := hLimit.conditions
  have hV := hLimit.relation
  have hs := h.stages α B R hB hR
  have idx {β Q} (hQ : Entry_d M β Q F) : M.mem β δ := (h.conditions.2.2 β).mpr ⟨Q, hQ⟩
  have hασ : M.MemberSubset α σ := fun i hi => (hσ i).mpr ⟨α, idx hB, hi⟩
  have compare {β Q} (hQ : Entry_d M β Q F) : M.MemberSubset α β ∨ M.MemberSubset β α := by
    rcases h.conditions.1.wellOrder.linear.compare α (idx hB) β (idx hQ) with he | he | he
    · exact Or.inl (fun i hi => (he i).mp hi)
    · exact Or.inl ((h.conditions.1.mem (idx hQ)).transitive.memberSubset he)
    · exact Or.inr ((h.conditions.1.mem (idx hB)).transitive.memberSubset he)
  have self {β γ p} (hp : Row_d M β p) (hβγ : M.MemberSubset β γ) : M.IsRestrictionOf I p p γ :=
    ⟨hp.graph, fun i s => ⟨fun his => ⟨hβγ i (hp.domain i s his), his⟩, And.right⟩⟩
  have mem p (hp : M.mem p B) : M.mem p D := by
    refine (hD p).mpr ⟨⟨(hs.rows p hp).graph, (hs.rows p hp).functional,
      fun i s his => hασ i ((hs.rows p hp).domain i s his)⟩, hSupp p hp, fun β Q hQ => ?_⟩
    obtain ⟨T, hT⟩ := (h.relations.2.2 β).mp (idx hQ)
    rcases compare hQ with hαβ | hβα
    · exact ⟨p, (h.links α β B R Q T hB hR hQ hT hαβ).mem p hp, self (hs.rows p hp) hαβ⟩
    · exact (h.links β α Q T B R hQ hT hB hR hβα).restrict p hp
  have lift p a q r (hp : M.mem p D) (ha : M.IsRestrictionOf I a p α)
      (hq : M.mem q B) (hqa : Entry_d M q a R) (hr : Row_splice_d M α q p r) :
      M.mem r D ∧ Entry_d M r p V ∧ Entry_d M r q V := by
    have hp' := (hD p).mp hp
    have hqD := mem q hq
    have hq' := (hD q).mp hqD
    have haB := row_lim_prefix_l I hZF.1 hp' hB ha
    have hrα : M.IsRestrictionOf I q r α := ⟨(hs.rows q hq).graph, row_splice_prefix_l (hs.rows q hq) hr⟩
    have step β Q T (hQ : Entry_d M β Q F) (hT : Entry_d M β T H) x b c
        (hx : M.IsRestrictionOf I x r β) (hb : M.IsRestrictionOf I b p β) (hc : M.IsRestrictionOf I c q β) :
        M.mem x Q ∧ Entry_d M x b T ∧ Entry_d M x c T := by
      have hbQ := row_lim_prefix_l I hZF.1 hp' hQ hb
      have hcQ := row_lim_prefix_l I hZF.1 hq' hQ hc
      rcases compare hQ with hαβ | hβα
      · have he := hc.eq hZF.1 (self (hs.rows q hq) hαβ)
        subst c
        have hsp := row_splice_cut_l hZF.1 hαβ (hs.rows q hq).graph (hs.rows q hq).domain hx.1 hb.2 hx.2 hr
        exact (h.links α β B R Q T hB hR hQ hT hαβ).splice b a q x hbQ (hb.trans ha hαβ) hq hqa hsp
      · have he := (hrα.trans hx hβα).eq hZF.1 hc
        subst x
        exact ⟨hcQ, (h.links β α Q T B R hQ hT hB hR hβα).mono q a c b hq haB hc (ha.trans hb hβα) hqa,
          (h.stages β Q T hQ hT).order.refl c hcQ⟩
    have hrD : M.mem r D := by
      refine (hD r).mpr ⟨row_splice_row_l (hs.rows q hq) hp'.1 hασ hr,
        row_splice_supp_l I hZF hω (hSupp q hq) hp'.2.1 hr, fun β Q hQ => ?_⟩
      obtain ⟨T, hT⟩ := (h.relations.2.2 β).mp (idx hQ)
      obtain ⟨b, _, hb⟩ := hp'.2.2 β Q hQ
      obtain ⟨c, _, hc⟩ := hq'.2.2 β Q hQ
      obtain ⟨x, hx⟩ := ZF.exists_restriction hZF I r β
      exact ⟨x, (step β Q T hQ hT x b c hx hb hc).1, hx⟩
    refine ⟨hrD, (hV r p).mpr ⟨hrD, hp, ?_⟩, (hV r q).mpr ⟨hrD, hqD, ?_⟩⟩
    · intro β T hT x b hx hb
      obtain ⟨Q, hQ⟩ := (h.conditions.2.2 β).mp ((h.relations.2.2 β).mpr ⟨T, hT⟩)
      obtain ⟨c, _, hc⟩ := hq'.2.2 β Q hQ
      exact (step β Q T hQ hT x b c hx hb hc).2.1
    · intro β T hT x c hx hc
      obtain ⟨Q, hQ⟩ := (h.conditions.2.2 β).mp ((h.relations.2.2 β).mpr ⟨T, hT⟩)
      obtain ⟨b, _, hb⟩ := hp'.2.2 β Q hQ
      exact (step β Q T hQ hT x b c hx hb hc).2.2
  refine ⟨hs.rows, mem, ?_, fun p hp => ((hD p).mp hp).2.2 α B hB, ?_, ?_, lift, ?_, ?_⟩
  · intro p q hp hq
    constructor
    · intro hpq
      exact ((hV p q).mp hpq).2.2 α R hR p q (self (hs.rows p hp) (fun _ hx => hx))
        (self (hs.rows q hq) (fun _ hx => hx))
    · intro hpq
      obtain ⟨r, hr⟩ := row_splice_exists_l M hZF α p q
      have he := row_splice_absorb_l hZF.1 (hs.rows q hq) hr
      subst r
      exact (lift q q p p (mem q hq) (self (hs.rows q hq) (fun _ hx => hx)) hp hpq hr).2.1
  · intro p a hp ha
    have hp' := (hD p).mp hp
    have haB := row_lim_prefix_l I hZF.1 hp' hB ha
    exact (lift p a a p hp ha haB (hs.order.refl a haB)
      (row_splice_restore_l hZF.1 hp'.1.graph ha.1 ha.2)).2.2
  · intro p q a b _ _ ha hb hpq
    exact ((hV p q).mp hpq).2.2 α R hR a b ha hb
  · intro p a q r u hp ha hq hqa hr hu hup huq
    have hp' := (hD p).mp hp
    have hu' := (hD u).mp hu
    have hqD := mem q hq
    have hq' := (hD q).mp hqD
    have hrD := (lift p a q r hp ha hq hqa hr).1
    have hrα : M.IsRestrictionOf I q r α := ⟨(hs.rows q hq).graph, row_splice_prefix_l (hs.rows q hq) hr⟩
    refine (hV u r).mpr ⟨hu, hrD, fun β T hT x y hx hy => ?_⟩
    obtain ⟨Q, hQ⟩ := (h.conditions.2.2 β).mp ((h.relations.2.2 β).mpr ⟨T, hT⟩)
    have hxQ := row_lim_prefix_l I hZF.1 hu' hQ hx
    rcases compare hQ with hαβ | hβα
    · obtain ⟨b, hbQ, hb⟩ := hp'.2.2 β Q hQ
      have hsp := row_splice_cut_l hZF.1 hαβ (hs.rows q hq).graph (hs.rows q hq).domain hy.1 hb.2 hy.2 hr
      have hxb := ((hV u p).mp hup).2.2 β T hT x b hx hb
      have hxq := ((hV u q).mp huq).2.2 β T hT x q hx (self (hs.rows q hq) hαβ)
      exact (h.links α β B R Q T hB hR hQ hT hαβ).splice_glb b a q y x hbQ
        (hb.trans ha hαβ) hq hqa hsp hxQ hxb hxq
    · obtain ⟨c, _, hc⟩ := hq'.2.2 β Q hQ
      have he := (hrα.trans hy hβα).eq hZF.1 hc
      subst y
      exact ((hV u q).mp huq).2.2 β T hT x c hx hc
  · intro p q a b hp hq ha hb hab hd
    have hp' := (hD p).mp hp
    have hq' := (hD q).mp hq
    have haB := row_lim_prefix_l I hZF.1 hp' hB ha
    have hbB := row_lim_prefix_l I hZF.1 hq' hB hb
    refine (hV p q).mpr ⟨hp, hq, fun β T hT x y hx hy => ?_⟩
    obtain ⟨Q, hQ⟩ := (h.conditions.2.2 β).mp ((h.relations.2.2 β).mpr ⟨T, hT⟩)
    have hxQ := row_lim_prefix_l I hZF.1 hp' hQ hx
    have hyQ := row_lim_prefix_l I hZF.1 hq' hQ hy
    rcases compare hQ with hαβ | hβα
    · apply (h.links α β B R Q T hB hR hQ hT hαβ).tail x y a b hxQ hyQ (hx.trans ha hαβ) (hy.trans hb hαβ) hab
      intro c hc
      obtain ⟨d, hdc, hdd⟩ := hd c hc
      refine ⟨d, hdc, fun z hz => ?_⟩
      obtain ⟨r, hr⟩ := row_splice_exists_l M hZF α d p
      obtain ⟨r', hr'⟩ := ZF.exists_restriction hZF I r β
      have he := row_splice_unique_l M hZF.1
        (row_splice_cut_l hZF.1 hαβ (hs.rows d hdc.1).graph (hs.rows d hdc.1).domain hr'.1 hx.2 hr'.2 hr) hz
      subst r'
      exact ((hV r q).mp (hdd r hr)).2.2 β T hT z y hr' hy
    · exact (h.links β α Q T B R hQ hT hB hR hβα).mono a b x y haB hbB (ha.trans hx hβα) (hb.trans hy hβα) hab

end YesMetaZFC.Model.Forcing.Internal
