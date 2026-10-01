import YesMetaZFC.Model.Forcing.Proper.Elementary.Membership
import YesMetaZFC.Model.Forcing.Internal.Atomic.Syntax

/-! # 传递隶属结构中的有界力迫证书

关系图内的所有坐标都落在传递载体中，条件量词受 B 所界，匹配见证受目标名称
的条目所界。因此一个已经属于载体的双模拟证书在两种隶属解释中完全相同。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem trans_kpair_l {X p a b : M.Domain} (hX : M.TransitiveSet X) (hp : M.mem p X)
    (h : KPair_d M p a b) : M.mem a X ∧ M.mem b X := by
  have hc x (hx : x = a ∨ x = b) : M.mem x X := by
    obtain ⟨v, hvp, hxv⟩ := (kpair_union_l M h x).mpr hx
    exact hX v (hX p hp v hvp) x hxv
  exact ⟨hc a (Or.inl rfl), hc b (Or.inr rfl)⟩

theorem trans_entry_l {X F a b : M.Domain} (hX : M.TransitiveSet X) (hF : M.mem F X)
    (h : Entry_d M a b F) : M.mem a X ∧ M.mem b X :=
  h.elim fun p hp => trans_kpair_l hX (hX F hF p hp.2) hp.1

theorem trans_rel_l {X F p s t : M.Domain} (hX : M.TransitiveSet X) (hF : M.mem F X)
    (h : Rel_d M F p s t) : M.mem p X ∧ M.mem s X ∧ M.mem t X := by
  obtain ⟨q, ⟨a, ha, hq⟩, hqF⟩ := h
  have hc := trans_kpair_l hX (hX F hF q hqF) hq
  exact ⟨hc.1, trans_kpair_l hX hc.2 ha⟩

variable {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
variable {c X T : M.Domain} (hM : Smdl_d I c X T)
  (hT : ∀ x y, M.PairMember I x y T ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y)
  (hX : M.TransitiveSet X)
local notation "L" => smdl_structure_l I (R := T) (And.left (And.right hM))
include hT hX

theorem smem_triple_l (q p s t : (L).Domain) : Triple_d L q p s t ↔ Triple_d M q.val p.val s.val t.val := by
  constructor
  · rintro ⟨a, ha, hq⟩
    exact ⟨a.val, (smem_kpair_l I hM hT hX a s t).mp ha, (smem_kpair_l I hM hT hX q p a).mp hq⟩
  · rintro ⟨a, ha, hq⟩
    let a' : (L).Domain := ⟨a, (trans_kpair_l hX q.property hq).2⟩
    exact ⟨a', (smem_kpair_l I hM hT hX a' s t).mpr ha, (smem_kpair_l I hM hT hX q p a').mpr hq⟩

theorem smem_rel_l (F p s t : (L).Domain) : Rel_d L F p s t ↔ Rel_d M F.val p.val s.val t.val := by
  constructor
  · rintro ⟨q, hq, hqF⟩
    exact ⟨q.val, (smem_triple_l I hM hT hX q p s t).mp hq, (smem_member_l I hM hT q F).mp hqF⟩
  · rintro ⟨q, hq, hqF⟩
    let q' : (L).Domain := ⟨q, hX F.val F.property q hqF⟩
    exact ⟨q', (smem_triple_l I hM hT hX q' p s t).mpr hq, (smem_member_l I hM hT q' F).mpr hqF⟩

theorem smem_below_l (B R z q p : (L).Domain) : Below_d L B R z q p ↔ Below_d M B.val R.val z.val q.val p.val :=
  and_congr (smem_member_l I hM hT q B) (and_congr
    (not_congr ⟨congrArg Subtype.val, Subtype.ext⟩) (smem_entry_l I hM hT hX q p R))

theorem smem_match_wit_l (k : Bool) (B R z F q a t : (L).Domain) :
    Match_wit_d L k B R z F q a t ↔ Match_wit_d M k B.val R.val z.val F.val q.val a.val t.val := by
  have hrel (r d : (L).Domain) :
      (if k then Rel_d L F r d a else Rel_d L F r a d) ↔
        (if k then Rel_d M F.val r.val d.val a.val else Rel_d M F.val r.val a.val d.val) := by
    cases k
    · exact smem_rel_l I hM hT hX F r a d
    · exact smem_rel_l I hM hT hX F r d a
  constructor
  · rintro ⟨r, d, c, hr, hd, hrc, hrel'⟩
    exact ⟨r.val, d.val, c.val, (smem_below_l I hM hT hX B R z r q).mp hr,
      (smem_entry_l I hM hT hX d c t).mp hd, (smem_entry_l I hM hT hX r c R).mp hrc, (hrel r d).mp hrel'⟩
  · rintro ⟨r, d, c, hr, hd, hrc, hrel'⟩
    let r' : (L).Domain := ⟨r, hX B.val B.property r hr.1⟩
    let d' : (L).Domain := ⟨d, (trans_entry_l hX t.property hd).1⟩
    let c' : (L).Domain := ⟨c, (trans_entry_l hX t.property hd).2⟩
    exact ⟨r', d', c', (smem_below_l I hM hT hX B R z r' q).mpr hr,
      (smem_entry_l I hM hT hX d' c' t).mpr hd, (smem_entry_l I hM hT hX r' c' R).mpr hrc, (hrel r' d').mpr hrel'⟩

theorem smem_match_l (k : Bool) (B R z F p s t : (L).Domain) :
    Match_d L k B R z F p s t ↔ Match_d M k B.val R.val z.val F.val p.val s.val t.val := by
  constructor
  · intro h a b hab q hq hqb
    let a' : (L).Domain := ⟨a, (trans_entry_l hX s.property hab).1⟩
    let b' : (L).Domain := ⟨b, (trans_entry_l hX s.property hab).2⟩
    let q' : (L).Domain := ⟨q, hX B.val B.property q hq.1⟩
    exact (smem_match_wit_l I hM hT hX k B R z F q' a' t).mp
      (h a' b' ((smem_entry_l I hM hT hX a' b' s).mpr hab) q'
        ((smem_below_l I hM hT hX B R z q' p).mpr hq) ((smem_entry_l I hM hT hX q' b' R).mpr hqb))
  · intro h a b hab q hq hqb
    exact (smem_match_wit_l I hM hT hX k B R z F q a t).mpr
      (h a.val b.val ((smem_entry_l I hM hT hX a b s).mp hab) q.val
        ((smem_below_l I hM hT hX B R z q p).mp hq) ((smem_entry_l I hM hT hX q b R).mp hqb))

theorem smem_bisim_l (B R z F : (L).Domain) : Bisim_d L B R z F ↔ Bisim_d M B.val R.val z.val F.val := by
  constructor
  · intro h p s t hpst
    have hc := trans_rel_l hX F.property hpst
    let p' : (L).Domain := ⟨p, hc.1⟩
    let s' : (L).Domain := ⟨s, hc.2.1⟩
    let t' : (L).Domain := ⟨t, hc.2.2⟩
    have hh := h p' s' t' ((smem_rel_l I hM hT hX F p' s' t').mpr hpst)
    exact ⟨(smem_match_l I hM hT hX false B R z F p' s' t').mp hh.1,
      (smem_match_l I hM hT hX true B R z F p' t' s').mp hh.2⟩
  · intro h p s t hpst
    have hh := h p.val s.val t.val ((smem_rel_l I hM hT hX F p s t).mp hpst)
    exact ⟨(smem_match_l I hM hT hX false B R z F p s t).mpr hh.1,
      (smem_match_l I hM hT hX true B R z F p t s).mpr hh.2⟩

theorem smem_supp_l (B S : (L).Domain) : Supp_d L B S ↔ Supp_d M B.val S.val := by
  constructor
  · intro h t ht p hp
    let t' : (L).Domain := ⟨t, hX S.val S.property t ht⟩
    let p' : (L).Domain := ⟨p, hX t t'.property p hp⟩
    obtain ⟨a, b, hab, ha, hb⟩ := h t' ((smem_member_l I hM hT t' S).mpr ht) p' ((smem_member_l I hM hT p' t').mpr hp)
    exact ⟨a.val, b.val, (smem_kpair_l I hM hT hX p' a b).mp hab,
      (smem_member_l I hM hT a S).mp ha, (smem_member_l I hM hT b B).mp hb⟩
  · intro h t ht p hp
    obtain ⟨a, b, hab, ha, hb⟩ := h t.val ((smem_member_l I hM hT t S).mp ht) p.val ((smem_member_l I hM hT p t).mp hp)
    let a' : (L).Domain := ⟨a, hX S.val S.property a ha⟩
    let b' : (L).Domain := ⟨b, hX B.val B.property b hb⟩
    exact ⟨a', b', (smem_kpair_l I hM hT hX p a' b').mpr hab,
      (smem_member_l I hM hT a' S).mpr ha, (smem_member_l I hM hT b' B).mpr hb⟩

end YesMetaZFC.Model.Forcing.Internal
