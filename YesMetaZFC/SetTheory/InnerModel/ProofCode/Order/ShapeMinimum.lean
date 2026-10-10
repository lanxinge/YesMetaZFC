import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.Height

/-! # 最小构造符纤维及叶码最小元 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project Internal
universe u
variable {M : Structure.{u}}

theorem ps_shape_bound_l {T c : M.Domain} (ht : M.TransitiveSet T) (hc : M.mem c T) (hv : Ps_valid_d c) :
    (∃ a, Pc_leaf_d T c a ∧ M.IsOrdinal a) ∨ ∃ k a b d, Pc_node_d T k c a b d := by
  rcases ps_valid_unfold_l hv with ⟨U, a, ⟨e, _, he, hp⟩, ha⟩ | ⟨U, k, a, b, d, hn, _⟩
  · exact Or.inl ⟨a, ⟨e, (po_pair_bound_l ht hc hp).1, he, hp⟩, ha⟩
  · exact Or.inr ⟨k, a, b, d, (po_node_fields_l ht hc hn).1⟩

theorem po_top_min_l (hM : M.Models KPi) {X : M.Domain} (hv : ∀ c, M.mem c X → Ps_valid_d c) (hn : ∃ c, M.mem c X) :
    ∃ T U, M.TransitiveSet T ∧ M.MemberSubset X T ∧ M.MemberSubset U X ∧ (∃ c, M.mem c U) ∧
      ((∀ c, M.mem c U → ∃ a, Pc_leaf_d T c a ∧ M.IsOrdinal a) ∨
        ∃ k, ∀ c, M.mem c U → ∃ a b d, Pc_node_d T k c a b d) ∧
      ∀ c, M.mem c U → ∀ d, M.mem d X → M.mem d U ∨ Po_lt_d c d := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨T, ht, hXT⟩ := KPi.transitive_cover_l hM X
  have xt := ht X hXT
  let ρ := (jh_env_l T).push T
  have proj c a := po_proj_sat_l hKP.1 false ρ c a
  have total c (hc : M.mem c X) : ∃ t, (po_proj_s false).toBinarySchema.denote ρ c t ∧ M.IsOrdinal t := by
    rcases ps_shape_bound_l ht (xt c hc) (hv c hc) with ⟨a, ⟨e, _, he, hp⟩, _⟩ | ⟨k, a, b, d, t, _, p, _, hn, _, hp⟩
    · exact ⟨e, (proj c e).mpr ⟨a, (po_pair_bound_l ht (xt c hc) hp).2, hp⟩,
        KPi.n0_ordinal_l hM (KP.n0_empty_l he)⟩
    · exact ⟨t, (proj c t).mpr ⟨p, (po_pair_bound_l ht (xt c hc) hp).2, hp⟩,
        KPi.n0_ordinal_l hM (po_num_natural_l hKP.1 hn)⟩
  have unique c (_ : M.mem c X) a b ha hb := po_proj_unique_l false ((proj c a).mp ha) ((proj c b).mp hb)
  obtain ⟨t, U, hU, hUn, hm⟩ := po_minfiber_l hKP (po_proj_s false) ρ X
    (fun c hc => (total c hc).imp (fun _ h => h.1)) unique (R := M.mem) (by
      intro Y hY
      apply po_ordinal_min_l hKP
      · intro a ha
        obtain ⟨c, hc, hca⟩ := (hY a).mp ha
        obtain ⟨b, hcb, hb⟩ := total c hc
        exact unique c hc b a hcb hca ▸ hb
      · obtain ⟨c, hc⟩ := hn
        obtain ⟨a, ha, _⟩ := total c hc
        exact ⟨a, (hY a).mpr ⟨c, hc, ha⟩⟩)
  have sub c hc := ((hU c).mp hc).1
  have top {c} (hc : M.mem c U) : Po_proj_d false T c t := (proj c t).mp ((hU c).mp hc).2
  have same {c s p} (hc : M.mem c U) (hp : KPair_d M c s p) : t = s := by
    obtain ⟨q, _, hq⟩ := top hc
    exact (kpair_injective_l M hq hp).1
  refine ⟨T, U, ht, xt, sub, hUn, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := hUn
    rcases ps_shape_bound_l ht (xt c (sub c hc)) (hv c (sub c hc)) with ⟨a, ⟨e, _, he, hp⟩, _⟩ | ⟨k, a, b, d, s, _, p, _, hs, _, hp⟩
    · have he : Num_d 0 t := (same hc hp).symm ▸ he
      refine Or.inl (fun d hd => ?_)
      rcases ps_shape_bound_l ht (xt d (sub d hd)) (hv d (sub d hd)) with hl | ⟨l, x, y, z, s, _, p, _, hs, _, hp⟩
      · exact hl
      · have hs : Num_d (pc_tag_l l) t := (same hd hp).symm ▸ hs
        exact (Nat.ne_of_gt (pc_tag_pos_l l) (num_injective_l hKP hs he)).elim
    · have hs : Num_d (pc_tag_l k) t := (same hc hp).symm ▸ hs
      refine Or.inr ⟨k, fun c hc => ?_⟩
      rcases ps_shape_bound_l ht (xt c (sub c hc)) (hv c (sub c hc)) with ⟨a, ⟨e, _, he, hp⟩, _⟩ | ⟨l, a, b, d, hl⟩
      · have he : Num_d 0 t := (same hc hp).symm ▸ he
        exact (Nat.ne_of_gt (pc_tag_pos_l k) (num_injective_l hKP hs he)).elim
      · have hl' := hl
        obtain ⟨s, _, p, _, ho, _, hp⟩ := hl
        have ho : Num_d (pc_tag_l l) t := (same hc hp).symm ▸ ho
        have hk := pc_tag_inj_l (num_injective_l hKP hs ho); subst l
        exact ⟨a, b, d, hl'⟩
  · intro c hc d hd
    obtain ⟨s, hs, _⟩ := total d hd
    rcases hm d hd s hs with he | hlt
    · exact Or.inl ((hU d).mpr ⟨hd, he.symm ▸ hs⟩)
    · obtain ⟨a, ha, hp⟩ := top hc
      obtain ⟨b, hb, hq⟩ := (proj d s).mp hs
      exact Or.inr (po_close_l hM (Or.inr (Or.inl ⟨t, (po_pair_bound_l ht (xt c (sub c hc)) hp).1,
        s, (po_pair_bound_l ht (xt d hd) hq).1, a, ha, b, hb, hp, hq, hlt⟩)))

theorem po_leaf_min_l (hM : M.Models KPi) {T X : M.Domain}
    (hl : ∀ c, M.mem c X → ∃ a, Pc_leaf_d T c a ∧ M.IsOrdinal a) (hn : ∃ c, M.mem c X) : Po_min_d Po_lt_d X := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let ρ := (jh_env_l T).push T
  have proj c a := po_proj_sat_l hKP.1 true ρ c a
  have total c (hc : M.mem c X) : ∃ a, (po_proj_s true).toBinarySchema.denote ρ c a := by
    obtain ⟨a, ⟨e, he, _, hp⟩, _⟩ := hl c hc
    exact ⟨a, (proj c a).mpr ⟨e, he, hp⟩⟩
  have leaf c (hc : M.mem c X) a (ha : (po_proj_s true).toBinarySchema.denote ρ c a) : Pc_leaf_d T c a ∧ M.IsOrdinal a := by
    obtain ⟨b, hb, ho⟩ := hl c hc
    have hb' := hb
    obtain ⟨e, he, _, hp⟩ := hb
    have heq := po_proj_unique_l true ((proj c a).mp ha) (show Po_proj_d true T c b from ⟨e, he, hp⟩)
    exact heq.symm ▸ ⟨hb', ho⟩
  obtain ⟨a, U, hU, ⟨c, hc⟩, hm⟩ := po_minfiber_l hKP (po_proj_s true) ρ X total
    (fun c _ a b ha hb => po_proj_unique_l true ((proj c a).mp ha) ((proj c b).mp hb)) (R := M.mem) (by
      intro Y hY
      apply po_ordinal_min_l hKP
      · intro a ha; obtain ⟨c, hc, ha⟩ := (hY a).mp ha; exact (leaf c hc a ha).2
      · obtain ⟨c, hc⟩ := hn; obtain ⟨a, ha⟩ := total c hc; exact ⟨a, (hY a).mpr ⟨c, hc, ha⟩⟩)
  have hca := (hU c).mp hc
  refine ⟨c, hca.1, fun d hd => ?_⟩
  obtain ⟨b, hb⟩ := total d hd
  rcases hm d hd b hb with he | he
  · subst b; exact Or.inl (pc_leaf_unique_l hKP.1 (leaf c hca.1 a hca.2).1 (leaf d hd a hb).1)
  · exact Or.inr ((po_leaf_iff_l hM (leaf c hca.1 a hca.2).1 (leaf d hd b hb).1).mpr he)

end YesMetaZFC.SetTheory.InnerModel
