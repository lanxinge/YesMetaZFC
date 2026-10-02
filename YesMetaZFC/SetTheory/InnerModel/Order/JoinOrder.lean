import YesMetaZFC.SetTheory.InnerModel.Order.Join

/-! # 端延拓链之并的良序性

任取待排序集合的一个成员所在的旧层，在该层的交集中取最小元即可。
因此不需要先替层族选择最早的索引，也不要求外部良基性。
-/

namespace YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : Structure.{u}}

theorem Rw_end_d.relation_subset_l (hE : Extensional M) {A S U R : M.Domain}
    (h : Rw_end_d A S U R) (hb : Rw_bound_d A S) : M.MemberSubset S R := by
  intro p hpS
  obtain ⟨x, hx, y, hy, hp⟩ := hb p hpS
  obtain ⟨q, hq, hqR⟩ := (h.2 x y hy).mpr ⟨hx, p, hp, hpS⟩
  exact kpair_unique_l M hE hq hp ▸ hqR

theorem rw_join_top_l (hE : Extensional M) {X U R V S : M.Domain}
    (hu : Rp_union_d false X U) (hr : Rp_union_d true X R)
    (hb : ∀ A T, Rd_entry_d A T X → Rw_bound_d A T) (hs : Rd_entry_d V S X)
    (ht : ∀ A T, Rd_entry_d A T X → Rw_end_d A T V S) : U = V ∧ R = S := by
  constructor
  · apply hE.eq_of_same_members; intro x
    rw [rp_union_entry_l hu]
    exact ⟨fun ⟨A, T, ha, hx⟩ => (ht A T ha).1 x hx, fun hx => ⟨V, S, hs, hx⟩⟩
  · apply hE.eq_of_same_members; intro p
    rw [rp_union_entry_l hr]
    exact ⟨fun ⟨A, T, ha, hp⟩ => (ht A T ha).relation_subset_l hE (hb A T ha) p hp,
      fun hp => ⟨V, S, hs, hp⟩⟩

theorem rw_join_end_l {X U R : M.Domain} (hu : Rp_union_d false X U) (hr : Rp_union_d true X R)
    (hb : ∀ A S, Rd_entry_d A S X → ∀ x y, Rd_entry_d x y S → M.mem x A ∧ M.mem y A)
    (hc : ∀ A S B T, Rd_entry_d A S X → Rd_entry_d B T X → Rw_end_d A S B T ∨ Rw_end_d B T A S)
    {A S : M.Domain} (ha : Rd_entry_d A S X) : Rw_end_d A S U R := by
  refine ⟨fun x hx => (rp_union_entry_l hu x).mpr ⟨A, S, ha, hx⟩, fun x y hy => ?_⟩
  rw [rw_join_entry_l hr]
  constructor
  · rintro ⟨B, T, hbt, hxy⟩
    rcases hc A S B T ha hbt with h | h
    · exact (h.2 x y hy).mp hxy
    · have hxyB := hb B T hbt x y hxy
      exact ⟨h.1 x hxyB.1, (h.2 x y hxyB.2).mpr ⟨hxyB.1, hxy⟩⟩
  · exact fun h => ⟨A, S, ha, h.2⟩

theorem rw_join_wellorder_l (hKP : M.Models KP) {X U R : M.Domain}
    (hu : Rp_union_d false X U) (hr : Rp_union_d true X R)
    (ho : ∀ A S, Rd_entry_d A S X → M.IsSetCodedWellOrder (kp_pair_l hKP) S A)
    (hb : ∀ A S, Rd_entry_d A S X → ∀ x y, Rd_entry_d x y S → M.mem x A ∧ M.mem y A)
    (hc : ∀ A S B T, Rd_entry_d A S X → Rd_entry_d B T X → Rw_end_d A S B T ∨ Rw_end_d B T A S) :
    M.IsSetCodedWellOrder (kp_pair_l hKP) R U ∧ (∀ x y, Rd_entry_d x y R → M.mem x U ∧ M.mem y U) := by
  have bound A S (ha : Rd_entry_d A S X) := rw_join_end_l hu hr hb hc ha
  have member x hx := (rp_union_entry_l hu x).mp hx
  have entry A S ha x y hxy := (rw_join_entry_l hr x y).mpr ⟨A, S, ha, hxy⟩
  have rel : Rw_rel_d (fun x y => Rd_entry_d x y R) U R := by
    intro p; constructor
    · intro hp
      obtain ⟨A, S, ha, hpS⟩ := (rp_union_entry_l hr p).mp hp
      obtain ⟨x, y, hp⟩ := (ho A S ha).linear.1 p hpS
      have hxy := hb A S ha x y ⟨p, hp, hpS⟩
      exact ⟨x, (bound A S ha).1 x hxy.1, y, (bound A S ha).1 y hxy.2, hp, entry A S ha x y ⟨p, hp, hpS⟩⟩
    · rintro ⟨x, _, y, _, hp, q, hq, hqR⟩
      exact kpair_unique_l M hKP.1 hq hp ▸ hqR
  have cmp x (hx : M.mem x U) y (hy : M.mem y U) : x = y ∨ Rd_entry_d x y R ∨ Rd_entry_d y x R := by
    obtain ⟨A, S, ha, hxA⟩ := member x hx
    obtain ⟨B, T, ht, hyB⟩ := member y hy
    have localcmp D Q hD hxD hyD := ((ho D Q hD).linear.2.2 x hxD y hyD).elim
      (fun he => Or.inl (hKP.1.eq_of_same_members x y he))
      (fun h => Or.inr (h.imp (entry D Q hD x y) (entry D Q hD y x)))
    exact (hc A S B T ha ht).elim (fun h => localcmp B T ht (h.1 x hxA) hyB)
      (fun h => localcmp A S ha hxA (h.1 y hyB))
  refine ⟨rel.wellorder_l hKP ?_ ?_ cmp ?_, fun x y h =>
    ⟨((rel.entry_l hKP).mp h).1, ((rel.entry_l hKP).mp h).2.1⟩⟩
  · intro x hx hxx
    obtain ⟨A, S, ha, hxA⟩ := member x hx
    exact (ho A S ha).linear.2.1.1 x hxA (((bound A S ha).2 x x hxA).mp hxx).2
  · intro x _ y _ z hz hxy hyz
    obtain ⟨A, S, ha, hzA⟩ := member z hz
    have hy := ((bound A S ha).2 y z hzA).mp hyz
    have hx := ((bound A S ha).2 x y hy.1).mp hxy
    exact entry A S ha x z ((ho A S ha).linear.2.1.2 x hx.1 y hy.1 z hzA hx.2 hy.2)
  · intro Y hy hn
    obtain ⟨y, hyY⟩ := hn
    obtain ⟨A, S, ha, hyA⟩ := member y (hy y hyY)
    obtain ⟨D, hd⟩ := KP.intersection_exists_d hKP Y A
    obtain ⟨m, hmD, hm⟩ := (ho A S ha).least D (fun x hx => ((hd x).mp hx).2) ⟨y, (hd y).mpr ⟨hyY, hyA⟩⟩
    obtain ⟨hmY, hmA⟩ := (hd m).mp hmD
    refine ⟨m, hmY, fun x hxY => ?_⟩
    classical
    by_cases hxA : M.mem x A
    · exact ((hm x ((hd x).mpr ⟨hxY, hxA⟩))).elim (fun he => Or.inl (hKP.1.eq_of_same_members m x he))
        (fun h => Or.inr (entry A S ha m x h))
    · rcases cmp m (hy m hmY) x (hy x hxY) with h | h | h
      · exact (hxA (h ▸ hmA)).elim
      · exact Or.inr h
      · exact (hxA (((bound A S ha).2 x m hmA).mp h).1).elim

end YesMetaZFC.SetTheory.InnerModel
