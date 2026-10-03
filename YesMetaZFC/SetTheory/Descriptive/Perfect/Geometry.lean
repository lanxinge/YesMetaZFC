import YesMetaZFC.SetTheory.Descriptive.Perfect.Splitting

/-! # 分裂节点的长度增长与自由坐标柱集 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem split_extend_l {ω A J U L R a b} (hs : Split_d I ω A J U L R)
    (h : M.PairMember I a b L ∨ M.PairMember I a b R) : M.MemberSubset a b := by
  rcases h with h | h
  · obtain ⟨c, _, hc⟩ := hs.2.2.1.2.2 a (hs.2.1.input_mem_of_pairMember h)
    exact (hs.2.2.2 a b c h hc).1
  · obtain ⟨c, _, hc⟩ := hs.2.1.2.2 a (hs.2.2.1.input_mem_of_pairMember h)
    exact (hs.2.2.2 a c b hc h).2.1

theorem split_grow_l (hZF : M.Models ZF) {ω A J U L R a b n m} (hω : M.IsOmega ω)
    (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R) (hn : M.mem n ω) (hm : M.mem m ω)
    (ha : M.IsSetFunctionFromTo I a n ω) (hb : M.IsSetFunctionFromTo I b m ω)
    (h : M.PairMember I a b L ∨ M.PairMember I a b R) : M.mem n m := by
  have sub := split_extend_l I hs h
  have ne : a ≠ b := by
    intro e
    subst b
    rcases h with h | h
    · obtain ⟨c, _, hc⟩ := hs.2.2.1.2.2 a (hs.2.1.input_mem_of_pairMember h)
      have s := hs.2.2.2 a a c h hc
      exact (pin_not_sub_l I hJ s.2.2).1 s.2.1
    · obtain ⟨c, _, hc⟩ := hs.2.1.2.2 a (hs.2.2.1.input_mem_of_pairMember h)
      have s := hs.2.2.2 a c a hc h
      exact (pin_not_sub_l I hJ s.2.2).2 s.1
  have nm : M.MemberSubset n m := fun i hi => (ha.2.2 i hi).elim fun x hx =>
    hb.input_mem_of_pairMember (hx.2.elim fun p hp => ⟨p, hp.1, sub p hp.2⟩)
  rcases (hω.isOrdinal hZF).wellOrder.linear.compare n hn m hm with e | e | e
  · have e := hZF.1.eq_of_same_members n m e
    subst m
    exact (ne (((ds_restrict_iff_l I ha hb.1).mpr sub).eq hZF.1 ((ds_restrict_iff_l I hb hb.1).mpr (fun _ => id)))).elim
  · exact e
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) m (nm m e)).elim

def Pre_d (ω J a x : M.Domain) : Prop := ∃ s t, Fp_d I ω J a s t ∧ M.MemberSubset s x
def pre_m {d} (ω J a x : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (fp_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken a.weaken.weaken (.bound 1) .newest)
  (Formula.subset (.bound 1) x.weaken.weaken)))
derive_free_closed pre_m
theorem pre_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J a x : Term d) :
    Formula.satisfies ρ (pre_m (𝒞 := 𝒞) ω J a x) ↔ Pre_d I (ω.eval ρ) (J.eval ρ) (a.eval ρ) (x.eval ρ) := by
  simp only [pre_m, Pre_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fp_sat_l I hE, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl
theorem pre_iff_l (hE : Extensional M) {ω J a s t x} (hJ : Npair_d I ω J) (h : Fp_d I ω J a s t) :
    Pre_d I ω J a x ↔ M.MemberSubset s x :=
  ⟨fun ⟨_, _, hp, sub⟩ => (fp_unique_l I hE hJ hp h).1 ▸ sub, fun sub => ⟨s, t, h, sub⟩⟩
theorem pre_mono_l (hZF : M.Models ZF) {ω A J a b x} (hA : Fseq_space_d I ω ω A)
    (hJ : Npair_d I ω J) (ha : M.mem a A) (hab : M.MemberSubset a b) (h : Pre_d I ω J b x) : Pre_d I ω J a x := by
  obtain ⟨s, t, hp⟩ := fp_decode_l I hZF hA hJ ha
  obtain ⟨u, v, hq, sub⟩ := h
  exact ⟨s, t, hp, fun p h => sub p (((fp_sub_l I hJ hp hq).mp hab).1 p h)⟩
theorem pre_disjoint_l (hE : Extensional M) {ω J a b x} (hJ : Npair_d I ω J)
    (h : Pin_d I ω J a b) (hx : M.IsSetFunction I x) (ha : Pre_d I ω J a x) (hb : Pre_d I ω J b x) : False := by
  obtain ⟨s, t, u, v, pa, pb, i, c, d, hc, hd, ne⟩ := h
  have hs := (pre_iff_l I hE hJ pa).mp ha
  have ht := (pre_iff_l I hE hJ pb).mp hb
  exact ne (hx.2 i c d (hc.elim fun p hp => ⟨p, hp.1, hs p hp.2⟩) (hd.elim fun p hp => ⟨p, hp.1, ht p hp.2⟩))

def Lc_d (A B x : M.Domain) (P : M.Domain → Prop) : Prop :=
  ∃ s, M.mem s A ∧ M.MemberSubset s x ∧ ∀ y, M.mem y B → M.MemberSubset s y → P y
theorem lc_and_l (hZF : M.Models ZF) {ω A B x} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hx : M.mem x B) {P Q : M.Domain → Prop}
    (h : Lc_d A B x P) (k : Lc_d A B x Q) : Lc_d A B x (fun y => P y ∧ Q y) := by
  obtain ⟨s, hs, hsx, h⟩ := h
  obtain ⟨t, ht, htx, k⟩ := k
  obtain ⟨n, hn, hsf⟩ := (hA s).mp hs
  obtain ⟨m, hm, htf⟩ := (hA t).mp ht
  rcases ds_prefix_compare_l I hZF.1 (hB.1.isOrdinal hZF) hn hm hsf htf ((hB.2 x).mp hx).1 hsx htx with inc | inc
  · exact ⟨t, ht, htx, fun y hy sub => ⟨h y hy (fun p hp => sub p (inc p hp)), k y hy sub⟩⟩
  · exact ⟨s, hs, hsx, fun y hy sub => ⟨h y hy sub, k y hy (fun p hp => sub p (inc p hp))⟩⟩

theorem pre_local_l (hZF : M.Models ZF) {ω A B J a x} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (ha : M.mem a A) (hx : M.mem x B) :
    Lc_d A B x (fun y => Pre_d I ω J a y ↔ Pre_d I ω J a x) := by
  classical
  obtain ⟨s, t, hp⟩ := fp_decode_l I hZF hA hJ ha
  have hs := (fp_type_l I hZF hA hJ hp).2.1
  have ep y := pre_iff_l I hZF.1 hJ (x := y) hp
  by_cases sub : M.MemberSubset s x
  · exact ⟨s, hs, sub, fun y _ hy => (ep y).trans (iff_of_true hy sub) |>.trans (ep x).symm⟩
  · obtain ⟨n, hn, hf⟩ := (hA s).mp hs
    obtain ⟨C, hc⟩ := cyl_exists_l (ZF.modelsKP hZF) B s
    obtain ⟨u, V, hu, hv, hxV, disj⟩ := cyl_outside_l I hZF hB.1 hB.2 hA hn hf hc hx (fun h => sub ((hc x).mp h).2)
    exact ⟨u, hu, ((hv x).mp hxV).2, fun y hy huy => (ep y).trans
      ((iff_of_false (fun h => disj y ⟨(hc y).mpr ⟨hy, h⟩, (hv y).mpr ⟨hy, huy⟩⟩) sub).trans (ep x).symm)⟩

end YesMetaZFC.SetTheory.Descriptive
