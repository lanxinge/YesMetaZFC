import YesMetaZFC.SetTheory.Descriptive.Perfect.Fusion

/-! # 分裂路径的实现及有限初段拼接 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem pw_pre_l (hZF : M.Models ZF) {ω A J U L R a x} (hω : M.IsOmega ω)
    (hs : Split_d I ω A J U L R) (ha : M.mem a U) (h : Pw_d I ω J U L R a x) : Pre_d I ω J a x := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  exact h z a hzω ((walk_zero_l I hZF hω hs ha hz).mpr rfl)

theorem ws_of_pre_l (hE : Extensional M) {ω A J U L R a b x} (hJ : Npair_d I ω J)
    (hs : Split_d I ω A J U L R) (hx : M.IsSetFunction I x)
    (hc : M.PairMember I a b L ∨ M.PairMember I a b R) (hb : Pre_d I ω J b x) : Ws_d I ω J L R a b x := by
  rcases hc with hc | hc
  · exact Or.inl ⟨⟨b, hc, hb⟩, hc⟩
  · exact Or.inr ⟨fun ⟨c, hL, hp⟩ => pre_disjoint_l I hE hJ (hs.2.2.2 a c b hL hc).2.2 hx hp hb, hc⟩

theorem pw_prepend_l (hZF : M.Models ZF) {ω A B J U L R a b x} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R)
    (hx : M.mem x B) (child : M.PairMember I a b L ∨ M.PairMember I a b R)
    (h : Pw_d I ω J U L R b x) : Pw_d I ω J U L R a x := by
  classical
  have ha := child.elim hs.2.1.input_mem_of_pairMember hs.2.2.1.input_mem_of_pairMember
  have hb := child.elim hs.2.1.output_mem_of_pairMember hs.2.2.1.output_mem_of_pairMember
  have pb := pw_pre_l I hZF hB.1 hs hb h
  have pa := pre_mono_l I hZF hA hJ (hs.1 a ha) (split_extend_l I hs child) pb
  obtain ⟨F, hf⟩ := sel_exists_l I hZF hs x
  have first := (hf.2 a b).mpr ⟨ha, ws_of_pre_l I hZF.1 hJ hs ((hB.2 x).mp hx).1 child pb⟩
  intro n c hn hc
  have val := (walk_fixed_l I hZF.1 hf).mp hc
  by_cases he : ∀ i, ¬ M.mem i n
  · exact (iv_zero_l I hZF hB.1 hf.1 ha he).mp val |>.symm ▸ pa
  · have ne : ∃ i, M.mem i n := Classical.byContradiction (fun h => he (fun i hi => h ⟨i, hi⟩))
    obtain ⟨k, hk, hnk⟩ := hB.1.exists_predecessor_of_mem_of_nonempty hZF hn ne
    exact h k c hk ((walk_fixed_l I hZF.1 hf).mpr ((iv_shift_l I hZF hB.1 hf.1 hk hnk first).mp val))

theorem pw_ancestor_l (hZF : M.Models ZF) {ω A B J U L R a} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R) (ha : M.mem a U) :
    ∀ n, M.mem n ω → ∀ b x y, M.mem y B → Walk_d I ω J U L R a n b x →
      Pw_d I ω J U L R b y → Pw_d I ω J U L R a y := by
  let ρ : Env M 7 := ((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push B).push J).push U).push L).push R).push a
  let φ : UnarySchema 7 := { body := .forallE (.forallE (.forallE (.imp (.mem .newest (.bound 9)) (.imp
    (walk_m (𝒞 := 𝒞) (.bound 10) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1)) (.imp
    (pw_m (𝒞 := 𝒞) (.bound 10) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 2) .newest)
    (pw_m (𝒞 := 𝒞) (.bound 10) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) .newest)))))) }
  have hp n : φ.denote ρ n ↔ ∀ b x y, M.mem y B → Walk_d I ω J U L R a n b x →
      Pw_d I ω J U L R b y → Pw_d I ω J U L R a y := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, walk_sat_l I hZF.1, pw_sat_l I hZF.1]; rfl
  apply hB.1.induction
  · obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨D, fun n => (hd n).trans (and_congr_right fun _ => hp n)⟩
  · intro z hz b x y _ hb h
    exact (walk_zero_l I hZF hB.1 hs ha hz).mp hb ▸ h
  · intro n hn ih m hm b x y hy hb h
    obtain ⟨c, hc, step⟩ := (walk_succ_l I hZF hB.1 hn hm).mp hb
    exact ih c x y hy hc (pw_prepend_l I hZF hB hA hJ hs hy (step.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)) h)

theorem pw_nonempty_l (hZF : M.Models ZF) {ω A B J U L R a} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R) (ha : M.mem a U) :
    ∃ x, M.mem x B ∧ Pw_d I ω J U L R a x := by
  obtain ⟨H, hh, hz, next⟩ := ZFC.iterate_l I hZF hB.1 hs.2.1 ha
  have it : It_d I ω U L a H := ⟨hh, hz, next⟩
  obtain ⟨f, ff, union, _⟩ := split_fusion_l I hZF hB.1 hA hJ hs it (fun _ _ h => Or.inl h)
  obtain ⟨x, y, hx, hy, pair⟩ := rp_decode_l I hZF hJ ff
  have pre n b (hb : M.PairMember I n b H) : Pre_d I ω J b x := by
    obtain ⟨s, t, hp⟩ := fp_decode_l I hZF hA hJ (hs.1 b (hh.output_mem_of_pairMember hb))
    obtain ⟨m, hm, sf, tf, hp'⟩ := hp
    exact ⟨s, t, ⟨m, hm, sf, tf, hp'⟩, ((rp_subset_l I hJ sf tf hp' pair).mp (fun p hp => (union p).mpr ⟨n, b, hb, hp⟩)).1⟩
  obtain ⟨F, hf⟩ := sel_exists_l I hZF hs x
  have walk : It_d I ω U F a H := ⟨hh, hz, fun n m b c hm hb hc =>
    (hf.2 b c).mpr ⟨hh.output_mem_of_pairMember hb, Or.inl ⟨⟨c, next n m b c hm hb hc, pre m c hc⟩, next n m b c hm hb hc⟩⟩⟩
  refine ⟨x, (hB.2 x).mpr hx, fun n b hn hb => ?_⟩
  obtain ⟨c, _, hc⟩ := hh.2.2 n hn
  have e := iv_unique_l I hZF hB.1 hf.1.1 ((walk_fixed_l I hZF.1 hf).mp hb) ⟨H, walk, hc⟩
  exact e.symm ▸ pre n c hc

theorem pw_realize_l (hZF : M.Models ZF) {ω A B J U L R T a x} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R) (ha : M.mem a U)
    (hT : Tree_d A T) (sub : M.MemberSubset U T) (hx : M.mem x B) (h : Pw_d I ω J U L R a x) :
    ∃ y p, M.mem y B ∧ M.mem p B ∧ Rp_d I J x y p ∧ Branch_d A T p := by
  obtain ⟨F, hf⟩ := sel_exists_l I hZF hs x
  obtain ⟨H, hh, hz, next⟩ := ZFC.iterate_l I hZF hB.1 hf.1 ha
  have it : It_d I ω U F a H := ⟨hh, hz, next⟩
  have step b c (hb : M.PairMember I b c F) := ((hf.2 b c).mp hb).2.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  obtain ⟨p, pf, union, cover⟩ := split_fusion_l I hZF hB.1 hA hJ hs it step
  obtain ⟨v, y, vf, yf, pair⟩ := rp_decode_l I hZF hJ pf
  have e := fusion_projection_l I hZF hA hJ hs.1 hh union ((hB.2 x).mp hx) yf vf pair
    (fun n b hb => h n b (hh.input_mem_of_pairMember hb) ⟨F, hf, H, it, hb⟩)
  subst v
  refine ⟨y, p, (hB.2 y).mpr yf, (hB.2 p).mpr pf, pair, fun s hsA hsp => ?_⟩
  obtain ⟨n, b, hb, hsb⟩ := cover s hsA hsp
  exact hT.2 b (sub b (hh.output_mem_of_pairMember hb)) s hsA hsb

end YesMetaZFC.SetTheory.Descriptive
