import YesMetaZFC.SetTheory.Descriptive.Perfect.Walk

/-! # 规范路径的局部稳定性与闭集解释 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ws_local_l (hZF : M.Models ZF) {ω A B J U L R a b x} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R)
    (ha : M.mem a U) (hx : M.mem x B) (h : Ws_d I ω J L R a b x) : Lc_d A B x (fun y => Ws_d I ω J L R a b y) := by
  obtain ⟨c, hc, hac⟩ := hs.2.1.2.2 a ha
  have hit y : Hit_d I ω J L a y ↔ Pre_d I ω J c y :=
    ⟨fun ⟨d, hd, hy⟩ => hs.2.1.1.2 a d c hd hac ▸ hy, fun hy => ⟨c, hac, hy⟩⟩
  obtain ⟨s, hsa, sub, obs⟩ := pre_local_l I hZF hB hA hJ (hs.1 c hc) hx
  refine ⟨s, hsa, sub, fun y hy hyS => ?_⟩
  have eqn := (hit y).trans ((obs y hy hyS).trans (hit x).symm)
  exact h.elim (fun h => Or.inl ⟨eqn.mpr h.1, h.2⟩) (fun h => Or.inr ⟨fun hh => h.1 (eqn.mp hh), h.2⟩)

def wloc_m {d} (ω A B J U L R a n b x : Term d) : Formula 1 d := Formula.existsMem A (.conj
  (Formula.subset .newest x.weaken) (Formula.forallMem B.weaken (.imp (Formula.subset (.bound 1) .newest)
  (walk_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken U.weaken.weaken L.weaken.weaken R.weaken.weaken
    a.weaken.weaken n.weaken.weaken b.weaken.weaken .newest))))
derive_free_closed wloc_m
theorem wloc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J U L R a n b x : Term d) :
    Formula.satisfies ρ (wloc_m (𝒞 := 𝒞) ω A B J U L R a n b x) ↔ Lc_d (A.eval ρ) (B.eval ρ) (x.eval ρ)
      (fun y => Walk_d I (ω.eval ρ) (J.eval ρ) (U.eval ρ) (L.eval ρ) (R.eval ρ) (a.eval ρ) (n.eval ρ) (b.eval ρ) y) := by
  simp only [wloc_m, Lc_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    walk_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem walk_local_l (hZF : M.Models ZF) {ω A B J U L R a} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R) (ha : M.mem a U) :
    ∀ n, M.mem n ω → ∀ b x, M.mem x B → Walk_d I ω J U L R a n b x → Lc_d A B x (fun y => Walk_d I ω J U L R a n b y) := by
  let ρ : Env M 8 := (((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push U).push L).push R).push a
  let φ : UnarySchema 8 := { body := .forallE (.forallE (.imp (.mem .newest (.bound 8)) (.imp
    (walk_m (𝒞 := 𝒞) (.bound 10) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (wloc_m (𝒞 := 𝒞) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)))) }
  have hp n : φ.denote ρ n ↔ ∀ b x, M.mem x B → Walk_d I ω J U L R a n b x → Lc_d A B x (fun y => Walk_d I ω J U L R a n b y) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, walk_sat_l I hZF.1, wloc_sat_l I hZF.1]; rfl
  apply hB.1.induction
  · obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨D, fun n => (hd n).trans (and_congr_right fun _ => hp n)⟩
  · intro z hz b x _ hb
    have e := (walk_zero_l I hZF hB.1 hs ha hz).mp hb
    obtain ⟨o, ho, hoω⟩ := hB.1.1.1
    exact ⟨o, (hA o).mpr ⟨o, hoω, ds_empty_fun_l I ho⟩, fun p hp => (ho p hp).elim,
      fun y _ _ => (walk_zero_l I hZF hB.1 hs ha hz).mpr e⟩
  · intro n hn ih m hm b x hx hb
    obtain ⟨c, hc, step⟩ := (walk_succ_l I hZF hB.1 hn hm).mp hb
    obtain ⟨s, hsA, sub, obs⟩ := lc_and_l I hZF hB hA hx (ih c x hx hc)
      (ws_local_l I hZF hB hA hJ hs (walk_bound_l I hc) hx step)
    exact ⟨s, hsA, sub, fun y hy hsy => (walk_succ_l I hZF hB.1 hn hm).mpr ⟨c, (obs y hy hsy).1, (obs y hy hsy).2⟩⟩

def Pw_d (ω J U L R a x : M.Domain) : Prop := ∀ n b, M.mem n ω → Walk_d I ω J U L R a n b x → Pre_d I ω J b x
def pw_m {d} (ω J U L R a x : Term d) : Formula 1 d := Formula.forallMem ω (.forallE (.imp
  (walk_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken U.weaken.weaken L.weaken.weaken R.weaken.weaken a.weaken.weaken (.bound 1) .newest x.weaken.weaken)
  (pre_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken .newest x.weaken.weaken)))
derive_free_closed pw_m
theorem pw_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J U L R a x : Term d) :
    Formula.satisfies ρ (pw_m (𝒞 := 𝒞) ω J U L R a x) ↔
      Pw_d I (ω.eval ρ) (J.eval ρ) (U.eval ρ) (L.eval ρ) (R.eval ρ) (a.eval ρ) (x.eval ρ) := by
  simp only [pw_m, Pw_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, walk_sat_l I hE, pre_sat_l I hE, Definitional.Term.eval_weaken]
  exact ⟨fun h n b hn => h n hn b, fun h n hn b => h n b hn⟩

theorem pw_closed_l (hZF : M.Models ZF) {ω A B J U L R a} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R) (ha : M.mem a U) :
    ∃ P, Cl_d A B P ∧ ∀ x, M.mem x P ↔ M.mem x B ∧ Pw_d I ω J U L R a x := by
  classical
  let ρ : Env M 6 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push U).push L).push R).push a
  let φ : UnarySchema 6 := { body := pw_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨P, hp'⟩ := ZF.separation_exists_d hZF φ ρ B
  have hp x : M.mem x P ↔ M.mem x B ∧ Pw_d I ω J U L R a x :=
    (hp' x).trans (and_congr_right fun _ => pw_sat_l I hZF.1 _ _ _ _ _ _ _ _)
  obtain ⟨V, hv⟩ := cm_exists_l (ZF.modelsKP hZF) B P
  refine ⟨P, ⟨fun x hx => ((hp x).mp hx).1, V, hv, ⟨fun x hx => ((hv x).mp hx).1, fun x hx => ?_⟩⟩, hp⟩
  obtain ⟨hxB, hxP⟩ := (hv x).mp hx
  obtain ⟨n, b, hn, hb, bad⟩ : ∃ n b, M.mem n ω ∧ Walk_d I ω J U L R a n b x ∧ ¬ Pre_d I ω J b x := by
    exact Classical.byContradiction (fun h => hxP ((hp x).mpr ⟨hxB, fun n b hn hb =>
      Classical.byContradiction (fun bad => h ⟨n, b, hn, hb, bad⟩)⟩))
  obtain ⟨s, hsA, sub, obs⟩ := lc_and_l I hZF hB hA hxB (walk_local_l I hZF hB hA hJ hs ha n hn b x hxB hb)
    (pre_local_l I hZF hB hA hJ (hs.1 b (walk_bound_l I hb)) hxB)
  exact ⟨s, hsA, sub, fun y hy hsy => (hv y).mpr ⟨hy, fun hyP =>
    bad ((obs y hy hsy).2.mp (((hp y).mp hyP).2 n b hn (obs y hy hsy).1))⟩⟩

end YesMetaZFC.SetTheory.Descriptive
