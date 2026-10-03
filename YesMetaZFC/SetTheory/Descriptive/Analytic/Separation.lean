import YesMetaZFC.SetTheory.Descriptive.Analytic.SeparationRecursion

/-! # Lusin 分离：不交解析集有实际 Borel 分离码 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def As_d (A B J T a x : M.Domain) : Prop := ∃ y p,
  M.mem y B ∧ M.mem p B ∧ Rp_d I J x y p ∧ Branch_d A T p ∧ M.MemberSubset a p
def as_m {d} (A B J T a x : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (.mem (.bound 1) B.weaken.weaken) (.conj (.mem .newest B.weaken.weaken) (.conj
  (rp_m (𝒞 := 𝒞) J.weaken.weaken x.weaken.weaken (.bound 1) .newest) (.conj
  (branch_m A.weaken.weaken T.weaken.weaken .newest) (Formula.subset a.weaken.weaken .newest))))))
derive_free_closed as_m
theorem as_sat_l {d} (ρ : Env M d) (A B J T a x : Term d) :
    Formula.satisfies ρ (as_m (𝒞 := 𝒞) A B J T a x) ↔
      As_d I (A.eval ρ) (B.eval ρ) (J.eval ρ) (T.eval ρ) (a.eval ρ) (x.eval ρ) := by
  simp only [as_m, As_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rp_sat_l I, branch_sat_l, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

theorem as_child_l (hZF : M.Models ZF) {ω A B J T a x} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.mem a A) (h : As_d I A B J T a x) :
    ∃ b, M.mem b T ∧ Step_d I ω a b ∧ As_d I A B J T b x := by
  obtain ⟨y, p, hy, hp, pair, path, sub⟩ := h
  have hf := (hB.2 p).mp hp
  obtain ⟨n, hn, haf⟩ := (hA a).mp ha
  obtain ⟨m, hm, hmω⟩ := hB.1.1.2 n hn
  obtain ⟨b, hbf, hb, _⟩ := ds_prefix_l I hZF hB.1 hf hmω
  have hbp := (ds_restrict_iff_l I hbf hf.1).mp hb
  have hab := ds_prefix_mono_l I haf hbf.1 ((ds_restrict_iff_l I haf hf.1).mpr sub) hb
    (fun i hi => (hm i).mpr (Or.inl hi))
  exact ⟨b, path b ((hA b).mpr ⟨m, hmω, hbf⟩) hbp,
    (tree_step_iff_l I hZF hB.1 hn hmω haf hbf).mpr ⟨hm, hab⟩, y, p, hy, hp, pair, path, hbp⟩

theorem as_prefix_l {ω A B J T a s t x} (hJ : Npair_d I ω J) (h : Fp_d I ω J a s t)
    (ha : As_d I A B J T a x) : M.MemberSubset s x := by
  obtain ⟨_, _, hs, ht, hp⟩ := h
  obtain ⟨_, _, _, _, pair, _, sub⟩ := ha
  exact ((rp_subset_l I hJ hs ht hp pair).mp sub).1

theorem as_root_l {A B J T K z} (h : Atree_d I A B J T K) (hz : ∀ p, ¬ M.mem p z) (x : M.Domain) :
    M.mem x K ↔ M.mem x B ∧ As_d I A B J T z x := by
  obtain ⟨_, C, hc, hk⟩ := h
  exact (hk x).trans (and_congr_right fun _ => ⟨fun ⟨y, p, hy, hp, pair, hpc⟩ =>
    ⟨y, p, hy, hp, pair, ((hc p).mp hpc).2, fun p hp => (hz p hp).elim⟩,
    fun ⟨y, p, hy, hp, pair, path, _⟩ => ⟨y, p, hy, hp, pair, (hc p).mpr ⟨hp, path⟩⟩⟩)

def Bsep_d (ω A B J T U a b c : M.Domain) : Prop := ∀ x, M.mem x B →
  (As_d I A B J T a x → Bsat_d I ω A A c x) ∧ (As_d I A B J U b x → ¬ Bsat_d I ω A A c x)
def bsep_m {d} (ω A B J T U a b c : Term d) : Formula 1 d := Formula.forallMem B (.conj
  (.imp (as_m (𝒞 := 𝒞) A.weaken B.weaken J.weaken T.weaken a.weaken .newest)
    (bsat_m (𝒞 := 𝒞) ω.weaken A.weaken A.weaken c.weaken .newest))
  (.imp (as_m (𝒞 := 𝒞) A.weaken B.weaken J.weaken U.weaken b.weaken .newest)
    (.neg (bsat_m (𝒞 := 𝒞) ω.weaken A.weaken A.weaken c.weaken .newest))))
derive_free_closed bsep_m
theorem bsep_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J T U a b c : Term d) :
    Formula.satisfies ρ (bsep_m (𝒞 := 𝒞) ω A B J T U a b c) ↔
      Bsep_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (T.eval ρ) (U.eval ρ) (a.eval ρ) (b.eval ρ) (c.eval ρ) := by
  simp only [bsep_m, Bsep_d, Formula.satisfies_forallMem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_imp_iff, as_sat_l I, bsat_sat_l I hE, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]; rfl

theorem separation_code_l (hZF : M.Models ZF) {ω A B J T U K L} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hT : Atree_d I A B J T K) (hU : Atree_d I A B J U L) (hKL : M.IsDisjoint K L) :
    ∃ c, Bcode_d I ω A A c ∧ (∀ x, M.mem x K → Bsat_d I ω A A c x) ∧
      ∀ x, M.mem x L → ¬ Bsat_d I ω A A c x := by
  classical
  obtain ⟨X, R, E, G, hX, hw, er, he, hg, total, step⟩ := separation_recursion_l I hZF hB hA ha hJ hT hU hKL
  let ρ : Env M 7 := ((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push T).push U).push G
  let φ : UnarySchema 7 := { body := .forallE (.forallE (.forallE (.imp
    (fp_m (𝒞 := 𝒞) (.bound 10) (.bound 7) (.bound 3) (.bound 2) (.bound 1)) (.imp
    (Formula.orderedPairMem 𝒞 (.bound 3) .newest (.bound 4))
    (bsep_m (𝒞 := 𝒞) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 2) (.bound 1) .newest))))) }
  have hp r : φ.denote ρ r ↔ ∀ a b c, Fp_d I ω J r a b → M.PairMember I r c G → Bsep_d I ω A B J T U a b c := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      fp_sat_l I hZF.1, Formula.satisfies_orderedPairMem_iff I, bsep_sat_l I hZF.1]; rfl
  have all := wf_rel_ind_l hZF hw φ ρ (fun r hr ih => (hp r).mpr (by
    intro a b c pr hc x hx
    obtain ⟨u, v, pr', hu, hv⟩ := (hX r).mp hr
    obtain ⟨eu, ev⟩ := fp_unique_l I hZF.1 hJ pr' pr
    subst u v
    obtain ⟨u, v, pr', sc⟩ := (step r c hc).2
    obtain ⟨eu, ev⟩ := fp_unique_l I hZF.1 hJ pr' pr
    subst u v
    rcases sc with ⟨cp, sc⟩ | ⟨cp, s, t, ps, sc⟩
    · have child {u v q} (hu : M.mem u T) (su : Step_d I ω a u) (hv : M.mem v U)
          (sv : Step_d I ω b v) (pq : Fp_d I ω J q u v) : M.mem q X ∧ Rd_entry_d q r R := by
        have hq := (hX q).mpr ⟨u, v, pq, hu, hv⟩
        exact ⟨hq, (er q r).mpr ⟨hq, hr, cp, (fp_step_l I hZF hB.1 hJ pr pq).mpr ⟨su, sv⟩⟩⟩
      obtain ⟨d, hd, _, dv⟩ := sm_exists_l I hZF hB.1 hA he hg hT.1.1 hU.1.1
        (fun _ _ _ d _ _ _ _ _ hd => (step _ d hd).1)
      have cv x := (sm_unique_l I hZF.1 hd sc ▸ dv) x
      constructor
      · intro ax
        obtain ⟨u, hu', su, ux⟩ := as_child_l I hZF hB hA (hT.1.1 a hu) ax
        apply (cv x).mpr
        refine ⟨u, hu', su, fun v q d hv sv pq hd => ?_⟩
        have edge := child hu' su hv sv pq
        exact ((hp q).mp (ih q edge.1 edge.2) u v d pq hd x hx).1 ux
      · intro bx cx
        obtain ⟨u, hu', su, ux⟩ := (cv x).mp cx
        obtain ⟨v, hv', sv, vx⟩ := as_child_l I hZF hB hA (hU.1.1 b hv) bx
        obtain ⟨q, pq, _⟩ := fp_child_l I hZF hB.1 hA hJ pr (hT.1.1 u hu') (hU.1.1 v hv') su sv
        have edge := child hu' su hv' sv pq
        obtain ⟨d, hd⟩ := total q edge.1
        exact ((hp q).mp (ih q edge.1 edge.2) u v d pq hd x hx).2 vx (ux v q d hv' sv pq hd)
    · have cv := (bbasic_correct_l I hZF hB.1 hA (fp_type_l I hZF hA hJ ps).2.1 sc).2
      refine ⟨fun ax => (cv x).mpr (as_prefix_l I hJ ps ax), fun bx cx => ?_⟩
      obtain ⟨v, w, pv⟩ := fp_decode_l I hZF hA hJ (hU.1.1 b hv)
      obtain ⟨n, hn, haf, hbf, _⟩ := pr
      have hs := (fp_at_l I hZF hJ ps haf).1
      have hvf := (fp_at_l I hZF hJ pv hbf).1
      have e := ((ds_restrict_iff_l I hs ((hB.2 x).mp hx).1).mpr ((cv x).mp cx)).eq hZF.1
        ((ds_restrict_iff_l I hvf ((hB.2 x).mp hx).1).mpr (as_prefix_l I hJ pv bx))
      exact cp ⟨a, b, s, t, w, ⟨n, hn, haf, hbf, ‹Rp_d I J a b r›⟩, ps, e.symm ▸ pv⟩))
  obtain ⟨z, hz, hzω⟩ := hB.1.1.1
  have hzA := (hA z).mpr ⟨z, hzω, ds_empty_fun_l I hz⟩
  have empty_sub (p : M.Domain) : M.MemberSubset z p := fun q hq => (hz q hq).elim
  have absent {T K} (ht : Atree_d I A B J T K) (hn : ¬ M.mem z T) : ∀ x, ¬ M.mem x K := by
    intro x hx
    obtain ⟨_, _, p, _, _, _, path, _⟩ := (as_root_l I ht hz x).mp hx
    exact hn (path z hzA (empty_sub p))
  by_cases ht : M.mem z T
  · by_cases hu : M.mem z U
    · have pz : Fp_d I ω J z z z := ⟨z, hzω, ds_empty_fun_l I hz, ds_empty_fun_l I hz,
        (ds_empty_fun_l I (X := ω) hz).1.1, fun i v => iff_of_false
          (fun ⟨p, _, hp⟩ => hz p hp) (fun ⟨_, _, ⟨p, _, hp⟩, _⟩ => hz p hp)⟩
      obtain ⟨c, hc⟩ := total z ((hX z).mpr ⟨z, z, pz, ht, hu⟩)
      have val := (hp z).mp (all z ((hX z).mpr ⟨z, z, pz, ht, hu⟩)) z z c pz hc
      exact ⟨c, (step z c hc).1, fun x hx => (val x ((as_root_l I hT hz x).mp hx).1).1 ((as_root_l I hT hz x).mp hx).2,
        fun x hx => (val x ((as_root_l I hU hz x).mp hx).1).2 ((as_root_l I hU hz x).mp hx).2⟩
    · obtain ⟨c, hc⟩ := bbasic_exists_l I (ZF.modelsKP hZF) z
      have val := bbasic_correct_l I hZF hB.1 hA hzA hc
      exact ⟨c, val.1, fun x _ => (val.2 x).mpr (empty_sub x), fun x hx => (absent hU hu x hx).elim⟩
  · obtain ⟨c, hc, cv⟩ := bcode_empty_l I hZF (S := A) hB.1 hA
    exact ⟨c, hc, fun x hx => (absent hT ht x hx).elim, fun x _ => cv x⟩

/-- 分离结论返回模型中的实际集合及其 Borel 码。 -/
theorem an_separation_l (hZF : M.Models ZF) {ω A B J K L} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hK : An_d I ω A B J K) (hL : An_d I ω A B J L) (hKL : M.IsDisjoint K L) :
    ∃ C, Borel_d I ω A A B C ∧ M.MemberSubset K C ∧ M.IsDisjoint C L := by
  obtain ⟨T, hT⟩ := (an_tree_iff_l I hZF hB hA ha hJ).mp hK
  obtain ⟨U, hU⟩ := (an_tree_iff_l I hZF hB hA ha hJ).mp hL
  obtain ⟨c, hc, hk, hl⟩ := separation_code_l I hZF hB hA ha hJ hT hU hKL
  obtain ⟨C, hC, _⟩ := bden_exists_unique_l I hZF ω A A B c
  have bound x (hx : M.mem x K) := ((an_proj_l I).mp hK).elim fun _ h => ((h.2 x).mp hx).1
  exact ⟨C, ⟨c, hc, hC⟩, fun x hx => (hC x).mpr ⟨bound x hx, hk x hx⟩,
    fun x ⟨hx, hy⟩ => hl x hy ((hC x).mp hx).2⟩

end YesMetaZFC.SetTheory.Descriptive
