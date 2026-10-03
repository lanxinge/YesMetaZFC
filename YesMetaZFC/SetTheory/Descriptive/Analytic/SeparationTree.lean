import YesMetaZFC.SetTheory.Descriptive.Analytic.NormalForm
import YesMetaZFC.SetTheory.Descriptive.RealPair.Finite
import YesMetaZFC.SetTheory.Descriptive.TreeWellFounded

/-! # 解析分离的同步乘积树

节点编码 ((s,u),(t,v))。s=t 的节点继续向下递归，s≠t 的节点终止。
若两投影不交，同步兼容子树无内部无限分支，因而递归关系内部良基。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Cp_d (ω J r : M.Domain) : Prop := ∃ a b s t v,
  Fp_d I ω J r a b ∧ Fp_d I ω J a s t ∧ Fp_d I ω J b s v
def cp_m {d} (ω J r : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (fp_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken J.weaken.weaken.weaken.weaken.weaken r.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3)) (.conj
  (fp_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken J.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 2) (.bound 1))
  (fp_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken J.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) .newest)))))))
derive_free_closed cp_m
theorem cp_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J r : Term d) :
    Formula.satisfies ρ (cp_m (𝒞 := 𝒞) ω J r) ↔ Cp_d I (ω.eval ρ) (J.eval ρ) (r.eval ρ) := by
  simp only [cp_m, Cp_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fp_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Stn_d (ω J T U r : M.Domain) : Prop := ∃ a b, Fp_d I ω J r a b ∧ M.mem a T ∧ M.mem b U
def stn_m {d} (ω J T U r : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (fp_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken r.weaken.weaken (.bound 1) .newest)
  (.conj (.mem (.bound 1) T.weaken.weaken) (.mem .newest U.weaken.weaken))))
derive_free_closed stn_m
theorem stn_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J T U r : Term d) :
    Formula.satisfies ρ (stn_m (𝒞 := 𝒞) ω J T U r) ↔
      Stn_d I (ω.eval ρ) (J.eval ρ) (T.eval ρ) (U.eval ρ) (r.eval ρ) := by
  simp only [stn_m, Stn_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fp_sat_l I hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

theorem cp_prefix_l (hZF : M.Models ZF) {ω A J r q} (hA : Fseq_space_d I ω ω A)
    (hJ : Npair_d I ω J) (hr : M.mem r A) (hq : Cp_d I ω J q) (hrq : M.MemberSubset r q) : Cp_d I ω J r := by
  obtain ⟨a, b, s, t, v, hq, ha, hb⟩ := hq
  obtain ⟨c, d, hp⟩ := fp_decode_l I hZF hA hJ hr
  obtain ⟨x, y, hx⟩ := fp_decode_l I hZF hA hJ (fp_type_l I hZF hA hJ hp).2.1
  obtain ⟨z, w, hz⟩ := fp_decode_l I hZF hA hJ (fp_type_l I hZF hA hJ hp).2.2
  obtain ⟨n, _, hrf⟩ := (hA r).mp hr
  have hc := fp_at_l I hZF hJ hp hrf
  have hxf := (fp_at_l I hZF hJ hx hc.1).1
  have hzf := (fp_at_l I hZF hJ hz hc.2.1).1
  have inc := (fp_sub_l I hJ hp hq).mp hrq
  have hxs := ((fp_sub_l I hJ hx ha).mp inc.1).1
  have hzs := ((fp_sub_l I hJ hz hb).mp inc.2).1
  obtain ⟨_, _, hsf, _, _⟩ := ha
  have e := ((ds_restrict_iff_l I hxf hsf.1).mpr hxs).eq hZF.1 ((ds_restrict_iff_l I hzf hsf.1).mpr hzs)
  exact ⟨c, d, x, y, w, hp, hx, e.symm ▸ hz⟩

theorem stn_tree_l (hZF : M.Models ZF) {ω A J T U X} (hA : Fseq_space_d I ω ω A)
    (hJ : Npair_d I ω J) (hT : Tree_d A T) (hU : Tree_d A U)
    (hX : ∀ r, M.mem r X ↔ Stn_d I ω J T U r) : Tree_d A X := by
  refine ⟨fun r hr => ((hX r).mp hr).elim fun a h => h.elim fun b h => (fp_type_l I hZF hA hJ h.1).1, ?_⟩
  intro r hr q hq hqr
  obtain ⟨a, b, hp, ha, hb⟩ := (hX r).mp hr
  obtain ⟨c, d, hpair⟩ := fp_decode_l I hZF hA hJ hq
  have inc := (fp_sub_l I hJ hpair hp).mp hqr
  have ty := fp_type_l I hZF hA hJ hpair
  exact (hX q).mpr ⟨c, d, hpair, hT.2 a ha c ty.2.1 inc.1, hU.2 b hb d ty.2.2 inc.2⟩

/-- 同步兼容树的分支恰会给出两投影共有的实数。 -/
theorem stn_no_branch_l (hZF : M.Models ZF) {ω A B J T U K L Q} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hT : Atree_d I A B J T K) (hU : Atree_d I A B J U L)
    (hKL : M.IsDisjoint K L) (hQ : ∀ r, M.mem r Q ↔ Stn_d I ω J T U r ∧ Cp_d I ω J r) :
    ∀ f, M.mem f B → ¬ Branch_d A Q f := by
  intro f hf path
  obtain ⟨a, b, haf, hbf, hp⟩ := rp_decode_l I hZF hJ ((hB.2 f).mp hf)
  obtain ⟨x, y, hxf, hyf, hx⟩ := rp_decode_l I hZF hJ haf
  obtain ⟨z, w, hzf, hwf, hz⟩ := rp_decode_l I hZF hJ hbf
  have pref n (hn : M.mem n ω) : ∃ c d s,
      M.IsSetFunctionFromTo I c n ω ∧ M.IsSetFunctionFromTo I d n ω ∧
      M.IsSetFunctionFromTo I s n ω ∧ M.mem c T ∧ M.mem d U ∧
      M.MemberSubset c a ∧ M.MemberSubset d b ∧ M.MemberSubset s x ∧ M.MemberSubset s z := by
    obtain ⟨r, hrf, hr, _⟩ := ds_prefix_l I hZF hB.1 ((hB.2 f).mp hf) hn
    have hq := (hQ r).mp (path r ((hA r).mpr ⟨n, hn, hrf⟩) ((ds_restrict_iff_l I hrf ((hB.2 f).mp hf).1).mp hr))
    obtain ⟨c, d, s, t, v, hrp, hc, hd⟩ := hq.2
    obtain ⟨u, v', hruv, hu, hv⟩ := hq.1
    obtain ⟨eu, ev⟩ := fp_unique_l I hZF.1 hJ hruv hrp
    subst u v'
    have ht := fp_at_l I hZF hJ hrp hrf
    have hst := fp_at_l I hZF hJ hc ht.1
    have hsv := fp_at_l I hZF hJ hd ht.2.1
    have sub := (rp_subset_l I hJ ht.1 ht.2.1 ht.2.2 hp).mp ((ds_restrict_iff_l I hrf ((hB.2 f).mp hf).1).mp hr)
    exact ⟨c, d, s, ht.1, ht.2.1, hst.1, hu, hv, sub.1, sub.2,
      ((rp_subset_l I hJ hst.1 hst.2.1 hst.2.2 hx).mp sub.1).1,
      ((rp_subset_l I hJ hsv.1 hsv.2.1 hsv.2.2 hz).mp sub.2).1⟩
  have eqn : x = z := by
    apply Classical.byContradiction
    intro ne
    obtain ⟨i, c, d, hi, hc, hd, hcd⟩ := ds_differ_l I hZF.1 hxf hzf ne
    obtain ⟨n, hn, hnω⟩ := hB.1.1.2 i hi
    obtain ⟨_, _, s, _, _, hs, _, _, _, _, hsx, hsz⟩ := pref n hnω
    obtain ⟨v, _, hv⟩ := hs.2.2 i hn.predecessor_mem
    have lift {F} (h : M.MemberSubset s F) : M.PairMember I i v F := hv.elim fun p hp => ⟨p, hp.1, h p hp.2⟩
    exact hcd ((hxf.1.2 i c v hc (lift hsx)).trans (hzf.1.2 i v d (lift hsz) hd))
  have haT : Branch_d A T a := (tree_branch_l I hZF hB.1 hA haf).mpr (fun n hn => by
    obtain ⟨c, _, _, hc, _, _, hcT, _, hca, _⟩ := pref n hn
    exact ⟨c, hcT, (ds_restrict_iff_l I hc haf.1).mpr hca⟩)
  have hbU : Branch_d A U b := (tree_branch_l I hZF hB.1 hA hbf).mpr (fun n hn => by
    obtain ⟨_, d, _, _, hd, _, _, hdU, _, hdb, _⟩ := pref n hn
    exact ⟨d, hdU, (ds_restrict_iff_l I hd hbf.1).mpr hdb⟩)
  have left := (atree_mem_l I hZF hB hA hJ hT x).mpr ⟨(hB.2 x).mpr hxf, y, (hB.2 y).mpr hyf,
    (tpath_branch_l I hZF hB.1 hA hJ hxf hyf hx).mp haT⟩
  have right := (atree_mem_l I hZF hB hA hJ hU z).mpr ⟨(hB.2 z).mpr hzf, w, (hB.2 w).mpr hwf,
    (tpath_branch_l I hZF hB.1 hA hJ hzf hwf hz).mp hbU⟩
  exact hKL x ⟨left, eqn.symm ▸ right⟩

theorem separation_relation_l (hZF : M.Models ZF) {ω A B J T U K L} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hT : Atree_d I A B J T K) (hU : Atree_d I A B J U L) (hKL : M.IsDisjoint K L) :
    ∃ X R, (∀ r, M.mem r X ↔ Stn_d I ω J T U r) ∧ Wf_rel_d X R ∧
      ∀ q r, Rd_entry_d q r R ↔ M.mem q X ∧ M.mem r X ∧ Cp_d I ω J r ∧ Step_d I ω r q := by
  classical
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push T).push U
  let φ : UnarySchema 4 := { body := stn_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨X, hX'⟩ := ZF.separation_exists_d hZF φ ρ A
  have hX r : M.mem r X ↔ Stn_d I ω J T U r := ((hX' r).trans
    (and_congr_right fun _ => stn_sat_l I hZF.1 _ _ _ _ _ _)).trans ⟨And.right,
      fun h => ⟨h.elim fun a h => h.elim fun b h => (fp_type_l I hZF hA hJ h.1).1, h⟩⟩
  have xt := stn_tree_l I hZF hA hJ hT.1 hU.1 hX
  let η : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J
  let ψ : UnarySchema 2 := { body := cp_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest }
  obtain ⟨Q, hQ'⟩ := ZF.separation_exists_d hZF ψ η X
  have hQ r : M.mem r Q ↔ Stn_d I ω J T U r ∧ Cp_d I ω J r :=
    (hQ' r).trans (and_congr (hX r) (cp_sat_l I hZF.1 _ _ _ _))
  have qt : Tree_d A Q := ⟨fun r hr => xt.1 r ((hX r).mpr ((hQ r).mp hr).1), fun r hr q hq hqr =>
    (hQ q).mpr ⟨(hX q).mp (xt.2 r ((hX r).mpr ((hQ r).mp hr).1) q hq hqr),
      cp_prefix_l I hZF hA hJ hq ((hQ r).mp hr).2 hqr⟩⟩
  obtain ⟨S, hs⟩ := tree_edges_l I hZF ω Q
  have wf := tree_wf_of_no_branch_l I hZF hB hA ha qt hs (stn_no_branch_l I hZF hB hA hJ hT hU hKL hQ)
  let θ : BinarySchema 2 := {
    body := .conj (cp_m (𝒞 := 𝒞) (.bound 3) (.bound 2) .newest)
      (step_m (𝒞 := 𝒞) (.bound 3) .newest (.bound 1)) }
  obtain ⟨R, _, hR⟩ := ZF.exists_setRelationOn_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) θ η X
  have er q r : Rd_entry_d q r R ↔ M.mem q X ∧ M.mem r X ∧ Cp_d I ω J r ∧ Step_d I ω r q := by
    simpa only [θ, BinarySchema.denote, Formula.satisfies_conj_iff, cp_sat_l I hZF.1, step_sat_l I hZF.1] using! hR q r
  refine ⟨X, R, hX, ?_, er⟩
  intro V hVX ⟨r, hr⟩
  by_cases terminal : ∃ q, M.mem q V ∧ ¬ Cp_d I ω J q
  · obtain ⟨q, hq, hn⟩ := terminal
    exact ⟨q, hq, fun r _ h => hn ((er r q).mp h).2.2.1⟩
  · have sub q (hq : M.mem q V) : M.mem q Q := (hQ q).mpr ⟨(hX q).mp (hVX q hq),
      Classical.byContradiction (fun hn => terminal ⟨q, hq, hn⟩)⟩
    obtain ⟨q, hq, hmin⟩ := wf V sub ⟨r, hr⟩
    exact ⟨q, hq, fun r hr he => hmin r hr ((hs.2 q r).mpr ⟨sub q hq, sub r hr, ((er r q).mp he).2.2.2⟩)⟩

end YesMetaZFC.SetTheory.Descriptive
