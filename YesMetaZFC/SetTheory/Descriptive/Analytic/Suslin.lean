import YesMetaZFC.SetTheory.Descriptive.Analytic.Code
import YesMetaZFC.SetTheory.Descriptive.Borel.Relabel
import YesMetaZFC.SetTheory.Descriptive.Normal.Closed
import YesMetaZFC.SetTheory.Descriptive.RealPair.Maps
import YesMetaZFC.SetTheory.Descriptive.RealPair.Finite
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeWellFounded
import YesMetaZFC.SetTheory.Descriptive.Borel.Universe

/-! # Borel 集的解析表示

对角配对给出闭嵌入。先映射原 Borel 码的叶标签，再与闭对角集相交，得到
对角像的实际 Borel 码；其投影恰为原集合。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Dg_d (B J D : M.Domain) : Prop := ∀ t, M.mem t D ↔ M.mem t B ∧ ∃ x, M.mem x B ∧ Rp_d I J x x t
def dg_m {d} (B J D : Term d) : Formula 1 d := .forallE (.iff (.mem .newest D.weaken)
  (.conj (.mem .newest B.weaken) (Formula.existsMem B.weaken
    (rp_m (𝒞 := 𝒞) J.weaken.weaken .newest .newest (.bound 1)))))
derive_free_closed dg_m
theorem dg_sat_l {d} (ρ : Env M d) (B J D : Term d) :
    Formula.satisfies ρ (dg_m (𝒞 := 𝒞) B J D) ↔ Dg_d I (B.eval ρ) (J.eval ρ) (D.eval ρ) := by
  simp only [dg_m, Dg_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_existsMem_iff,
    rp_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem dg_closed_l (hZF : M.Models ZF) {ω B A J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) :
    ∃ D U, Dg_d I B J D ∧ Cm_d B D U ∧ Open_d A B U := by
  let ρ : Env M 2 := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push J
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 2) (rp_m (𝒞 := 𝒞) (.bound 2) .newest .newest (.bound 1)) }
  obtain ⟨D, hD'⟩ := ZF.separation_exists_d hZF φ ρ B
  have hD : Dg_d I B J D := by
    intro t
    simpa only [φ, Formula.satisfies_existsMem_iff, rp_sat_l I] using! hD' t
  obtain ⟨U, hU⟩ := cm_exists_l (ZF.modelsKP hZF) B D
  refine ⟨D, U, hD, hU, ⟨fun t ht => ((hU t).mp ht).1, fun t ht => ?_⟩⟩
  obtain ⟨htB, htD⟩ := (hU t).mp ht
  obtain ⟨x, y, hx, hy, hp⟩ := rp_decode_l I hZF hJ ((hB.2 t).mp htB)
  have hxy : x ≠ y := by
    intro e
    subst y
    exact htD ((hD t).mpr ⟨htB, x, (hB.2 x).mpr hx, hp⟩)
  obtain ⟨i, a, b, hi, hia, hib, hab⟩ := ds_differ_l I hZF.1 hx hy hxy
  obtain ⟨v, _, hv⟩ := np_total_l I hJ (hx.output_mem_of_pairMember hia) (hy.output_mem_of_pairMember hib)
  have hiv := (hp.2 i v).mpr ⟨a, b, hia, hib, hv⟩
  obtain ⟨n, hn, hnω⟩ := hB.1.1.2 i hi
  obtain ⟨s, hs, hr, _⟩ := ds_prefix_l I hZF hB.1 ((hB.2 t).mp htB) hnω
  refine ⟨s, (hA s).mpr ⟨n, hnω, hs⟩, (ds_restrict_iff_l I hs ((hB.2 t).mp htB).1).mp hr, fun u hu hsu => ?_⟩
  apply (hU u).mpr
  refine ⟨hu, fun huD => ?_⟩
  obtain ⟨_, w, hw, hwu⟩ := (hD u).mp huD
  obtain ⟨p, hpc, hps⟩ := (hr.2 i v).mpr ⟨hn.predecessor_mem, hiv⟩
  obtain ⟨c, d, hic, hid, hcd⟩ := (hwu.2 i v).mp ⟨p, hpc, hsu p hps⟩
  obtain ⟨ha, hb⟩ := np_injective_l I hJ hv hcd
  exact hab (ha.trans ((((hB.2 w).mp hw).1.2 i c d hic hid).trans hb.symm))

theorem dg_prefix_graph_l (hZF : M.Models ZF) {ω A J}
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) : ∃ H, M.IsSetFunctionFromTo I H A A ∧
      ∀ s t, M.PairMember I s t H ↔ M.mem s A ∧ Rp_d I J s s t := by
  let ρ : Env M 1 := ⟨fun _ => J, fun _ => J⟩
  let φ : BinarySchema 1 := { body := rp_m (𝒞 := 𝒞) (.bound 2) (.bound 1) (.bound 1) .newest }
  have hp s t : φ.denote ρ s t ↔ Rp_d I J s s t := rp_sat_l I _ _ _ _ _
  obtain ⟨H, hH, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := A) (target := A)
    (by
      intro s hs
      obtain ⟨_, _, hs⟩ := (hA s).mp hs
      obtain ⟨t, _, ht⟩ := rp_exists_l I hZF hJ hs hs
      exact ⟨t, (hp s t).mpr ht⟩)
    (fun s _ t u ht hu => rp_unique_l I hZF.1 ((hp s t).mp ht) ((hp s u).mp hu))
    (by
      intro s t hs ht
      obtain ⟨n, hn, hs⟩ := (hA s).mp hs
      exact (hA t).mpr ⟨n, hn, rp_type_l I hZF hJ hs hs ((hp s t).mp ht)⟩)
  exact ⟨H, hH, fun s t => (he s t).trans (and_congr_right fun _ => hp s t)⟩

theorem dg_borel_l (hZF : M.Models ZF) {ω B A J K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hK : Borel_d I ω A A B K) : ∃ R, Borel_d I ω A A B R ∧
      ∀ z, M.mem z R ↔ ∃ x, M.mem x K ∧ Rp_d I J x x z := by
  obtain ⟨c, hc, hK⟩ := hK
  obtain ⟨H, hH, map⟩ := dg_prefix_graph_l I hZF hA hJ
  obtain ⟨d, hd, val⟩ := bcode_relabel_l I hZF hH hc
  have value {x z} (h : Rp_d I J x x z) : Bsat_d I ω A A d z ↔ Bsat_d I ω A A c x := by
    apply val x z
    intro s t hs ht
    obtain ⟨_, _, hs⟩ := (hA s).mp hs
    exact (rp_subset_l I hJ hs hs ((map s t).mp ht).2 h).trans ⟨And.left, fun h => ⟨h, h⟩⟩
  obtain ⟨D, U, hD, hU, ho⟩ := dg_closed_l I hZF hB hA hJ
  obtain ⟨T, _, _, ht⟩ := tree_of_closed_l (ZF.modelsKP hZF) (fun x hx => ((hD x).mp hx).1) hU ho
  obtain ⟨q, hq, eqn⟩ := tree_body_borel_l I hZF hB.1 hA ha ht
  obtain ⟨e, he, ev⟩ := bcode_inter_l I hZF hB.1 hA hd hq
  obtain ⟨R, hR, _⟩ := bden_exists_unique_l I hZF ω A A B e
  refine ⟨R, ⟨e, he, hR⟩, fun z => ⟨?_, ?_⟩⟩
  · intro hz
    obtain ⟨hzB, hz⟩ := (hR z).mp hz
    obtain ⟨hdz, hqz⟩ := (ev z).mp hz
    obtain ⟨_, x, hxB, hp⟩ := (hD z).mp ((eqn z).mpr ⟨hzB, hqz⟩)
    exact ⟨x, (hK x).mpr ⟨hxB, (value hp).mp hdz⟩, hp⟩
  · rintro ⟨x, hx, hp⟩
    obtain ⟨hxB, hcx⟩ := (hK x).mp hx
    have hxF := (hB.2 x).mp hxB
    have hzB := (hB.2 z).mpr (rp_type_l I hZF hJ hxF hxF hp)
    have hzD := (hD z).mpr ⟨hzB, x, hxB, hp⟩
    exact (hR z).mpr ⟨hzB, (ev z).mpr ⟨(value hp).mpr hcx, ((eqn z).mp hzD).2⟩⟩

/-- 每个 Borel 集及其相对补都解析，故 Borel ⊆ Δ¹₁ 的关键包含实际成立。 -/
theorem borel_an_l (hZF : M.Models ZF) {ω B A J K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hK : Borel_d I ω A A B K) : An_d I ω A B J K := by
  have hKB : M.MemberSubset K B := hK.elim fun c h => fun x hx => ((h.2 x).mp hx).1
  obtain ⟨R, hr, image⟩ := dg_borel_l I hZF hB hA ha hJ hK
  apply (an_proj_l I).mpr
  refine ⟨R, hr, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    have hxf := (hB.2 x).mp (hKB x hx)
    obtain ⟨z, hz, hp⟩ := rp_exists_l I hZF hJ hxf hxf
    exact ⟨hKB x hx, x, z, hKB x hx, (hB.2 z).mpr hz, hp, (image z).mpr ⟨x, hx, hp⟩⟩
  · rintro ⟨hxB, y, z, hyB, _, hp, hzR⟩
    obtain ⟨u, hu, hdiag⟩ := (image z).mp hzR
    have huf := (hB.2 u).mp (hKB u hu)
    have eqn := rp_injective_l I hZF.1 hJ ((hB.2 x).mp hxB) ((hB.2 y).mp hyB) huf huf hp hdiag
    exact eqn.1.symm ▸ hu

end YesMetaZFC.SetTheory.Descriptive

/-! ## 解析集的闭集及闭树投影正规形

先将 Borel 关系替换为闭求值证书，再重括号合并原实数见证与证书见证。
最后取闭关系的规范前缀树。所有步骤均产生模型中的实际集合。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem an_closed_l (hZF : M.Models ZF) {ω A B J K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J) :
    An_d I ω A B J K ↔ ∃ D, Cl_d A B D ∧ Pr_d I B J D K := by
  constructor
  · intro h
    obtain ⟨R, hr, hK⟩ := (an_proj_l I).mp h
    obtain ⟨C, hc, hR⟩ := borel_closed_proj_l I hZF hB hA ha hJ hr
    obtain ⟨D, hd, eqn⟩ := ac_closed_l I hZF hB hA hJ hc
    refine ⟨D, hd, fun x => ⟨?_, ?_⟩⟩
    · intro hx
      obtain ⟨hxB, y, r, hyB, hrB, hxy, hrR⟩ := (hK x).mp hx
      obtain ⟨_, w, q, hwB, hqB, hrw, hqC⟩ := (hR r).mp hrR
      have hxf := (hB.2 x).mp hxB
      have hyf := (hB.2 y).mp hyB
      have hwf := (hB.2 w).mp hwB
      obtain ⟨u, huf, hyw⟩ := rp_exists_l I hZF hJ hyf hwf
      obtain ⟨p, hpf, hxu⟩ := rp_exists_l I hZF hJ hxf huf
      exact ⟨hxB, u, p, (hB.2 u).mpr huf, (hB.2 p).mpr hpf, hxu,
        (eqn p).mpr ⟨(hB.2 p).mpr hpf, q, hqB,
          ⟨x, y, w, u, r, hxf, hyf, hwf, huf, (hB.2 r).mp hrB, hyw, hxu, hxy, hrw⟩, hqC⟩⟩
    · rintro ⟨hxB, u, p, huB, _, hxu, hpD⟩
      obtain ⟨_, q, hqB, ac, hqC⟩ := (eqn p).mp hpD
      obtain ⟨x', y, w, u', v, hxf, hyf, hwf, huf, hvf, _, hp, hxy, hvw⟩ := ac
      obtain ⟨ex, eu⟩ := rp_injective_l I hZF.1 hJ ((hB.2 x).mp hxB) ((hB.2 u).mp huB) hxf huf hxu hp
      subst x' u'
      have hvB := (hB.2 v).mpr hvf
      have hvR := (hR v).mpr ⟨hvB, w, q, (hB.2 w).mpr hwf, hqB, hvw, hqC⟩
      exact (hK x).mpr ⟨hxB, y, v, (hB.2 y).mpr hyf, hvB, hxy, hvR⟩
  · rintro ⟨D, hd, hk⟩
    obtain ⟨T, _, ht⟩ := (closed_tree_l (ZF.modelsKP hZF)).mp hd
    exact (an_proj_l I).mpr ⟨D, tree_body_borel_l I hZF hB.1 hA ha ht, hk⟩

def Atree_d (A B J T K : M.Domain) : Prop := Tree_d A T ∧ ∃ C, Body_d A B T C ∧ Pr_d I B J C K
def atree_m {d} (A B J T K : Term d) : Formula 1 d := .conj (tree_m A T) (.existsE (.conj
  (body_m A.weaken B.weaken T.weaken .newest) (pr_m (𝒞 := 𝒞) B.weaken J.weaken .newest K.weaken)))
derive_free_closed atree_m

theorem atree_sat_l {d} (ρ : Env M d) (A B J T K : Term d) :
    Formula.satisfies ρ (atree_m (𝒞 := 𝒞) A B J T K) ↔
      Atree_d I (A.eval ρ) (B.eval ρ) (J.eval ρ) (T.eval ρ) (K.eval ρ) := by
  simp only [atree_m, Atree_d, Formula.satisfies_conj_iff, tree_sat_l, Formula.satisfies_exists_iff,
    body_sat_l, pr_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem an_tree_iff_l (hZF : M.Models ZF) {ω A B J K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J) :
    An_d I ω A B J K ↔ ∃ T, Atree_d I A B J T K := by
  refine (an_closed_l I hZF hB hA ha hJ).trans ⟨?_, ?_⟩
  · rintro ⟨C, hc, hk⟩
    obtain ⟨T, ht, hb⟩ := (closed_tree_l (ZF.modelsKP hZF)).mp hc
    exact ⟨T, ht, C, hb, hk⟩
  · rintro ⟨T, ht, C, hb, hk⟩
    exact ⟨C, (closed_tree_l (ZF.modelsKP hZF)).mpr ⟨T, ht, hb⟩, hk⟩

/-- 正规形还返回规范树及其无死节点性质；树中每个节点都能延伸到闭关系。 -/
theorem an_normal_l (hZF : M.Models ZF) {ω A B J K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (h : An_d I ω A B J K) : ∃ T C, Ktree_d A C T ∧ Atree_d I A B J T K ∧
      (∀ s, M.mem s T → ∃ t, M.mem t T ∧ Step_d I ω s t) ∧ ∀ U, Ktree_d A C U → U = T := by
  obtain ⟨C, hc, hk⟩ := (an_closed_l I hZF hB hA ha hJ).mp h
  obtain ⟨T, ht, htree, hb, hu⟩ := closed_ktree_l (ZF.modelsKP hZF) hc
  exact ⟨T, C, ht, ⟨htree, C, hb, hk⟩, ktree_pruned_l I hZF hB hA hc.1 ht, hu⟩

/-- 实数对在树中形成分支：每个内部长度都有对应的成对前缀节点。 -/
def Tpath_d (ω J T x y : M.Domain) : Prop := ∀ n, M.mem n ω → ∃ s t r,
  M.IsSetFunctionFromTo I s n ω ∧ M.IsSetFunctionFromTo I t n ω ∧
  M.MemberSubset s x ∧ M.MemberSubset t y ∧ Rp_d I J s t r ∧ M.mem r T
def tpath_m {d} (ω J T x y : Term d) : Formula 1 d := Formula.forallMem ω (.existsE (.existsE (.existsE (.conj
  (Formula.isFunctionFromTo 𝒞 (.bound 2) (.bound 3) ω.weaken.weaken.weaken.weaken) (.conj
  (Formula.isFunctionFromTo 𝒞 (.bound 1) (.bound 3) ω.weaken.weaken.weaken.weaken) (.conj
  (Formula.subset (.bound 2) x.weaken.weaken.weaken.weaken) (.conj
  (Formula.subset (.bound 1) y.weaken.weaken.weaken.weaken) (.conj
  (rp_m (𝒞 := 𝒞) J.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
  (.mem .newest T.weaken.weaken.weaken.weaken)))))))))
derive_free_closed tpath_m

theorem tpath_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J T x y : Term d) :
    Formula.satisfies ρ (tpath_m (𝒞 := 𝒞) ω J T x y) ↔
      Tpath_d I (ω.eval ρ) (J.eval ρ) (T.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [tpath_m, Tpath_d, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_subset_iff, rp_sat_l I, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

theorem tpath_branch_l (hZF : M.Models ZF) {ω A J T x y p} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J)
    (hx : M.IsSetFunctionFromTo I x ω ω) (hy : M.IsSetFunctionFromTo I y ω ω) (hp : Rp_d I J x y p) :
    Branch_d A T p ↔ Tpath_d I ω J T x y := by
  have hpf := rp_type_l I hZF hJ hx hy hp
  refine (tree_branch_l I hZF hω hA hpf).trans ⟨?_, ?_⟩
  · intro h n hn
    obtain ⟨r, hrT, hr⟩ := h n hn
    have hrf := hr.isSetFunctionFromTo hpf (hω.transitive (ZF.modelsKP hZF) n hn)
    obtain ⟨s, t, hs, ht, hst⟩ := rp_decode_l I hZF hJ hrf
    obtain ⟨hsx, hty⟩ := (rp_subset_l I hJ hs ht hst hp).mp ((ds_restrict_iff_l I hrf hpf.1).mp hr)
    exact ⟨s, t, r, hs, ht, hsx, hty, hst, hrT⟩
  · intro h n hn
    obtain ⟨s, t, r, hs, ht, hsx, hty, hst, hrT⟩ := h n hn
    exact ⟨r, hrT, (ds_restrict_iff_l I (rp_type_l I hZF hJ hs ht hst) hpf.1).mpr
      ((rp_subset_l I hJ hs ht hst hp).mpr ⟨hsx, hty⟩)⟩

theorem atree_mem_l (hZF : M.Models ZF) {ω A B J T K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (h : Atree_d I A B J T K) (x : M.Domain) :
    M.mem x K ↔ M.mem x B ∧ ∃ y, M.mem y B ∧ Tpath_d I ω J T x y := by
  obtain ⟨_, C, hc, hk⟩ := h
  constructor
  · intro hx
    obtain ⟨hxB, y, p, hyB, _, hp, hpC⟩ := (hk x).mp hx
    exact ⟨hxB, y, hyB, (tpath_branch_l I hZF hB.1 hA hJ ((hB.2 x).mp hxB) ((hB.2 y).mp hyB) hp).mp ((hc p).mp hpC).2⟩
  · rintro ⟨hxB, y, hyB, ht⟩
    obtain ⟨p, hpF, hp⟩ := rp_exists_l I hZF hJ ((hB.2 x).mp hxB) ((hB.2 y).mp hyB)
    have hpB := (hB.2 p).mpr hpF
    exact (hk x).mpr ⟨hxB, y, p, hyB, hpB, hp, (hc p).mpr ⟨hpB,
      (tpath_branch_l I hZF hB.1 hA hJ ((hB.2 x).mp hxB) ((hB.2 y).mp hyB) hp).mpr ht⟩⟩

/-- 直接的 ∃实数见证、∀内部长度正规形，无需调用者先提供闭集或树。 -/
theorem an_prefix_iff_l (hZF : M.Models ZF) {ω A B J K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J) :
    An_d I ω A B J K ↔ ∃ T, Tree_d A T ∧ ∀ x,
      M.mem x K ↔ M.mem x B ∧ ∃ y, M.mem y B ∧ Tpath_d I ω J T x y := by
  constructor
  · intro h
    obtain ⟨T, ht⟩ := (an_tree_iff_l I hZF hB hA ha hJ).mp h
    exact ⟨T, ht.1, atree_mem_l I hZF hB hA hJ ht⟩
  · rintro ⟨T, ht, hk⟩
    obtain ⟨C, hc⟩ := tree_body_exists_l (ZF.modelsKP hZF) A B T
    obtain ⟨L, hl⟩ := pr_exists_l I hZF B J C
    have hL : Atree_d I A B J T L := ⟨ht, C, hc, hl⟩
    have e := hZF.1.eq_of_same_members L K (fun x => (atree_mem_l I hZF hB hA hJ hL x).trans (hk x).symm)
    exact (an_tree_iff_l I hZF hB hA ha hJ).mpr ⟨T, e ▸ hL⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 解析分离的同步乘积树

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

/-! ## 分离码的递归算子：逐行交，再对行取并 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Se_d (ω J U E G b a i d : M.Domain) : Prop := ∃ v q,
  M.mem v U ∧ Step_d I ω b v ∧ Fp_d I ω J q a v ∧ M.PairMember I v i E ∧ M.PairMember I q d G
def se_m {d} (ω J U E G b a i c : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (.mem (.bound 1) U.weaken.weaken) (.conj (step_m (𝒞 := 𝒞) ω.weaken.weaken b.weaken.weaken (.bound 1)) (.conj
  (fp_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken .newest a.weaken.weaken (.bound 1)) (.conj
  (Formula.orderedPairMem 𝒞 (.bound 1) i.weaken.weaken E.weaken.weaken)
  (Formula.orderedPairMem 𝒞 .newest c.weaken.weaken G.weaken.weaken))))))
derive_free_closed se_m
theorem se_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J U E G b a i c : Term d) :
    Formula.satisfies ρ (se_m (𝒞 := 𝒞) ω J U E G b a i c) ↔
      Se_d I (ω.eval ρ) (J.eval ρ) (U.eval ρ) (E.eval ρ) (G.eval ρ) (b.eval ρ) (a.eval ρ) (i.eval ρ) (c.eval ρ) := by
  simp only [se_m, Se_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    step_sat_l I hE, fp_sat_l I hE, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

def Sr_d (ω J U E G b a c : M.Domain) : Prop := ∃ H, M.IsSetRelation I H ∧
  (∀ i d, M.PairMember I i d H ↔ Se_d I ω J U E G b a i d) ∧ Binf_d I ω H c
def sr_m {d} (ω J U E G b a c : Term d) : Formula 1 d := .existsE (.conj (Formula.isRelation 𝒞 .newest) (.conj
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
    (se_m (𝒞 := 𝒞) ω.weaken.weaken.weaken J.weaken.weaken.weaken U.weaken.weaken.weaken E.weaken.weaken.weaken
      G.weaken.weaken.weaken b.weaken.weaken.weaken a.weaken.weaken.weaken (.bound 1) .newest))))
  (binf_m (𝒞 := 𝒞) ω.weaken .newest c.weaken)))
derive_free_closed sr_m
theorem sr_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J U E G b a c : Term d) :
    Formula.satisfies ρ (sr_m (𝒞 := 𝒞) ω J U E G b a c) ↔
      Sr_d I (ω.eval ρ) (J.eval ρ) (U.eval ρ) (E.eval ρ) (G.eval ρ) (b.eval ρ) (a.eval ρ) (c.eval ρ) := by
  simp only [sr_m, Sr_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    se_sat_l I hE, binf_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem sr_unique_l (hE : Extensional M) {ω J U E G b a c d}
    (h : Sr_d I ω J U E G b a c) (k : Sr_d I ω J U E G b a d) : c = d := by
  obtain ⟨H, hh, he, hc⟩ := h
  obtain ⟨F, hf, fe, hd⟩ := k
  have e := hf.eq_of_pairMember_iff hE hh (fun i c => (fe i c).trans (he i c).symm)
  subst F
  exact binf_unique_l I hE hc hd

def So_d (ω J T U E G a b i c : M.Domain) : Prop := ∃ u,
  M.mem u T ∧ Step_d I ω a u ∧ M.PairMember I u i E ∧ Sr_d I ω J U E G b u c
def so_m {d} (ω J T U E G a b i c : Term d) : Formula 1 d := Formula.existsMem T (.conj
  (step_m (𝒞 := 𝒞) ω.weaken a.weaken .newest) (.conj
  (Formula.orderedPairMem 𝒞 .newest i.weaken E.weaken)
  (sr_m (𝒞 := 𝒞) ω.weaken J.weaken U.weaken E.weaken G.weaken b.weaken .newest c.weaken)))
derive_free_closed so_m
theorem so_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J T U E G a b i c : Term d) :
    Formula.satisfies ρ (so_m (𝒞 := 𝒞) ω J T U E G a b i c) ↔
      So_d I (ω.eval ρ) (J.eval ρ) (T.eval ρ) (U.eval ρ) (E.eval ρ) (G.eval ρ) (a.eval ρ) (b.eval ρ) (i.eval ρ) (c.eval ρ) := by
  simp only [so_m, So_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    step_sat_l I hE, sr_sat_l I hE, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

def Sm_d (ω J T U E G a b c : M.Domain) : Prop := ∃ H, M.IsSetRelation I H ∧
  (∀ i d, M.PairMember I i d H ↔ So_d I ω J T U E G a b i d) ∧ Bsup_d I ω H c
def sm_m {d} (ω J T U E G a b c : Term d) : Formula 1 d := .existsE (.conj (Formula.isRelation 𝒞 .newest) (.conj
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
    (so_m (𝒞 := 𝒞) ω.weaken.weaken.weaken J.weaken.weaken.weaken T.weaken.weaken.weaken U.weaken.weaken.weaken E.weaken.weaken.weaken
      G.weaken.weaken.weaken a.weaken.weaken.weaken b.weaken.weaken.weaken (.bound 1) .newest))))
  (bsup_m (𝒞 := 𝒞) ω.weaken .newest c.weaken)))
derive_free_closed sm_m
theorem sm_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J T U E G a b c : Term d) :
    Formula.satisfies ρ (sm_m (𝒞 := 𝒞) ω J T U E G a b c) ↔
      Sm_d I (ω.eval ρ) (J.eval ρ) (T.eval ρ) (U.eval ρ) (E.eval ρ) (G.eval ρ) (a.eval ρ) (b.eval ρ) (c.eval ρ) := by
  simp only [sm_m, Sm_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    so_sat_l I hE, bsup_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem sm_unique_l (hE : Extensional M) {ω J T U E G a b c d}
    (h : Sm_d I ω J T U E G a b c) (k : Sm_d I ω J T U E G a b d) : c = d := by
  obtain ⟨H, hh, he, hc⟩ := h
  obtain ⟨F, hf, fe, hd⟩ := k
  have e := hf.eq_of_pairMember_iff hE hh (fun i c => (fe i c).trans (he i c).symm)
  subst F
  exact bsup_unique_l I hE hc hd

theorem sr_exists_l (hZF : M.Models ZF) {ω A J U E G b a} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (he : M.IsSetInjectionFromTo I E A ω) (hG : M.IsSetFunction I G)
    (hU : M.MemberSubset U A) (bound : ∀ v q d, M.mem v U → Step_d I ω b v →
      Fp_d I ω J q a v → M.PairMember I q d G → Bcode_d I ω A A d) :
    ∃ c, Sr_d I ω J U E G b a c ∧ Bcode_d I ω A A c ∧ ∀ x,
      Bsat_d I ω A A c x ↔ ∀ v q d, M.mem v U → Step_d I ω b v →
        Fp_d I ω J q a v → M.PairMember I q d G → Bsat_d I ω A A d x := by
  let ρ : Env M 7 := ((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push U).push E).push G).push b).push a
  let φ : BinarySchema 7 := { body := se_m (𝒞 := 𝒞) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp i d : φ.denote ρ i d ↔ Se_d I ω J U E G b a i d := se_sat_l I hZF.1 _ _ _ _ _ _ _ _ _ _
  obtain ⟨H, hf, pair⟩ := bf_defined_l I hZF φ ρ (by
    intro i c d hc hd
    obtain ⟨v, q, _, _, ⟨_, _, _, _, hq⟩, hi, hc⟩ := (hp i c).mp hc
    obtain ⟨w, r, _, _, ⟨_, _, _, _, hr⟩, hj, hd⟩ := (hp i d).mp hd
    have e := he.2 w v i hj hi
    subst w
    exact hG.2 q c d hc (rp_unique_l I hZF.1 hr hq ▸ hd)) (by
    intro i d hd
    obtain ⟨v, q, hv, hs, hq, hi, hd⟩ := (hp i d).mp hd
    exact ⟨he.1.output_mem_of_pairMember hi, bound v q d hv hs hq hd⟩)
  have ep i d := (pair i d).trans (hp i d)
  obtain ⟨c, hc, hf', cv⟩ := binf_exists_l I hZF hω hA hf
  refine ⟨c, ⟨H, hf.1.1, ep, hc⟩, hf', fun x => (cv x).trans ⟨?_, ?_⟩⟩
  · intro hall v q d hv hs hq hd
    obtain ⟨i, _, hi⟩ := he.1.2.2 v (hU v hv)
    exact hall i d ((ep i d).mpr ⟨v, q, hv, hs, hq, hi, hd⟩)
  · intro hall i d hd
    obtain ⟨v, q, hv, hs, hq, _, hd⟩ := (ep i d).mp hd
    exact hall v q d hv hs hq hd

theorem sm_exists_l (hZF : M.Models ZF) {ω A J T U E G a b} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (he : M.IsSetInjectionFromTo I E A ω) (hG : M.IsSetFunction I G)
    (hT : M.MemberSubset T A) (hU : M.MemberSubset U A)
    (bound : ∀ u v q d, M.mem u T → Step_d I ω a u → M.mem v U → Step_d I ω b v →
      Fp_d I ω J q u v → M.PairMember I q d G → Bcode_d I ω A A d) :
    ∃ c, Sm_d I ω J T U E G a b c ∧ Bcode_d I ω A A c ∧ ∀ x,
      Bsat_d I ω A A c x ↔ ∃ u, M.mem u T ∧ Step_d I ω a u ∧
        ∀ v q d, M.mem v U → Step_d I ω b v → Fp_d I ω J q u v → M.PairMember I q d G → Bsat_d I ω A A d x := by
  let ρ : Env M 8 := (((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push T).push U).push E).push G).push a).push b
  let φ : BinarySchema 8 := { body := so_m (𝒞 := 𝒞) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp i d : φ.denote ρ i d ↔ So_d I ω J T U E G a b i d := so_sat_l I hZF.1 _ _ _ _ _ _ _ _ _ _ _
  have row u (hu : M.mem u T) (hs : Step_d I ω a u) := sr_exists_l I hZF hω hA he hG hU (bound u · · · hu hs)
  obtain ⟨H, hf, pair⟩ := bf_defined_l I hZF φ ρ (by
    intro i c d hc hd
    obtain ⟨u, _, _, hi, hc⟩ := (hp i c).mp hc
    obtain ⟨v, _, _, hj, hd⟩ := (hp i d).mp hd
    exact sr_unique_l I hZF.1 hc (he.2 v u i hj hi ▸ hd)) (by
    intro i d hd
    obtain ⟨u, hu, hs, hi, hd⟩ := (hp i d).mp hd
    obtain ⟨c, hc, ht, _⟩ := row u hu hs
    exact ⟨he.1.output_mem_of_pairMember hi, sr_unique_l I hZF.1 hc hd ▸ ht⟩)
  have ep i d := (pair i d).trans (hp i d)
  obtain ⟨c, hc, hf', cv⟩ := bsup_exists_l I hZF hω hA hf
  refine ⟨c, ⟨H, hf.1.1, ep, hc⟩, hf', fun x => (cv x).trans ⟨?_, ?_⟩⟩
  · rintro ⟨i, d, hd, hx⟩
    obtain ⟨u, hu, hs, _, hd⟩ := (ep i d).mp hd
    obtain ⟨e, he, _, ev⟩ := row u hu hs
    exact ⟨u, hu, hs, (ev x).mp (sr_unique_l I hZF.1 hd he ▸ hx)⟩
  · rintro ⟨u, hu, hs, hx⟩
    obtain ⟨d, hd, _, dv⟩ := row u hu hs
    obtain ⟨i, _, hi⟩ := he.1.2.2 u (hT u hu)
    exact ⟨i, d, (ep i d).mpr ⟨u, hu, hs, hi, hd⟩, (dv x).mpr hx⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 分离码递归的实际内部总图 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sm_congr_l {ω J T U E G H a b c}
    (eqn : ∀ u v q d, M.mem u T → Step_d I ω a u → M.mem v U → Step_d I ω b v →
      Fp_d I ω J q u v → (M.PairMember I q d G ↔ M.PairMember I q d H)) :
    Sm_d I ω J T U E G a b c ↔ Sm_d I ω J T U E H a b c := by
  have row u (hu : M.mem u T) (hs : Step_d I ω a u) i d :
      Se_d I ω J U E G b u i d ↔ Se_d I ω J U E H b u i d := by
    exact exists_congr fun v => exists_congr fun q => and_congr_right fun hv => and_congr_right fun ht =>
      and_congr_right fun hp => and_congr_right fun _ => eqn u v q d hu hs hv ht hp
  have rows u (hu : M.mem u T) (hs : Step_d I ω a u) d :
      Sr_d I ω J U E G b u d ↔ Sr_d I ω J U E H b u d := by
    exact exists_congr fun F => and_congr_right fun _ => and_congr_left fun _ =>
      forall_congr' fun i => forall_congr' fun e => iff_congr Iff.rfl (row u hu hs i e)
  exact exists_congr fun F => and_congr_right fun _ => and_congr_left fun _ =>
    forall_congr' fun i => forall_congr' fun d => iff_congr Iff.rfl
      (exists_congr fun u => and_congr_right fun hu => and_congr_right fun hs =>
        and_congr_right fun _ => rows u hu hs d)

def Sc_d (ω J T U E G r c : M.Domain) : Prop := ∃ a b, Fp_d I ω J r a b ∧
  ((Cp_d I ω J r ∧ Sm_d I ω J T U E G a b c) ∨
    (¬ Cp_d I ω J r ∧ ∃ s t, Fp_d I ω J a s t ∧ Bbasic_d I s c))
def sc_m {d} (ω J T U E G r c : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (fp_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken r.weaken.weaken (.bound 1) .newest) (.disj (.conj
  (cp_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken r.weaken.weaken)
  (sm_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken T.weaken.weaken U.weaken.weaken E.weaken.weaken G.weaken.weaken (.bound 1) .newest c.weaken.weaken))
  (.conj (.neg (cp_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken r.weaken.weaken)) (.existsE (.existsE (.conj
  (fp_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken J.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) .newest)
  (bbasic_m (𝒞 := 𝒞) (.bound 1) c.weaken.weaken.weaken.weaken))))))))
derive_free_closed sc_m
theorem sc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J T U E G r c : Term d) :
    Formula.satisfies ρ (sc_m (𝒞 := 𝒞) ω J T U E G r c) ↔
      Sc_d I (ω.eval ρ) (J.eval ρ) (T.eval ρ) (U.eval ρ) (E.eval ρ) (G.eval ρ) (r.eval ρ) (c.eval ρ) := by
  simp only [sc_m, Sc_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_disj_iff,
    fp_sat_l I hE, cp_sat_l I hE, sm_sat_l I hE, bbasic_sat_l I hE, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]; rfl

theorem separation_recursion_l (hZF : M.Models ZF) {ω A B J T U K L} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hT : Atree_d I A B J T K) (hU : Atree_d I A B J U L) (hKL : M.IsDisjoint K L) :
    ∃ X R E G, (∀ r, M.mem r X ↔ Stn_d I ω J T U r) ∧ Wf_rel_d X R ∧
      (∀ q r, Rd_entry_d q r R ↔ M.mem q X ∧ M.mem r X ∧ Cp_d I ω J r ∧ Step_d I ω r q) ∧
      M.IsSetInjectionFromTo I E A ω ∧ M.IsSetFunction I G ∧
      (∀ r, M.mem r X → ∃ c, M.PairMember I r c G) ∧
      ∀ r c, M.PairMember I r c G → Bcode_d I ω A A c ∧ Sc_d I ω J T U E G r c := by
  classical
  obtain ⟨X, R, hX, hw, hR⟩ := separation_relation_l I hZF hB hA ha hJ hT hU hKL
  obtain ⟨E, he⟩ := ha
  obtain ⟨C, hC⟩ := bcode_universe_l I hZF ω A A
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push T).push U).push E
  let φ : BinarySchema 6 := { body := sc_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp G r c : φ.denote (ρ.push G) r c ↔ Sc_d I ω J T U E G r c := sc_sat_l I hZF.1 _ _ _ _ _ _ _ _ _
  have child {r a b q u v} (hr : M.mem r X) (cp : Cp_d I ω J r) (pr : Fp_d I ω J r a b)
      (hu : M.mem u T) (su : Step_d I ω a u) (hv : M.mem v U) (sv : Step_d I ω b v)
      (pq : Fp_d I ω J q u v) : M.mem q X ∧ Rd_entry_d q r R := by
    have hq := (hX q).mpr ⟨u, v, pq, hu, hv⟩
    exact ⟨hq, (hR q r).mpr ⟨hq, hr, cp, (fp_step_l I hZF hB.1 hJ pr pq).mpr ⟨su, sv⟩⟩⟩
  have total r G (hr : M.mem r X) (hg : M.IsSetFunction I G)
      (ready : ∀ q, M.mem q X → Rd_entry_d q r R → ∃ d, M.mem d C ∧ M.PairMember I q d G) :
      ∃ c, M.mem c C ∧ φ.denote (ρ.push G) r c := by
    obtain ⟨a, b, pr, ha, _⟩ := (hX r).mp hr
    by_cases cp : Cp_d I ω J r
    · obtain ⟨c, hc, ht, _⟩ := sm_exists_l I hZF hB.1 hA he hg hT.1.1 hU.1.1 (by
        intro u v q d hu su hv sv pq hd
        have edge := child hr cp pr hu su hv sv pq
        obtain ⟨e, heC, heG⟩ := ready q edge.1 edge.2
        exact hg.2 q e d heG hd ▸ (hC e).mp heC)
      exact ⟨c, (hC c).mpr ht, (hp G r c).mpr ⟨a, b, pr, Or.inl ⟨cp, hc⟩⟩⟩
    · obtain ⟨s, t, ps⟩ := fp_decode_l I hZF hA hJ (hT.1.1 a ha)
      obtain ⟨c, hc⟩ := bbasic_exists_l I (ZF.modelsKP hZF) s
      exact ⟨c, (hC c).mpr (bbasic_correct_l I hZF hB.1 hA (fp_type_l I hZF hA hJ ps).2.1 hc).1,
        (hp G r c).mpr ⟨a, b, pr, Or.inr ⟨cp, s, t, ps, hc⟩⟩⟩
  have unique r G H c d (hr : M.mem r X) (_ : M.IsSetFunction I G) (_ : M.IsSetFunction I H)
      (eqn : ∀ q e, M.mem q X → Rd_entry_d q r R → (M.PairMember I q e G ↔ M.PairMember I q e H))
      (hc : φ.denote (ρ.push G) r c) (hd : φ.denote (ρ.push H) r d) : c = d := by
    obtain ⟨a, b, pr, hc⟩ := (hp G r c).mp hc
    obtain ⟨u, v, pq, hd⟩ := (hp H r d).mp hd
    obtain ⟨eu, ev⟩ := fp_unique_l I hZF.1 hJ pq pr
    subst u v
    rcases hc with ⟨cp, hc⟩ | ⟨cp, s, t, ps, hc⟩ <;> rcases hd with ⟨cq, hd⟩ | ⟨cq, x, y, px, hd⟩
    · apply sm_unique_l I hZF.1 hc
      apply (sm_congr_l I (G := G) (H := H) ?_).mpr hd
      intro u v q e hu su hv sv pq
      have edge := child hr cp pr hu su hv sv pq
      exact eqn q e edge.1 edge.2
    · exact (cq cp).elim
    · exact (cp cq).elim
    · exact bbasic_unique_l I hZF.1 hc ((fp_unique_l I hZF.1 hJ px ps).1 ▸ hd)
  obtain ⟨G, hg, step⟩ := wf_bounded_recursion_l I hZF total unique hw
  exact ⟨X, R, E, G, hX, hw, hR, he, hg.1, fun r hr => (hg.2.2 r hr).imp fun _ h => h.2,
    fun r c hc => ⟨(hC c).mp (hg.output_mem_of_pairMember hc), (hp G r c).mp (step r c hc)⟩⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## Lusin 分离：不交解析集有实际 Borel 分离码 -/
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

/-! ## Suslin 定理：解析且余解析当且仅当 Borel -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem suslin_l (hZF : M.Models ZF) {ω A B J K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J) :
    Borel_d I ω A A B K ↔ An_d I ω A B J K ∧ Coan_d I ω A B J K := by
  constructor
  · intro hk
    obtain ⟨L, hl, hb⟩ := borel_compl_l I hZF hB.1 hA hk
    have sub : M.MemberSubset K B := hk.elim fun _ h => fun x hx => ((h.2 x).mp hx).1
    exact ⟨borel_an_l I hZF hB hA ha hJ hk,
      L, borel_an_l I hZF hB hA ha hJ hb, cm_symm_l sub hl⟩
  · rintro ⟨hk, L, hl, hc⟩
    obtain ⟨C, hb, sub, disj⟩ := an_separation_l I hZF hB hA ha hJ hk hl
      (fun x ⟨hx, hy⟩ => ((hc x).mp hx).2 hy)
    have cb : M.MemberSubset C B := hb.elim fun _ h => fun x hx => ((h.2 x).mp hx).1
    have e := hZF.1.eq_of_same_members C K (fun x => ⟨fun hx => (hc x).mpr
      ⟨cb x hx, fun hy => disj x ⟨hx, hy⟩⟩, sub x⟩)
    exact e ▸ hb

end YesMetaZFC.SetTheory.Descriptive
