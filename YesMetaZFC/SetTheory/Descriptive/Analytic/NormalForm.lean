import YesMetaZFC.SetTheory.Descriptive.Normal.Closed
import YesMetaZFC.SetTheory.Descriptive.RealPair.Associate

/-! # 解析集的闭集及闭树投影正规形

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
    have hrf := hr.isSetFunctionFromTo hpf (hω.transitive hZF n hn)
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
