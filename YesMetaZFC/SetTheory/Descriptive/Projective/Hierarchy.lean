import YesMetaZFC.SetTheory.Descriptive.Projective.Iteration
import YesMetaZFC.SetTheory.Descriptive.Analytic

/-! # 内部射影点类

Σ¹₀ 取已有 Borel 类；Σ¹ₙ 的码由一个 Borel 关系码及内部层号 n 组成。
每次后继先补再投影，Π¹ₙ 取相对补，Δ¹ₙ 为二者交。原公式同时覆盖标准与非标准层。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ps_d (ω A B J n K : M.Domain) : Prop := ∃ c C,
  Bcode_d I ω A A c ∧ Bden_d I ω A A B c C ∧ Pval_d I ω B J n C K
def ps_m {d} (ω A B J n K : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (bcode_m (𝒞 := 𝒞) ω.weaken.weaken A.weaken.weaken A.weaken.weaken (.bound 1)) (.conj
  (bden_m (𝒞 := 𝒞) ω.weaken.weaken A.weaken.weaken A.weaken.weaken B.weaken.weaken (.bound 1) .newest)
  (pval_m (𝒞 := 𝒞) ω.weaken.weaken B.weaken.weaken J.weaken.weaken n.weaken.weaken .newest K.weaken.weaken))))
derive_free_closed ps_m

theorem ps_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J n K : Term d) :
    Formula.satisfies ρ (ps_m (𝒞 := 𝒞) ω A B J n K) ↔
      Ps_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (K.eval ρ) := by
  simp only [ps_m, Ps_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bcode_sat_l I hE, bden_sat_l I hE, pval_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Pp_d (ω A B J n K : M.Domain) : Prop := ∃ L, Ps_d I ω A B J n L ∧ Cm_d B L K
def pp_m {d} (ω A B J n K : Term d) : Formula 1 d := .existsE (.conj
  (ps_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken J.weaken n.weaken .newest) (cm_m B.weaken .newest K.weaken))
derive_free_closed pp_m

theorem pp_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J n K : Term d) :
    Formula.satisfies ρ (pp_m (𝒞 := 𝒞) ω A B J n K) ↔
      Pp_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (K.eval ρ) := by
  simp only [pp_m, Pp_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ps_sat_l I hE, cm_sat_l, Definitional.Term.eval_weaken]; rfl

def Pd_d (ω A B J n K : M.Domain) : Prop := Ps_d I ω A B J n K ∧ Pp_d I ω A B J n K
def pd_m {d} (ω A B J n K : Term d) : Formula 1 d :=
  .conj (ps_m (𝒞 := 𝒞) ω A B J n K) (pp_m (𝒞 := 𝒞) ω A B J n K)
derive_free_closed pd_m

theorem pd_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J n K : Term d) :
    Formula.satisfies ρ (pd_m (𝒞 := 𝒞) ω A B J n K) ↔
      Pd_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (K.eval ρ) := by
  simp only [pd_m, Pd_d, Formula.satisfies_conj_iff, ps_sat_l I hE, pp_sat_l I hE]

theorem ps_subset_l {ω A B J n K} (h : Ps_d I ω A B J n K) : M.MemberSubset K B := by
  obtain ⟨_, _, _, _, H, hH, hK⟩ := h
  exact hH.bound n K hK

theorem ps_zero_l (hZF : M.Models ZF) {ω A B J z K} (hω : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z) :
    Ps_d I ω A B J z K ↔ Borel_d I ω A A B K := by
  constructor
  · rintro ⟨c, C, hc, hC, hv⟩
    have e := (pval_zero_l I hZF hω hz (fun x hx => ((hC x).mp hx).1)).mp hv
    exact ⟨c, hc, e.symm ▸ hC⟩
  · rintro ⟨c, hc, hK⟩
    exact ⟨c, K, hc, hK, (pval_zero_l I hZF hω hz (fun x hx => ((hK x).mp hx).1)).mpr rfl⟩

/-- 后继层恰为上一 Π 层的实数投影；反向也构造同一初始码的后继求值。 -/
theorem ps_succ_l (hZF : M.Models ZF) {ω A B J n m K} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) : Ps_d I ω A B J m K ↔
      ∃ L, Pp_d I ω A B J n L ∧ Pr_d I B J L K := by
  constructor
  · rintro ⟨c, C, hc, hC, hv⟩
    obtain ⟨D, hD, L, hl, hk⟩ := (pval_succ_l I hZF hω hn hm).mp hv
    exact ⟨L, ⟨D, ⟨c, C, hc, hC, hD⟩, hl⟩, hk⟩
  · rintro ⟨L, ⟨D, ⟨c, C, hc, hC, hv⟩, hl⟩, hk⟩
    exact ⟨c, C, hc, hC, (pval_succ_l I hZF hω hn hm).mpr ⟨D, hv, L, hl, hk⟩⟩

theorem ps_pp_compl_l (hE : Extensional M) {ω A B J n K L} (hK : M.MemberSubset K B) (h : Cm_d B K L) :
    Ps_d I ω A B J n K ↔ Pp_d I ω A B J n L := by
  refine ⟨fun hk => ⟨K, hk, h⟩, fun ⟨D, hd, hD⟩ => ?_⟩
  exact cm_unique_l hE (cm_symm_l (ps_subset_l I hd) hD) (cm_symm_l hK h) ▸ hd

theorem pp_zero_l (hZF : M.Models ZF) {ω A B J z K} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ x, ¬ M.mem x z) :
    Pp_d I ω A B J z K ↔ Borel_d I ω A A B K := by
  constructor
  · rintro ⟨L, hL, hk⟩
    obtain ⟨V, hv, hb⟩ := borel_compl_l I hZF hω hA ((ps_zero_l I hZF hω hz).mp hL)
    exact cm_unique_l hZF.1 hv hk ▸ hb
  · intro hk
    have hKB : M.MemberSubset K B := hk.elim fun c h => fun x hx => ((h.2 x).mp hx).1
    obtain ⟨L, hl, hb⟩ := borel_compl_l I hZF hω hA hk
    exact ⟨L, (ps_zero_l I hZF hω hz).mpr hb, cm_symm_l hKB hl⟩

theorem ps_one_l (hZF : M.Models ZF) {ω A B J o K} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (ho : M.IsOrdinalOne o) : Ps_d I ω A B J o K ↔ An_d I ω A B J K := by
  obtain ⟨z, hz, ho⟩ := ho
  obtain ⟨e, he, heω⟩ := hω.1.1
  have hzω := hZF.1.eq_of_same_members e z (fun x => iff_of_false (he x) (hz x)) ▸ heω
  exact (ps_succ_l I hZF hω hzω ho).trans
    ((exists_congr fun L => and_congr_left fun _ => pp_zero_l I hZF (K := L) hω hA hz).trans (an_proj_l I).symm)

theorem pp_one_l (hZF : M.Models ZF) {ω A B J o K} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (ho : M.IsOrdinalOne o) : Pp_d I ω A B J o K ↔ Coan_d I ω A B J K :=
  exists_congr fun L => and_congr_left fun _ => ps_one_l I hZF (K := L) hω hA ho

theorem pd_zero_l (hZF : M.Models ZF) {ω A B J z K} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ x, ¬ M.mem x z) :
    Pd_d I ω A B J z K ↔ Borel_d I ω A A B K := by
  exact (and_congr (ps_zero_l I hZF hω hz) (pp_zero_l I hZF hω hA hz)).trans ⟨And.left, fun h => ⟨h, h⟩⟩

theorem pd_compl_l (hE : Extensional M) {ω A B J n K L} (hK : M.MemberSubset K B) (h : Cm_d B K L) :
    Pd_d I ω A B J n K ↔ Pd_d I ω A B J n L := by
  have a := ps_pp_compl_l I (ω := ω) (A := A) (J := J) (n := n) hE hK h
  have b := ps_pp_compl_l I (ω := ω) (A := A) (J := J) (n := n) hE
    (fun x hx => ((h x).mp hx).1) (cm_symm_l hK h)
  exact ⟨fun hk => ⟨b.mpr hk.2, a.mp hk.1⟩, fun hl => ⟨a.mpr hl.2, b.mp hl.1⟩⟩

theorem borel_pd_one_l (hZF : M.Models ZF) {ω A B J o K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (ho : M.IsOrdinalOne o) (hK : Borel_d I ω A A B K) : Pd_d I ω A B J o K := by
  have hKB : M.MemberSubset K B := hK.elim fun c h => fun x hx => ((h.2 x).mp hx).1
  obtain ⟨L, hl, hb⟩ := borel_compl_l I hZF hB.1 hA hK
  exact ⟨(ps_one_l I hZF hB.1 hA ho).mpr (borel_an_l I hZF hB hA ha hJ hK),
    (pp_one_l I hZF hB.1 hA ho).mpr ⟨L, borel_an_l I hZF hB hA ha hJ hb, cm_symm_l hKB hl⟩⟩

end YesMetaZFC.SetTheory.Descriptive
