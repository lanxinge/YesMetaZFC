import YesMetaZFC.SetTheory.Descriptive.Projective.Iteration
import YesMetaZFC.SetTheory.Descriptive.Topology.Analytic
import YesMetaZFC.SetTheory.Descriptive.Borel.Pullback
import YesMetaZFC.SetTheory.Descriptive.Topology.ContinuousLift
import YesMetaZFC.SetTheory.Descriptive.Borel.Universe
import YesMetaZFC.SetTheory.Descriptive.Coding.RealChoice

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

theorem pd_one_borel_l (hZF : M.Models ZF) {ω A B J o K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (ho : M.IsOrdinalOne o) : Pd_d I ω A B J o K ↔ Borel_d I ω A A B K :=
  (and_congr (ps_one_l I hZF hB.1 hA ho) (pp_one_l I hZF hB.1 hA ho)).trans (suslin_l I hZF hB hA ha hJ).symm

end YesMetaZFC.SetTheory.Descriptive

/-! ## 全部内部射影层的实际集合图

每层 Σ、Π 类都是 P(B) 的内部子集，Δ 类为它们的交；再把层号送到有序对
(Σ,Π)，形成定义域恰为内部 ω 的实际函数图。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Plevel_d (ω A B J n p : M.Domain) : Prop := ∃ S P, I.Codes p S P ∧
  (∀ K, M.mem K S ↔ Ps_d I ω A B J n K) ∧ ∀ K, M.mem K P ↔ Pp_d I ω A B J n K
def plevel_m {d} (ω A B J n p : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (𝒞.code p.weaken.weaken (.bound 1) .newest) (.conj
  (.forallE (.iff (.mem .newest (.bound 2)) (ps_m (𝒞 := 𝒞) ω.weaken.weaken.weaken
    A.weaken.weaken.weaken B.weaken.weaken.weaken J.weaken.weaken.weaken n.weaken.weaken.weaken .newest)))
  (.forallE (.iff (.mem .newest (.bound 1)) (pp_m (𝒞 := 𝒞) ω.weaken.weaken.weaken
    A.weaken.weaken.weaken B.weaken.weaken.weaken J.weaken.weaken.weaken n.weaken.weaken.weaken .newest))))))
derive_free_closed plevel_m

theorem plevel_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J n p : Term d) :
    Formula.satisfies ρ (plevel_m (𝒞 := 𝒞) ω A B J n p) ↔
      Plevel_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (p.eval ρ) := by
  simp only [plevel_m, Plevel_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, ps_sat_l I hE, pp_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem plevel_unique_l (hE : Extensional M) {ω A B J n p q}
    (h : Plevel_d I ω A B J n p) (k : Plevel_d I ω A B J n q) : p = q := by
  obtain ⟨S, P, hp, hs, ht⟩ := h
  obtain ⟨S', P', hq, hs', ht'⟩ := k
  have e := hE.eq_of_same_members S S' (fun K => (hs K).trans (hs' K).symm)
  subst S'
  have e := hE.eq_of_same_members P P' (fun K => (ht K).trans (ht' K).symm)
  subst P'
  exact I.unique hp hq

theorem plevel_exists_l (hZF : M.Models ZF) (ω A B J n : M.Domain) : ∃ p, Plevel_d I ω A B J n p := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push n
  let φ : UnarySchema 5 := { body := ps_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  let ψ : UnarySchema 5 := { body := pp_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨S, hS'⟩ := ZF.separation_exists_d hZF φ ρ P
  obtain ⟨Q, hQ'⟩ := ZF.separation_exists_d hZF ψ ρ P
  have hS K : M.mem K S ↔ Ps_d I ω A B J n K := ((hS' K).trans
    (and_congr_right fun _ => ps_sat_l I hZF.1 _ _ _ _ _ _ _)).trans
      ⟨And.right, fun h => ⟨(hP K).mpr (ps_subset_l I h), h⟩⟩
  have hQ K : M.mem K Q ↔ Pp_d I ω A B J n K := ((hQ' K).trans
    (and_congr_right fun _ => pp_sat_l I hZF.1 _ _ _ _ _ _ _)).trans
      ⟨And.right, fun h => ⟨(hP K).mpr (h.elim fun _ h => fun x hx => ((h.2 x).mp hx).1), h⟩⟩
  obtain ⟨p, hp⟩ := I.total S Q
  exact ⟨p, S, Q, hp, hS, hQ⟩

theorem plevel_delta_l (hKP : M.Models KP) {ω A B J n p} (h : Plevel_d I ω A B J n p) :
    ∃ D, ∀ K, M.mem K D ↔ Pd_d I ω A B J n K := by
  obtain ⟨S, P, _, hs, hp⟩ := h
  obtain ⟨D, hD⟩ := KP.intersection_exists_d hKP S P
  exact ⟨D, fun K => (hD K).trans (and_congr (hs K) (hp K))⟩

def Phier_d (ω A B J H : M.Domain) : Prop := M.IsSetFunction I H ∧ ∀ n p,
  M.PairMember I n p H ↔ M.mem n ω ∧ Plevel_d I ω A B J n p
def phier_m {d} (ω A B J H : Term d) : Formula 1 d := .conj (Formula.isFunction 𝒞 H)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken)
    (.conj (.mem (.bound 1) ω.weaken.weaken) (plevel_m (𝒞 := 𝒞) ω.weaken.weaken
      A.weaken.weaken B.weaken.weaken J.weaken.weaken (.bound 1) .newest)))))
derive_free_closed phier_m

theorem phier_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J H : Term d) :
    Formula.satisfies ρ (phier_m (𝒞 := 𝒞) ω A B J H) ↔
      Phier_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (H.eval ρ) := by
  simp only [phier_m, Phier_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, plevel_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem phier_exists_unique_l (hZF : M.Models ZF) (ω A B J : M.Domain) :
    ∃ H, Phier_d I ω A B J H ∧ ∀ G, Phier_d I ω A B J G → G = H := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF P
  obtain ⟨V, hV⟩ := ZF.exists_cartesianProduct hZF I Q Q
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J
  let φ : BinarySchema 4 := { body := plevel_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp n p : φ.denote ρ n p ↔ Plevel_d I ω A B J n p := plevel_sat_l I hZF.1 _ _ _ _ _ _ _
  obtain ⟨H, hH, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := V)
    (fun n _ => (plevel_exists_l I hZF ω A B J n).imp fun p h => (hp n p).mpr h)
    (fun n _ p q h k => plevel_unique_l I hZF.1 ((hp n p).mp h) ((hp n q).mp k))
    (by
      intro n p _ h
      obtain ⟨S, R, hp, hs, hr⟩ := (hp n p).mp h
      exact (hV p).mpr ⟨S, (hQ S).mpr (fun K hK => (hP K).mpr (ps_subset_l I ((hs K).mp hK))),
        R, (hQ R).mpr (fun K hK => (hP K).mpr (((hr K).mp hK).elim fun L h => fun x hx => ((h.2 x).mp hx).1)), hp⟩)
  have hh : Phier_d I ω A B J H := ⟨hH.1, fun n p => (he n p).trans (and_congr_right fun _ => hp n p)⟩
  exact ⟨H, hh, fun G hg => hg.1.1.eq_of_pairMember_iff hZF.1 hh.1.1
    (fun n p => (hg.2 n p).trans (hh.2 n p).symm)⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 射影层次的内部单调性

起点是已构造的 Borel 解析表示；投影和取补将相邻层包含传递到下一层。
两次归纳都使用实际原公式分离，结论覆盖模型内任意有限层号。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ps_next_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J) :
    ∀ n, M.mem n ω → ∀ m K, M.SuccessorOf m n → Ps_d I ω A B J n K → Ps_d I ω A B J m K := by
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J
  let φ : UnarySchema 4 := {
    body := .forallE (.forallE (.imp (Formula.isSuccessor (.bound 1) (.bound 2))
      (.imp (ps_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest)
        (ps_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest)))) }
  have hp n : φ.denote ρ n ↔ ∀ m K, M.SuccessorOf m n → Ps_d I ω A B J n K → Ps_d I ω A B J m K := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_isSuccessor_iff, ps_sat_l I hZF.1]; rfl
  apply hB.1.induction (fun n => ∀ m K, M.SuccessorOf m n → Ps_d I ω A B J n K → Ps_d I ω A B J m K)
  · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨C, fun n => (hC n).trans (and_congr_right fun _ => hp n)⟩
  · intro z hz m K hm hk
    exact (ps_one_l I hZF hB.1 hA ⟨z, hz, hm⟩).mpr
      (borel_an_l I hZF hB hA ha hJ ((ps_zero_l I hZF hB.1 hz).mp hk))
  · intro n hn ih m hmn l K hlm hk
    obtain ⟨m', hm', hmω⟩ := hB.1.1.2 n hn
    have hmω := Structure.SuccessorOf.eq hZF.1 hm' hmn ▸ hmω
    obtain ⟨L, ⟨D, hd, hc⟩, hp⟩ := (ps_succ_l I hZF hB.1 hn hmn).mp hk
    exact (ps_succ_l I hZF hB.1 hmω hlm).mpr ⟨L, ⟨D, ih m D hmn hd, hc⟩, hp⟩

theorem ps_mono_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J) :
    ∀ m, M.mem m ω → ∀ n K, M.mem n m → Ps_d I ω A B J n K → Ps_d I ω A B J m K := by
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J
  let φ : UnarySchema 4 := {
    body := .forallE (.forallE (.imp (.mem (.bound 1) (.bound 2))
      (.imp (ps_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest)
        (ps_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest)))) }
  have hp m : φ.denote ρ m ↔ ∀ n K, M.mem n m → Ps_d I ω A B J n K → Ps_d I ω A B J m K := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, ps_sat_l I hZF.1]; rfl
  apply hB.1.induction (fun m => ∀ n K, M.mem n m → Ps_d I ω A B J n K → Ps_d I ω A B J m K)
  · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨C, fun m => (hC m).trans (and_congr_right fun _ => hp m)⟩
  · exact fun z hz n _ hn _ => (hz n hn).elim
  · intro m hm ih l hl n K hn hk
    apply ps_next_l I hZF hB hA ha hJ m hm l K hl
    rcases (hl n).mp hn with hn | hn
    · exact ih n K hn hk
    · exact hZF.1.eq_of_same_members n m hn ▸ hk

theorem pp_mono_l (hZF : M.Models ZF) {ω A B J n m K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hm : M.mem m ω) (hn : M.mem n m) (hK : Pp_d I ω A B J n K) : Pp_d I ω A B J m K := by
  obtain ⟨L, hl, hc⟩ := hK
  exact ⟨L, ps_mono_l I hZF hB hA ha hJ m hm n L hn hl, hc⟩

theorem pd_mono_l (hZF : M.Models ZF) {ω A B J n m K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hm : M.mem m ω) (hn : M.mem n m) (hK : Pd_d I ω A B J n K) : Pd_d I ω A B J m K :=
  ⟨ps_mono_l I hZF hB hA ha hJ m hm n K hn hK.1, pp_mono_l I hZF hB hA ha hJ hm hn hK.2⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 单个内部射影码

码为 (n,(ε,c))：n 是内部层号，ε=0 表示 Σ 分支，ε=1 表示其补，c 是 Borel 码。
解释唯一且实际存在；这里没有外部自然数长度的语法替代。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ppack_d (p n t c : M.Domain) : Prop := ∃ q, I.Codes p n q ∧ I.Codes q t c
def ppack_m {d} (p n t c : Term d) : Formula 1 d := .existsE (.conj
  (𝒞.code p.weaken n.weaken .newest) (𝒞.code .newest t.weaken c.weaken))
derive_free_closed ppack_m
theorem ppack_sat_l {d} (ρ : Env M d) (p n t c : Term d) :
    Formula.satisfies ρ (ppack_m (𝒞 := 𝒞) p n t c) ↔ Ppack_d I (p.eval ρ) (n.eval ρ) (t.eval ρ) (c.eval ρ) := by
  simp only [ppack_m, Ppack_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, Definitional.Term.eval_weaken]; rfl

theorem ppack_exists_l (n t c : M.Domain) : ∃ p, Ppack_d I p n t c := by
  obtain ⟨q, hq⟩ := I.total t c
  obtain ⟨p, hp⟩ := I.total n q
  exact ⟨p, q, hp, hq⟩
theorem ppack_unique_l {p n t c n' t' c'} (h : Ppack_d I p n t c) (k : Ppack_d I p n' t' c') :
    n = n' ∧ t = t' ∧ c = c' := by
  obtain ⟨q, hp, hq⟩ := h
  obtain ⟨q', hp', hq'⟩ := k
  obtain ⟨rfl, rfl⟩ := I.injective hp hp'
  exact ⟨rfl, I.injective hq hq'⟩

def Pcode_d (ω A p : M.Domain) : Prop := ∃ n t c, Ppack_d I p n t c ∧ M.mem n ω ∧
  ((∀ x, ¬ M.mem x t) ∨ M.IsOrdinalOne t) ∧ Bcode_d I ω A A c
def pcode_m {d} (ω A p : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.conj
  (ppack_m (𝒞 := 𝒞) p.weaken.weaken.weaken (.bound 2) (.bound 1) .newest) (.conj
  (.mem (.bound 2) ω.weaken.weaken.weaken) (.conj
  (.disj (Formula.isEmpty (.bound 1)) (Formula.isOrdinalOne (.bound 1)))
  (bcode_m (𝒞 := 𝒞) ω.weaken.weaken.weaken A.weaken.weaken.weaken A.weaken.weaken.weaken .newest))))))
derive_free_closed pcode_m

theorem pcode_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A p : Term d) :
    Formula.satisfies ρ (pcode_m (𝒞 := 𝒞) ω A p) ↔ Pcode_d I (ω.eval ρ) (A.eval ρ) (p.eval ρ) := by
  simp only [pcode_m, Pcode_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ppack_sat_l I, Formula.satisfies_mem_iff, Formula.satisfies_disj_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_isOrdinalOne_iff, bcode_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Pden_d (ω A B J p K : M.Domain) : Prop := ∃ n t c C D, Ppack_d I p n t c ∧
  Bden_d I ω A A B c C ∧ Pval_d I ω B J n C D ∧
  (((∀ x, ¬ M.mem x t) ∧ D = K) ∨ (M.IsOrdinalOne t ∧ Cm_d B D K))
def pden_m {d} (ω A B J p K : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ppack_m (𝒞 := 𝒞) p.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2)) (.conj
  (bden_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken.weaken
    A.weaken.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 1)) (.conj
  (pval_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken.weaken
    J.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 1) .newest)
  (.disj (.conj (Formula.isEmpty (.bound 3)) (Formula.extensionalEq .newest K.weaken.weaken.weaken.weaken.weaken))
    (.conj (Formula.isOrdinalOne (.bound 3))
      (cm_m B.weaken.weaken.weaken.weaken.weaken .newest K.weaken.weaken.weaken.weaken.weaken))))))))))
derive_free_closed pden_m

theorem pden_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J p K : Term d) :
    Formula.satisfies ρ (pden_m (𝒞 := 𝒞) ω A B J p K) ↔
      Pden_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (p.eval ρ) (K.eval ρ) := by
  simp only [pden_m, Pden_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ppack_sat_l I, bden_sat_l I hE, pval_sat_l I hE, Formula.satisfies_disj_iff,
    Formula.satisfies_isEmpty_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_isOrdinalOne_iff, cm_sat_l, Definitional.Term.eval_weaken]; rfl

omit I in
theorem ptag_disjoint_l {t : M.Domain} (ht : ∀ x, ¬ M.mem x t) (ho : M.IsOrdinalOne t) : False :=
  ho.elim fun z h => ht z h.2.predecessor_mem

theorem pden_unique_l (hZF : M.Models ZF) {ω A B J p K L} (hω : M.IsOmega ω)
    (h : Pden_d I ω A B J p K) (k : Pden_d I ω A B J p L) : K = L := by
  obtain ⟨n, t, c, C, D, hp, hc, hd, hv⟩ := h
  obtain ⟨n', t', c', C', D', hp', hc', hd', hv'⟩ := k
  obtain ⟨rfl, rfl, rfl⟩ := ppack_unique_l I hp hp'
  have e := hZF.1.eq_of_same_members C C' (fun x => (hc x).trans (hc' x).symm)
  subst C'
  have e := pval_unique_l I hZF hω hd hd'
  subst D'
  rcases hv with ⟨ht, hk⟩ | ⟨ht, hk⟩ <;> rcases hv' with ⟨ht', hl⟩ | ⟨ht', hl⟩
  · exact hk.symm.trans hl
  · exact (ptag_disjoint_l ht ht').elim
  · exact (ptag_disjoint_l ht' ht).elim
  · exact cm_unique_l hZF.1 hk hl

theorem pden_exists_unique_l (hZF : M.Models ZF) {ω A B J p} (hω : M.IsOmega ω) (hp : Pcode_d I ω A p) :
    ∃ K, Pden_d I ω A B J p K ∧ ∀ L, Pden_d I ω A B J p L → L = K := by
  obtain ⟨n, t, c, hp, hn, ht, _⟩ := hp
  obtain ⟨C, hc, _⟩ := bden_exists_unique_l I hZF ω A A B c
  obtain ⟨D, hd, _⟩ := pval_exists_unique_l I hZF (J := J) hω hn (fun x hx => ((hc x).mp hx).1)
  have out : ∃ K, Pden_d I ω A B J p K := by
    rcases ht with ht | ht
    · exact ⟨D, n, t, c, C, D, hp, hc, hd, Or.inl ⟨ht, rfl⟩⟩
    · obtain ⟨K, hk⟩ := cm_exists_l (ZF.modelsKP hZF) B D
      exact ⟨K, n, t, c, C, D, hp, hc, hd, Or.inr ⟨ht, hk⟩⟩
  obtain ⟨K, hK⟩ := out
  exact ⟨K, hK, fun L hL => pden_unique_l I hZF hω hL hK⟩

def Projective_d (ω A B J K : M.Domain) : Prop := ∃ n, M.mem n ω ∧ (Ps_d I ω A B J n K ∨ Pp_d I ω A B J n K)
def projective_m {d} (ω A B J K : Term d) : Formula 1 d := Formula.existsMem ω (.disj
  (ps_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken J.weaken .newest K.weaken)
  (pp_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken J.weaken .newest K.weaken))
derive_free_closed projective_m

theorem projective_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J K : Term d) :
    Formula.satisfies ρ (projective_m (𝒞 := 𝒞) ω A B J K) ↔
      Projective_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (K.eval ρ) := by
  simp only [projective_m, Projective_d, Formula.satisfies_existsMem_iff, Formula.satisfies_disj_iff,
    ps_sat_l I hE, pp_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem projective_code_l (hZF : M.Models ZF) {ω A B J K} (hω : M.IsOmega ω) :
    Projective_d I ω A B J K ↔ ∃ p, Pcode_d I ω A p ∧ Pden_d I ω A B J p K := by
  constructor
  · rintro ⟨n, hn, hk | hk⟩
    · obtain ⟨c, C, hc, hC, hv⟩ := hk
      obtain ⟨t, ht⟩ := KP.exists_empty (ZF.modelsKP hZF)
      obtain ⟨p, hp⟩ := ppack_exists_l I n t c
      exact ⟨p, ⟨n, t, c, hp, hn, Or.inl ht, hc⟩, n, t, c, C, K, hp, hC, hv, Or.inl ⟨ht, rfl⟩⟩
    · obtain ⟨L, ⟨c, C, hc, hC, hv⟩, hL⟩ := hk
      obtain ⟨t, ht, _⟩ := hω.exists_ordinalOne_mem
      obtain ⟨p, hp⟩ := ppack_exists_l I n t c
      exact ⟨p, ⟨n, t, c, hp, hn, Or.inr ht, hc⟩, n, t, c, C, L, hp, hC, hv, Or.inr ⟨ht, hL⟩⟩
  · rintro ⟨p, ⟨n, t, c, hp, hn, _, hc⟩, n', t', c', C, D, hp', hC, hv, ht⟩
    obtain ⟨rfl, rfl, rfl⟩ := ppack_unique_l I hp hp'
    refine ⟨n, hn, ?_⟩
    exact ht.elim (fun h => Or.inl ⟨c, C, hc, hC, h.2 ▸ hv⟩)
      (fun h => Or.inr ⟨D, ⟨c, C, hc, hC, hv⟩, h.2⟩)

theorem projective_compl_l (hKP : M.Models KP) {ω A B J K} (hK : Projective_d I ω A B J K) :
    ∃ L, Cm_d B K L ∧ Projective_d I ω A B J L := by
  obtain ⟨n, hn, hk | hk⟩ := hK
  · obtain ⟨L, hl⟩ := cm_exists_l hKP B K
    exact ⟨L, hl, n, hn, Or.inr ⟨K, hk, hl⟩⟩
  · obtain ⟨L, hl, hc⟩ := hk
    exact ⟨L, cm_symm_l (ps_subset_l I hl) hc, n, hn, Or.inl hl⟩

theorem projective_collection_l (hZF : M.Models ZF) (ω A B J : M.Domain) :
    ∃ C, ∀ K, M.mem K C ↔ Projective_d I ω A B J K := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J
  let φ : UnarySchema 4 := { body := projective_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ P
  refine ⟨C, fun K => ((hC K).trans (and_congr_right fun _ => projective_sat_l I hZF.1 _ _ _ _ _ _)).trans
    ⟨And.right, fun h => ⟨?_, h⟩⟩⟩
  obtain ⟨_, _, h | h⟩ := h
  · exact (hP K).mpr (ps_subset_l I h)
  · exact (hP K).mpr (h.elim fun L h => fun x hx => ((h.2 x).mp hx).1)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 射影码的补与交替量词

直接改写 (层号,极性,Borel 码)：补仅翻转极性；增加量词还把层号取后继。
改写关系由原公式给出且输出唯一，因而可作用于整个内部码族。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ppack_ext_l {p q n t c} (h : Ppack_d I p n t c) (k : Ppack_d I q n t c) : p = q := by
  obtain ⟨a, ha, hb⟩ := h
  obtain ⟨b, hc, hd⟩ := k
  exact I.unique ha (I.unique hd hb ▸ hc)

/-- 指定层号和极性的合法码；层号依然是内部集合。 -/
def Pc_d (ω A n t p : M.Domain) : Prop := M.mem n ω ∧
  ((∀ x, ¬ M.mem x t) ∨ M.IsOrdinalOne t) ∧ ∃ c, Ppack_d I p n t c ∧ Bcode_d I ω A A c
def pc_m {d} (ω A n t p : Term d) : Formula 1 d := .conj (.mem n ω) (.conj
  (.disj (Formula.isEmpty t) (Formula.isOrdinalOne t)) (.existsE (.conj
    (ppack_m (𝒞 := 𝒞) p.weaken n.weaken t.weaken .newest)
    (bcode_m (𝒞 := 𝒞) ω.weaken A.weaken A.weaken .newest))))
derive_free_closed pc_m
theorem pc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A n t p : Term d) :
    Formula.satisfies ρ (pc_m (𝒞 := 𝒞) ω A n t p) ↔
      Pc_d I (ω.eval ρ) (A.eval ρ) (n.eval ρ) (t.eval ρ) (p.eval ρ) := by
  simp only [pc_m, Pc_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_isEmpty_iff, Formula.satisfies_isOrdinalOne_iff,
    Formula.satisfies_exists_iff, ppack_sat_l I, bcode_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem pc_code_l {ω A n t p} (h : Pc_d I ω A n t p) : Pcode_d I ω A p := by
  obtain ⟨hn, ht, c, hp, hc⟩ := h
  exact ⟨n, t, c, hp, hn, ht, hc⟩

theorem pden_subset_l {ω A B J p K} (h : Pden_d I ω A B J p K) : M.MemberSubset K B := by
  obtain ⟨n, _, _, _, D, _, _, hv, ht⟩ := h
  obtain ⟨H, hH, hn⟩ := hv
  exact ht.elim (fun h => h.2 ▸ hH.bound _ D hn) (fun h x hx => ((h.2 x).mp hx).1)

theorem pc_sigma_l {ω A B J n z K} (hn : M.mem n ω) (hz : ∀ x, ¬ M.mem x z) :
    Ps_d I ω A B J n K ↔ ∃ p, Pc_d I ω A n z p ∧ Pden_d I ω A B J p K := by
  constructor
  · rintro ⟨c, C, hc, hC, hv⟩
    obtain ⟨p, hp⟩ := ppack_exists_l I n z c
    exact ⟨p, ⟨hn, Or.inl hz, c, hp, hc⟩, n, z, c, C, K, hp, hC, hv, Or.inl ⟨hz, rfl⟩⟩
  · rintro ⟨p, ⟨_, _, c, hp, hc⟩, m, t, d, C, D, hq, hC, hv, ht⟩
    obtain ⟨hm, ht', hd⟩ := ppack_unique_l I hq hp
    subst m t d
    exact ht.elim (fun h => ⟨c, C, hc, hC, h.2 ▸ hv⟩) (fun h => (ptag_disjoint_l hz h.1).elim)

theorem pc_pi_l {ω A B J n o K} (hn : M.mem n ω) (ho : M.IsOrdinalOne o) :
    Pp_d I ω A B J n K ↔ ∃ p, Pc_d I ω A n o p ∧ Pden_d I ω A B J p K := by
  constructor
  · rintro ⟨D, ⟨c, C, hc, hC, hv⟩, hd⟩
    obtain ⟨p, hp⟩ := ppack_exists_l I n o c
    exact ⟨p, ⟨hn, Or.inr ho, c, hp, hc⟩, n, o, c, C, D, hp, hC, hv, Or.inr ⟨ho, hd⟩⟩
  · rintro ⟨p, ⟨_, _, c, hp, hc⟩, m, t, d, C, D, hq, hC, hv, ht⟩
    obtain ⟨hm, ht', hd⟩ := ppack_unique_l I hq hp
    subst m t d
    exact ht.elim (fun h => (ptag_disjoint_l h.1 ho).elim) (fun h => ⟨D, ⟨c, C, hc, hC, hv⟩, h.2⟩)

/-- false 为补码，true 为下一层的对偶量词码。两种操作均保留原 Borel 矩阵。 -/
def Pedit_d (b : Bool) (p q : M.Domain) : Prop := ∃ n m t u c,
  Ppack_d I p n t c ∧ Ppack_d I q m u c ∧ (if b then M.SuccessorOf m n else m = n) ∧
  (((∀ x, ¬ M.mem x t) ∧ M.IsOrdinalOne u) ∨ (M.IsOrdinalOne t ∧ ∀ x, ¬ M.mem x u))
def pedit_m (b : Bool) {d} (p q : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ppack_m (𝒞 := 𝒞) p.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 2) .newest) (.conj
    (ppack_m (𝒞 := 𝒞) q.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) .newest) (.conj
    (if b then Formula.isSuccessor (.bound 3) (.bound 4) else Formula.extensionalEq (.bound 3) (.bound 4))
    (.disj (.conj (Formula.isEmpty (.bound 2)) (Formula.isOrdinalOne (.bound 1)))
      (.conj (Formula.isOrdinalOne (.bound 2)) (Formula.isEmpty (.bound 1)))))))))))
@[simp] theorem pedit_closed_l (b : Bool) {d} (p q : Term d)
    (hp : p.freeSupport = []) (hq : q.freeSupport = []) : (pedit_m (𝒞 := 𝒞) b p q).FreeClosed := by
  cases b <;> simp -implicitDefEqProofs [pedit_m, Definitional.Formula.FreeClosed, hp, hq]
theorem pedit_sat_l (hE : Extensional M) (b : Bool) {d} (ρ : Env M d) (p q : Term d) :
    Formula.satisfies ρ (pedit_m (𝒞 := 𝒞) b p q) ↔ Pedit_d I b (p.eval ρ) (q.eval ρ) := by
  cases b <;> simp only [pedit_m, Pedit_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, ppack_sat_l I,
    Formula.satisfies_isSuccessor_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_disj_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_isOrdinalOne_iff, Definitional.Term.eval_weaken] <;> rfl

theorem pedit_unique_l (hE : Extensional M) {b p q r} (h : Pedit_d I b p q) (k : Pedit_d I b p r) : q = r := by
  obtain ⟨n, m, t, u, c, hp, hq, hm, ht⟩ := h
  obtain ⟨n', m', t', u', c', hp', hr, hm', ht'⟩ := k
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp hp'
  subst n' t' c'
  have e : m = m' := by
    cases b
    · exact hm.trans hm'.symm
    · exact Structure.SuccessorOf.eq hE hm hm'
  subst m'
  have e : u = u' := by
    rcases ht with ⟨ht, hu⟩ | ⟨ht, hu⟩ <;> rcases ht' with ⟨ht', hu'⟩ | ⟨ht', hu'⟩
    · exact Structure.IsOrdinalOne.eq hE hu hu'
    · exact (ptag_disjoint_l ht ht').elim
    · exact (ptag_disjoint_l ht' ht).elim
    · exact hE.eq_of_same_members u u' (fun x => iff_of_false (hu x) (hu' x))
  exact ppack_ext_l I hq (e.symm ▸ hr)

theorem pedit_exists_l (hKP : M.Models KP) {ω A p} (hω : M.IsOmega ω)
    (hp : Pcode_d I ω A p) (b : Bool) : ∃ q, Pedit_d I b p q ∧ Pcode_d I ω A q := by
  obtain ⟨n, t, c, hp, hn, ht, hc⟩ := hp
  obtain ⟨z, hz⟩ := KP.exists_empty hKP
  obtain ⟨o, ho⟩ := KP.exists_successor hKP z
  have tag : ∃ u, ((∀ x, ¬ M.mem x t) ∧ M.IsOrdinalOne u) ∨ (M.IsOrdinalOne t ∧ ∀ x, ¬ M.mem x u) :=
    ht.elim (fun h => ⟨o, Or.inl ⟨h, z, hz, ho⟩⟩) (fun h => ⟨z, Or.inr ⟨h, hz⟩⟩)
  obtain ⟨u, hu⟩ := tag
  have level : ∃ m, M.mem m ω ∧ (if b then M.SuccessorOf m n else m = n) := by
    cases b
    · exact ⟨n, hn, rfl⟩
    · obtain ⟨m, hm, hmω⟩ := hω.1.2 n hn
      exact ⟨m, hmω, hm⟩
  obtain ⟨m, hmω, hm⟩ := level
  obtain ⟨q, hq⟩ := ppack_exists_l I m u c
  exact ⟨q, ⟨n, m, t, u, c, hp, hq, hm, hu⟩,
    m, u, c, hq, hmω, hu.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2), hc⟩

theorem pedit_compl_l (hE : Extensional M) {ω A B J p q K L} (h : Pedit_d I false p q)
    (hp : Pden_d I ω A B J p K) (hl : Cm_d B K L) : Pden_d I ω A B J q L := by
  obtain ⟨n, m, t, u, c, hp', hq, hm, ht⟩ := h
  obtain ⟨n', t', c', C, D, hp, hC, hv, hk⟩ := hp
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp hp'
  subst n' t' c'
  have hm : m = n := hm
  subst m
  refine ⟨n, u, c, C, D, hq, hC, hv, ?_⟩
  rcases ht with ⟨ht, hu⟩ | ⟨ht, hu⟩ <;> rcases hk with ⟨ht', hk⟩ | ⟨ht', hk⟩
  · exact Or.inr ⟨hu, hk.symm ▸ hl⟩
  · exact (ptag_disjoint_l ht ht').elim
  · exact (ptag_disjoint_l ht' ht).elim
  · obtain ⟨H, hH, hn⟩ := hv
    have hd := cm_symm_l (hH.bound n D hn) hk
    exact Or.inl ⟨hu, cm_unique_l hE hd hl⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 射影码量词的集合语义

Π¹ₙ 上加存在量词得到 Σ¹ₙ₊₁，Σ¹ₙ 上加全称量词得到 Π¹ₙ₊₁。
全称量词也直接给出逐实数判据；自由变量和见证均量化于内部 Baire 空间。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def All_d (B J R K : M.Domain) : Prop := ∀ x, M.mem x K ↔ M.mem x B ∧
  ∀ y z, M.mem y B → M.mem z B → Rp_d I J x y z → M.mem z R
def all_m {d} (B J R K : Term d) : Formula 1 d := .forallE (.iff (.mem .newest K.weaken)
  (.conj (.mem .newest B.weaken) (.forallE (.forallE
    (.imp (.mem (.bound 1) B.weaken.weaken.weaken) (.imp (.mem .newest B.weaken.weaken.weaken)
      (.imp (rp_m (𝒞 := 𝒞) J.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
        (.mem .newest R.weaken.weaken.weaken))))))))
derive_free_closed all_m
theorem all_sat_l {d} (ρ : Env M d) (B J R K : Term d) :
    Formula.satisfies ρ (all_m (𝒞 := 𝒞) B J R K) ↔
      All_d I (B.eval ρ) (J.eval ρ) (R.eval ρ) (K.eval ρ) := by
  simp only [all_m, All_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_imp_iff, rp_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem all_compl_l {B J R C D K} (hc : Cm_d B R C) (hd : Pr_d I B J C D)
    (hk : Cm_d B D K) : All_d I B J R K := by
  classical
  intro x
  refine (hk x).trans (and_congr_right fun hx => ⟨?_, ?_⟩)
  · intro hn y z hy hz hp
    exact Classical.byContradiction (fun hr => hn ((hd x).mpr ⟨hx, y, z, hy, hz, hp, (hc z).mpr ⟨hz, hr⟩⟩))
  · intro h hxD
    obtain ⟨_, y, z, hy, hz, hp, hzC⟩ := (hd x).mp hxD
    exact ((hc z).mp hzC).2 (h y z hy hz hp)

theorem all_unique_l (hE : Extensional M) {B J R K L} (h : All_d I B J R K) (k : All_d I B J R L) : K = L :=
  hE.eq_of_same_members K L (fun x => (h x).trans (k x).symm)

theorem all_exists_l (hZF : M.Models ZF) (B J R : M.Domain) : ∃ K, All_d I B J R K := by
  obtain ⟨C, hc⟩ := cm_exists_l (ZF.modelsKP hZF) B R
  obtain ⟨D, hd⟩ := pr_exists_l I hZF B J C
  obtain ⟨K, hk⟩ := cm_exists_l (ZF.modelsKP hZF) B D
  exact ⟨K, all_compl_l I hc hd hk⟩

/-- 补码与补集同时构造；仅要求 KP 和已有解释。 -/
theorem pcode_compl_l (hKP : M.Models KP) {ω A B J p K} (hω : M.IsOmega ω)
    (hp : Pcode_d I ω A p) (hk : Pden_d I ω A B J p K) :
    ∃ q L, Pedit_d I false p q ∧ Pcode_d I ω A q ∧ Cm_d B K L ∧ Pden_d I ω A B J q L := by
  obtain ⟨q, hq, hq'⟩ := pedit_exists_l I hKP hω hp false
  obtain ⟨L, hl⟩ := cm_exists_l hKP B K
  exact ⟨q, L, hq, hq', hl, pedit_compl_l I hKP.1 hq hk hl⟩

theorem pedit_proj_l (hZF : M.Models ZF) {ω A B J n o p q K L} (hω : M.IsOmega ω)
    (hc : Pc_d I ω A n o p) (ho : M.IsOrdinalOne o) (he : Pedit_d I true p q)
    (hk : Pden_d I ω A B J p K) (hl : Pr_d I B J K L) : Pden_d I ω A B J q L := by
  obtain ⟨hn, _, c, hp, _⟩ := hc
  obtain ⟨n', m, t, u, c', hp', hq, hm, ht⟩ := he
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp' hp
  subst n' t c'
  obtain ⟨n', t, c', C, D, hp', hC, hv, hd⟩ := hk
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp' hp
  subst n' t c'
  have hu : ∀ x, ¬ M.mem x u := ht.elim (fun h => (ptag_disjoint_l h.1 ho).elim) And.right
  have hd : Cm_d B D K := hd.elim (fun h => (ptag_disjoint_l h.1 ho).elim) And.right
  exact ⟨m, u, c, C, L, hq, hC, (pval_succ_l I hZF hω hn hm).mpr ⟨D, hv, K, hd, hl⟩, Or.inl ⟨hu, rfl⟩⟩

theorem pedit_all_l (hZF : M.Models ZF) {ω A B J n z p q K L} (hω : M.IsOmega ω)
    (hc : Pc_d I ω A n z p) (hz : ∀ x, ¬ M.mem x z) (he : Pedit_d I true p q)
    (hk : Pden_d I ω A B J p K) (hl : All_d I B J K L) : Pden_d I ω A B J q L := by
  obtain ⟨hn, _, c, hp, _⟩ := hc
  obtain ⟨n', m, t, u, c', hp', hq, hm, ht⟩ := he
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp' hp
  subst n' t c'
  obtain ⟨n', t, c', C, D, hp', hC, hv, hd⟩ := hk
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp' hp
  subst n' t c'
  have hu : M.IsOrdinalOne u := ht.elim And.right (fun h => (ptag_disjoint_l hz h.1).elim)
  have e : D = K := hd.elim And.right (fun h => (ptag_disjoint_l hz h.1).elim)
  subst D
  obtain ⟨V, hvC⟩ := cm_exists_l (ZF.modelsKP hZF) B K
  obtain ⟨W, hw⟩ := pr_exists_l I hZF B J V
  obtain ⟨L', hl'⟩ := cm_exists_l (ZF.modelsKP hZF) B W
  have e := all_unique_l I hZF.1 (all_compl_l I hvC hw hl') hl
  exact ⟨m, u, c, C, W, hq, hC, (pval_succ_l I hZF hω hn hm).mpr ⟨K, hv, V, hvC, hw⟩,
    Or.inr ⟨hu, e ▸ hl'⟩⟩

/-- 同一实际改写给出所有层的量词运算；极性决定存在或全称。 -/
theorem pcode_quant_l (hZF : M.Models ZF) {ω A B J n t p K} (hω : M.IsOmega ω)
    (hc : Pc_d I ω A n t p) (hk : Pden_d I ω A B J p K) :
    ∃ m u q L, M.SuccessorOf m n ∧ Pc_d I ω A m u q ∧ Pedit_d I true p q ∧
      Pden_d I ω A B J q L ∧
      (((∀ x, ¬ M.mem x t) ∧ M.IsOrdinalOne u ∧ All_d I B J K L) ∨
       (M.IsOrdinalOne t ∧ (∀ x, ¬ M.mem x u) ∧ Pr_d I B J K L)) := by
  obtain ⟨q, he, hq⟩ := pedit_exists_l I (ZF.modelsKP hZF) hω (pc_code_l I hc) true
  obtain ⟨n', m, t', u, c, hp, hq', hm, ht⟩ := he
  obtain ⟨d, hd, _⟩ := hc.2.2
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hp hd
  subst n' t' d
  obtain ⟨m', u', c', hq'', hmω, _, hc'⟩ := hq
  obtain ⟨en, et, ec⟩ := ppack_unique_l I hq'' hq'
  subst m' u' c'
  have he : Pedit_d I true p q := ⟨n, m, t, u, c, hp, hq', hm, ht⟩
  have out : Pc_d I ω A m u q := ⟨hmω, ht.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2), c, hq', hc'⟩
  rcases ht with ⟨ht, hu⟩ | ⟨ht, hu⟩
  · obtain ⟨L, hl⟩ := all_exists_l I hZF B J K
    exact ⟨m, u, q, L, hm, out, he, pedit_all_l I hZF hω hc ht he hk hl, Or.inl ⟨ht, hu, hl⟩⟩
  · obtain ⟨L, hl⟩ := pr_exists_l I hZF B J K
    exact ⟨m, u, q, L, hm, out, he, pedit_proj_l I hZF hω hc ht he hk hl, Or.inr ⟨ht, hu, hl⟩⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 任意内部射影层的统一连续逆像码

在 B^B 中迭代 f↦f×id，再对原 Borel 矩阵作一次逆像替换。
该算法在每个内部层号都有唯一输出，故可逐项处理内部可数码族。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Lgraph_d (B J X L : M.Domain) : Prop := M.IsFunctionSpace I X B B ∧
  M.IsSetFunctionFromTo I L X X ∧ ∀ f g, M.PairMember I f g L ↔ M.mem f X ∧ Lift_d I B J f g
def lgraph_m {d} (B J X L : Term d) : Formula 1 d := .conj (Formula.isFunctionSpace 𝒞 X B B) (.conj
  (Formula.isFunctionFromTo 𝒞 L X X) (.forallE (.forallE (.iff
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest L.weaken.weaken) (.conj (.mem (.bound 1) X.weaken.weaken)
      (lift_m (𝒞 := 𝒞) B.weaken.weaken J.weaken.weaken (.bound 1) .newest))))))
@[simp] theorem lgraph_closed_l {d} (B J X L : Term d) (hB : B.freeSupport = []) (hJ : J.freeSupport = [])
    (hX : X.freeSupport = []) (hL : L.freeSupport = []) : (lgraph_m (𝒞 := 𝒞) B J X L).FreeClosed := by
  simp -implicitDefEqProofs [lgraph_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed, hB, hJ, hX, hL]
theorem lgraph_sat_l (hE : Extensional M) {d} (ρ : Env M d) (B J X L : Term d) :
    Formula.satisfies ρ (lgraph_m (𝒞 := 𝒞) B J X L) ↔ Lgraph_d I (B.eval ρ) (J.eval ρ) (X.eval ρ) (L.eval ρ) := by
  simp only [lgraph_m, Lgraph_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionSpace_iff I hE,
    Formula.satisfies_isFunctionFromTo_iff I hE, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff, lift_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem lgraph_exists_l (hZF : M.Models ZF) {ω B J} (hB : Baire_d I ω B) (hJ : Npair_d I ω J) :
    ∃ X L, Lgraph_d I B J X L := by
  obtain ⟨X, hX⟩ := ZF.exists_functionSpace hZF I B B
  let ρ : Env M 2 := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push J
  let φ : BinarySchema 2 := { body := lift_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp f g : φ.denote ρ f g ↔ Lift_d I B J f g := lift_sat_l I hZF.1 _ _ _ _ _
  obtain ⟨L, hL, hl⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := X) (target := X)
    (fun f hf => (lift_exists_l I hZF hB hJ ((hX f).mp hf)).imp fun g hg => (hp f g).mpr hg)
    (fun _ _ _ _ h k => lift_unique_l I hZF.1 ((hp _ _).mp h) ((hp _ _).mp k))
    (fun _ g _ h => (hX g).mpr ((hp _ _).mp h).1)
  exact ⟨X, L, hX, hL, fun f g => (hl f g).trans (and_congr_right fun _ => hp f g)⟩

theorem lift_iter_cont_l (hZF : M.Models ZF) {ω A B J X L f n g} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hL : Lgraph_d I B J X L)
    (hf : Cont_d I A B f) (h : Iv_d I ω X L f n g) : Cont_d I A B g := by
  obtain ⟨H, hH, hg⟩ := h
  let ρ : Env M 3 := ((⟨fun _ => A, fun _ => A⟩ : Env M 1).push B).push H
  let φ : UnarySchema 3 := { body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
    (cont_m (𝒞 := 𝒞) (.bound 4) (.bound 3) .newest)) }
  have hp n : φ.denote ρ n ↔ ∀ g, M.PairMember I n g H → Cont_d I A B g := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, cont_sat_l I hZF.1]; rfl
  have all : ∀ n, M.mem n ω → ∀ g, M.PairMember I n g H → Cont_d I A B g := by
    apply hB.1.induction
    · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨C, fun n => (hC n).trans (and_congr_right fun _ => hp n)⟩
    · intro z hz g hg
      exact hH.1.1.2 z f g (hH.2.1 z hz) hg ▸ hf
    · intro n hn ih m hm g hg
      obtain ⟨f', _, hf'⟩ := hH.1.2.2 n hn
      exact lift_cont_l I hZF hB hA hJ (ih f' hf') ((hL.2.2 f' g).mp (hH.2.2 n m f' g hm hf' hg)).2
  exact all n (hH.1.input_mem_of_pairMember hg) g hg

theorem pval_pull_l (hZF : M.Models ZF) {ω A B J X L} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hL : Lgraph_d I B J X L) :
    ∀ n, M.mem n ω → ∀ f g C D K V, Cont_d I A B f → Iv_d I ω X L f n g →
      Ip_d I B g C D → Pval_d I ω B J n C K → Pval_d I ω B J n D V → Ip_d I B f K V := by
  let ρ : Env M 6 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push X).push L
  let φ : UnarySchema 6 := { body := .forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
    (cont_m (𝒞 := 𝒞) (.bound 11) (.bound 10) (.bound 5)) (.imp
    (iv_m (𝒞 := 𝒞) (.bound 12) (.bound 8) (.bound 7) (.bound 5) (.bound 6) (.bound 4)) (.imp
    (ip_m (𝒞 := 𝒞) (.bound 10) (.bound 4) (.bound 3) (.bound 2)) (.imp
    (pval_m (𝒞 := 𝒞) (.bound 12) (.bound 10) (.bound 9) (.bound 6) (.bound 3) (.bound 1)) (.imp
    (pval_m (𝒞 := 𝒞) (.bound 12) (.bound 10) (.bound 9) (.bound 6) (.bound 2) .newest)
    (ip_m (𝒞 := 𝒞) (.bound 10) (.bound 5) (.bound 1) .newest))))))))))) }
  have hp n : φ.denote ρ n ↔ ∀ f g C D K V, Cont_d I A B f → Iv_d I ω X L f n g →
      Ip_d I B g C D → Pval_d I ω B J n C K → Pval_d I ω B J n D V → Ip_d I B f K V := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      cont_sat_l I hZF.1, iv_sat_l I hZF.1, ip_sat_l I, pval_sat_l I hZF.1]; rfl
  apply hB.1.induction
  · obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨T, fun n => (hT n).trans (and_congr_right fun _ => hp n)⟩
  · intro z hz f g C D K V hf hg hip hK hV
    have e := (iv_zero_l I hZF hB.1 hL.2.1 ((hL.1 f).mpr hf.1) hz).mp hg
    subst g
    obtain ⟨H, hH, hk⟩ := hK
    obtain ⟨G, hG, hv⟩ := hV
    exact hH.fn.2 z C K (hH.zero z hz) hk ▸ hG.fn.2 z D V (hG.zero z hz) hv ▸ hip
  · intro n hn ih m hm f g C D K V hf hg hip hK hV
    obtain ⟨f', _, hf'⟩ := hL.2.1.2.2 f ((hL.1 f).mpr hf.1)
    have hl := ((hL.2.2 f f').mp hf').2
    have hg' := (iv_shift_l I hZF hB.1 hL.2.1 hn hm hf').mp hg
    obtain ⟨K', hk, hK⟩ := (pval_succ_l I hZF hB.1 hn hm).mp hK
    obtain ⟨V', hv, hV⟩ := (pval_succ_l I hZF hB.1 hn hm).mp hV
    exact lift_step_l I hZF hB hJ hf.1 hl
      (ih f' g C D K' V' (lift_cont_l I hZF hB hA hJ hf hl) hg' hip hk hv) hK hV

def Ppull_d (ω A E X L f n c d : M.Domain) : Prop := ∃ g, Iv_d I ω X L f n g ∧ Bpull_d I ω A E g c d
def ppull_m {d} (ω A E X L f n c e : Term d) : Formula 1 d := .existsE (.conj
  (iv_m (𝒞 := 𝒞) ω.weaken X.weaken L.weaken f.weaken n.weaken .newest)
  (bpull_m (𝒞 := 𝒞) ω.weaken A.weaken E.weaken .newest c.weaken e.weaken))
derive_free_closed ppull_m
theorem ppull_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A E X L f n c e : Term d) :
    Formula.satisfies ρ (ppull_m (𝒞 := 𝒞) ω A E X L f n c e) ↔
      Ppull_d I (ω.eval ρ) (A.eval ρ) (E.eval ρ) (X.eval ρ) (L.eval ρ) (f.eval ρ) (n.eval ρ) (c.eval ρ) (e.eval ρ) := by
  simp only [ppull_m, Ppull_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    iv_sat_l I hE, bpull_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem ppull_unique_l (hZF : M.Models ZF) {ω A E X L f n c d e} (hω : M.IsOmega ω)
    (hL : M.IsSetFunction I L) (h : Ppull_d I ω A E X L f n c d) (k : Ppull_d I ω A E X L f n c e) : d = e := by
  obtain ⟨g, hg, hd⟩ := h
  obtain ⟨g', hg', he⟩ := k
  exact bpull_unique_l I hZF.1 hd (iv_unique_l I hZF hω hL hg' hg ▸ he)

theorem ppull_exists_l (hZF : M.Models ZF) {ω A B J E X L f n c} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (he : M.IsSetInjectionFromTo I E A ω) (hL : Lgraph_d I B J X L)
    (hf : M.IsSetFunctionFromTo I f B B) (hn : M.mem n ω) (hc : Bcode_d I ω A A c) :
    ∃ d, Ppull_d I ω A E X L f n c d ∧ Bcode_d I ω A A d := by
  obtain ⟨g, hg⟩ := iv_exists_l I hZF hB.1 hL.2.1 ((hL.1 f).mpr hf) hn
  obtain ⟨d, hd, hd'⟩ := bpull_exists_l I hZF hB.1 hA he hc
  exact ⟨d, ⟨g, hg, hd⟩, hd'⟩

theorem ppull_value_l (hZF : M.Models ZF) {ω A B J E X L f n c d C D K V} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (he : M.IsSetInjectionFromTo I E A ω)
    (hL : Lgraph_d I B J X L) (hf : Cont_d I A B f) (hn : M.mem n ω) (hc : Bcode_d I ω A A c)
    (h : Ppull_d I ω A E X L f n c d) (hC : Bden_d I ω A A B c C) (hD : Bden_d I ω A A B d D)
    (hK : Pval_d I ω B J n C K) (hV : Pval_d I ω B J n D V) : Ip_d I B f K V := by
  obtain ⟨g, hg, hd⟩ := h
  have hgc := lift_iter_cont_l I hZF hB hA hJ hL hf hg
  have hip : Ip_d I B g C D := by
    intro x
    refine (hD x).trans (and_congr_right fun hx => ⟨?_, ?_⟩)
    · intro hd'
      obtain ⟨y, hy, hxy⟩ := hgc.1.2.2 x hx
      exact ⟨y, hxy, (hC y).mpr ⟨hy, (bpull_correct_l I hZF hB.1 hA he hgc hc hd x y hxy).mp hd'⟩⟩
    · rintro ⟨y, hxy, hy⟩
      exact (bpull_correct_l I hZF hB.1 hA he hgc hc hd x y hxy).mpr ((hC y).mp hy).2
  exact pval_pull_l I hZF hB hA hJ hL n hn f g C D K V hf hg hip hK hV

end YesMetaZFC.SetTheory.Descriptive

/-! ## 射影矩阵求值及可数行族的合取、析取 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Pm_d (ω A B J n c x : M.Domain) : Prop := ∃ C K,
  Bden_d I ω A A B c C ∧ Pval_d I ω B J n C K ∧ M.mem x K
def pm_m {d} (ω A B J n c x : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (bden_m (𝒞 := 𝒞) ω.weaken.weaken A.weaken.weaken A.weaken.weaken B.weaken.weaken c.weaken.weaken (.bound 1)) (.conj
  (pval_m (𝒞 := 𝒞) ω.weaken.weaken B.weaken.weaken J.weaken.weaken n.weaken.weaken (.bound 1) .newest)
  (.mem x.weaken.weaken .newest))))
derive_free_closed pm_m
theorem pm_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J n c x : Term d) :
    Formula.satisfies ρ (pm_m (𝒞 := 𝒞) ω A B J n c x) ↔
      Pm_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (c.eval ρ) (x.eval ρ) := by
  simp only [pm_m, Pm_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bden_sat_l I hE, pval_sat_l I hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

theorem pm_mem_l (hZF : M.Models ZF) {ω A B J n c C K x} (hω : M.IsOmega ω)
    (hc : Bden_d I ω A A B c C) (hk : Pval_d I ω B J n C K) : M.mem x K ↔ Pm_d I ω A B J n c x := by
  refine ⟨fun hx => ⟨C, K, hc, hk, hx⟩, fun ⟨D, L, hd, hl, hx⟩ => ?_⟩
  have e := hZF.1.eq_of_same_members D C (fun x => (hd x).trans (hc x).symm)
  exact pval_unique_l I hZF hω (e ▸ hl) hk ▸ hx

theorem pm_set_l (hZF : M.Models ZF) {ω A B J n c} (hω : M.IsOmega ω) (hn : M.mem n ω) :
    ∃ K, ∀ x, M.mem x K ↔ Pm_d I ω A B J n c x := by
  obtain ⟨C, hc, _⟩ := bden_exists_unique_l I hZF ω A A B c
  obtain ⟨K, hk, _⟩ := pval_exists_unique_l I hZF (J := J) hω hn (fun x hx => ((hc x).mp hx).1)
  exact ⟨K, fun _ => pm_mem_l I hZF hω hc hk⟩

theorem pm_subset_l {ω A B J n c x} (h : Pm_d I ω A B J n c x) : M.mem x B := by
  obtain ⟨_, K, _, hv, hx⟩ := h
  obtain ⟨H, hH, hn⟩ := hv
  exact hH.bound n K hn x hx

theorem pm_zero_l (hZF : M.Models ZF) {ω A B J z c x} (hω : M.IsOmega ω) (hz : ∀ v, ¬ M.mem v z) :
    Pm_d I ω A B J z c x ↔ M.mem x B ∧ Bsat_d I ω A A c x := by
  obtain ⟨C, hc, _⟩ := bden_exists_unique_l I hZF ω A A B c
  have hv := (pval_zero_l I hZF (J := J) hω hz (fun x hx => ((hc x).mp hx).1)).mpr rfl
  exact (pm_mem_l I hZF hω hc hv).symm.trans (hc x)

theorem pm_succ_l (hZF : M.Models ZF) {ω A B J n m c x} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) : Pm_d I ω A B J m c x ↔ M.mem x B ∧ ∃ y z,
      M.mem y B ∧ M.mem z B ∧ Rp_d I J x y z ∧ ¬ Pm_d I ω A B J n c z := by
  obtain ⟨C, hc, _⟩ := bden_exists_unique_l I hZF ω A A B c
  obtain ⟨K, hk, _⟩ := pval_exists_unique_l I hZF (J := J) hω hn (fun x hx => ((hc x).mp hx).1)
  obtain ⟨D, hd⟩ := cm_exists_l (ZF.modelsKP hZF) B K
  obtain ⟨L, hl⟩ := pr_exists_l I hZF B J D
  have hv := (pval_succ_l I hZF hω hn hm).mpr ⟨K, hk, D, hd, hl⟩
  refine (pm_mem_l I hZF hω hc hv).symm.trans ((hl x).trans (and_congr_right fun _ =>
    exists_congr fun y => exists_congr fun z => and_congr_right fun _ => and_congr_right fun hz => and_congr_right fun _ => ?_))
  exact (hd z).trans ⟨fun h => (not_congr (pm_mem_l I hZF hω hc hk)).mp h.2,
    fun h => ⟨hz, (not_congr (pm_mem_l I hZF hω hc hk)).mpr h⟩⟩

def Aw_d (b : Bool) (ω A B J n H w : M.Domain) : Prop := if b then
  ∃ i c x, M.PairMember I i c H ∧ Row_d I J i w x ∧ Pm_d I ω A B J n c x
  else ∀ i c x, M.PairMember I i c H → Row_d I J i w x → Pm_d I ω A B J n c x
def aw_m (b : Bool) {d} (ω A B J n H w : Term d) : Formula 1 d := if b then
  .existsE (.existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) H.weaken.weaken.weaken) (.conj
    (row_m (𝒞 := 𝒞) J.weaken.weaken.weaken (.bound 2) w.weaken.weaken.weaken .newest)
    (pm_m (𝒞 := 𝒞) ω.weaken.weaken.weaken A.weaken.weaken.weaken B.weaken.weaken.weaken J.weaken.weaken.weaken n.weaken.weaken.weaken (.bound 1) .newest)))))
  else .forallE (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) H.weaken.weaken.weaken) (.imp
    (row_m (𝒞 := 𝒞) J.weaken.weaken.weaken (.bound 2) w.weaken.weaken.weaken .newest)
    (pm_m (𝒞 := 𝒞) ω.weaken.weaken.weaken A.weaken.weaken.weaken B.weaken.weaken.weaken J.weaken.weaken.weaken n.weaken.weaken.weaken (.bound 1) .newest)))))
@[simp] theorem aw_closed_l (b : Bool) {d} (ω A B J n H w : Term d)
    (hω : ω.freeSupport = []) (hA : A.freeSupport = []) (hB : B.freeSupport = []) (hJ : J.freeSupport = [])
    (hn : n.freeSupport = []) (hH : H.freeSupport = []) (hw : w.freeSupport = []) : (aw_m (𝒞 := 𝒞) b ω A B J n H w).FreeClosed := by
  cases b <;> simp -implicitDefEqProofs [aw_m, Definitional.Formula.FreeClosed, hω, hA, hB, hJ, hn, hH, hw]
theorem aw_sat_l (hE : Extensional M) (b : Bool) {d} (ρ : Env M d) (ω A B J n H w : Term d) :
    Formula.satisfies ρ (aw_m (𝒞 := 𝒞) b ω A B J n H w) ↔
      Aw_d I b (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (H.eval ρ) (w.eval ρ) := by
  cases b <;> simp only [aw_m, Aw_d, Bool.false_eq_true, ↓reduceIte, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I, row_sat_l I, pm_sat_l I hE, Definitional.Term.eval_weaken] <;> rfl

def Aj_d (b : Bool) (ω A B J n H K : M.Domain) : Prop := ∀ w, M.mem w K ↔ M.mem w B ∧ Aw_d I b ω A B J n H w
def aj_m (b : Bool) {d} (ω A B J n H K : Term d) : Formula 1 d := .forallE (.iff (.mem .newest K.weaken)
  (.conj (.mem .newest B.weaken) (aw_m (𝒞 := 𝒞) b ω.weaken A.weaken B.weaken J.weaken n.weaken H.weaken .newest)))
derive_free_closed aj_m
theorem aj_sat_l (hE : Extensional M) (b : Bool) {d} (ρ : Env M d) (ω A B J n H K : Term d) :
    Formula.satisfies ρ (aj_m (𝒞 := 𝒞) b ω A B J n H K) ↔
      Aj_d I b (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (n.eval ρ) (H.eval ρ) (K.eval ρ) := by
  simp only [aj_m, Aj_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, aw_sat_l I hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.Descriptive

/-! ## 可数并交与交替实数量词交换

每次“补后投影”交换合取与析取。唯一的选择步骤是把逐行存在的实数见证
收集为实际实数列，假设精确限制为内部 AC_ω(B)。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem aw_step_l (hZF : M.Models ZF) {ω A B J n m H w} (hB : Baire_d I ω B)
    (hJ : Npair_d I ω J) (hcc : Fcc_d I B H) (hH : Bfam_d I ω A A H)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (hw : M.mem w B) (b : Bool) :
    Aw_d I (!b) ω A B J m H w ↔ ∃ Y p, M.mem Y B ∧ M.mem p B ∧ Rp_d I J w Y p ∧ ¬ Aw_d I b ω A B J n H p := by
  classical
  cases b
  · change (∃ i c x, M.PairMember I i c H ∧ Row_d I J i w x ∧ Pm_d I ω A B J m c x) ↔ _
    constructor
    · rintro ⟨i, c, x, hic, hr, hx⟩
      obtain ⟨hxB, y, z, hy, hz, hxy, hnz⟩ := (pm_succ_l I hZF hB.1 hn hm).mp hx
      obtain ⟨Y, hY, rows⟩ := row_surj_l I hZF hB hJ hy
      obtain ⟨p, hp, hwp⟩ := rp_exists_l I hZF hJ ((hB.2 w).mp hw) ((hB.2 Y).mp hY)
      exact ⟨Y, p, hY, (hB.2 p).mpr hp, hwp, fun h => hnz (h i c z hic
        (row_pair_l I hJ hr (rows i (hH.2 i c hic).1) hwp hxy))⟩
    · rintro ⟨Y, p, hY, _, hwp, hp⟩
      have bad : ∃ i c z, M.PairMember I i c H ∧ Row_d I J i p z ∧ ¬ Pm_d I ω A B J n c z := by
        apply Classical.byContradiction
        intro h
        exact hp (fun i c z hic hr => Classical.byContradiction (fun hz => h ⟨i, c, z, hic, hr, hz⟩))
      obtain ⟨i, c, z, hic, hr, hz⟩ := bad
      obtain ⟨x, hx, hix⟩ := row_exists_l I hZF hJ (hH.2 i c hic).1 ((hB.2 w).mp hw)
      obtain ⟨y, hy, hiy⟩ := row_exists_l I hZF hJ (hH.2 i c hic).1 ((hB.2 Y).mp hY)
      obtain ⟨z', hz', hxy⟩ := rp_exists_l I hZF hJ hx hy
      have e := row_unique_l I hZF.1 hr (row_pair_l I hJ hix hiy hwp hxy)
      exact ⟨i, c, x, hic, hix, (pm_succ_l I hZF hB.1 hn hm).mpr
        ⟨(hB.2 x).mpr hx, y, z', (hB.2 y).mpr hy, (hB.2 z').mpr hz', hxy, e ▸ hz⟩⟩
  · change (∀ i c x, M.PairMember I i c H → Row_d I J i w x → Pm_d I ω A B J m c x) ↔ _
    constructor
    · intro hall
      obtain ⟨D, hDω, hD⟩ := family_domain_l I hZF (fun i c hc => (hH.2 i c hc).1)
      let ρ : Env M 7 := ((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push n).push H).push w
      let φ : BinarySchema 7 := { body := .existsE (.existsE (.existsE (.conj
        (Formula.orderedPairMem 𝒞 (.bound 4) (.bound 2) (.bound 6)) (.conj
        (row_m (𝒞 := 𝒞) (.bound 8) (.bound 4) (.bound 5) (.bound 1)) (.conj
        (.mem .newest (.bound 9)) (.conj (rp_m (𝒞 := 𝒞) (.bound 8) (.bound 1) (.bound 3) .newest)
        (.neg (pm_m (𝒞 := 𝒞) (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 2) .newest)))))))) }
      have hp i y : φ.denote ρ i y ↔ ∃ c x z, M.PairMember I i c H ∧ Row_d I J i w x ∧
          M.mem z B ∧ Rp_d I J x y z ∧ ¬ Pm_d I ω A B J n c z := by
        simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
          Formula.satisfies_orderedPairMem_iff I, row_sat_l I, Formula.satisfies_mem_iff,
          rp_sat_l I, Formula.satisfies_neg_iff, pm_sat_l I hZF.1]; rfl
      obtain ⟨G, hg, eg⟩ := cc_schema_l I hZF (hcc D hD) φ ρ (by
        intro i hi
        obtain ⟨c, hic⟩ := (hD i).mp hi
        obtain ⟨x, _, hr⟩ := row_exists_l I hZF hJ (hDω i hi) ((hB.2 w).mp hw)
        obtain ⟨_, y, z, hy, hz, hxy, hnz⟩ := (pm_succ_l I hZF hB.1 hn hm).mp (hall i c x hic hr)
        exact ⟨y, hy, (hp i y).mpr ⟨c, x, z, hic, hr, hz, hxy, hnz⟩⟩)
      obtain ⟨Y, hY, rows⟩ := array_encode_l I hZF hB hJ hDω hg
      obtain ⟨p, hpB, hwp⟩ := rp_exists_l I hZF hJ ((hB.2 w).mp hw) ((hB.2 Y).mp hY)
      refine ⟨Y, p, hY, (hB.2 p).mpr hpB, hwp, fun ⟨i, c, z, hic, hr, hz⟩ => ?_⟩
      obtain ⟨y, _, hiy⟩ := hg.2.2 i ((hD i).mpr ⟨c, hic⟩)
      obtain ⟨c', x, z', hic', hix, _, hxy, hnz⟩ := (hp i y).mp (eg i y hiy)
      have ec := hH.1.2 i c c' hic hic'
      have ez := row_unique_l I hZF.1 hr (row_pair_l I hJ hix (rows i y hiy) hwp hxy)
      exact hnz (ec ▸ ez ▸ hz)
    · rintro ⟨Y, p, hY, _, hwp, hp⟩ i c x hic hix
      have hi := (hH.2 i c hic).1
      have hx := row_mem_l I hZF hB hJ hi hw hix
      obtain ⟨y, hy, hiy⟩ := row_exists_l I hZF hJ hi ((hB.2 Y).mp hY)
      obtain ⟨z, hz, hxy⟩ := rp_exists_l I hZF hJ ((hB.2 x).mp hx) hy
      exact (pm_succ_l I hZF hB.1 hn hm).mpr ⟨hx, y, z, (hB.2 y).mpr hy, (hB.2 z).mpr hz, hxy,
        fun hnz => hp ⟨i, c, z, hic, row_pair_l I hJ hix hiy hwp hxy, hnz⟩⟩

theorem aj_step_l (hZF : M.Models ZF) {ω A B J n m H K L} (hB : Baire_d I ω B)
    (hJ : Npair_d I ω J) (hcc : Fcc_d I B H) (hH : Bfam_d I ω A A H)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) {b : Bool}
    (hk : Aj_d I b ω A B J n H K) (hl : Pstep_d I B J K L) : Aj_d I (!b) ω A B J m H L := by
  obtain ⟨C, hc, hl⟩ := hl
  intro w
  refine (hl w).trans (and_congr_right fun hw => Iff.trans ?_ (aw_step_l I hZF hB hJ hcc hH hn hm hw b).symm)
  apply exists_congr; intro Y
  apply exists_congr; intro p
  exact and_congr_right fun _ => and_congr_right fun hp => and_congr_right fun _ =>
    (hc p).trans ⟨fun h ha => h.2 ((hk p).mpr ⟨hp, ha⟩), fun h => ⟨hp, fun hm => h ((hk p).mp hm).2⟩⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 可数实数行族的 Borel 初始矩阵 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem array_base_l (hZF : M.Models ZF) {ω A B J H z} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hH : Bfam_d I ω A A H) (hz : ∀ x, ¬ M.mem x z) (b : Bool) :
    ∃ c, Bcode_d I ω A A c ∧ ∀ w, M.mem w B → (Bsat_d I ω A A c w ↔ Aw_d I b ω A B J z H w) := by
  obtain ⟨E, he⟩ := ha
  obtain ⟨D, _, hD⟩ := family_domain_l I hZF (fun i c hc => (hH.2 i c hc).1)
  let ρ : Env M 6 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push H).push E
  let φ : BinarySchema 6 := { body := .existsE (.existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) (.bound 5)) (.conj
    (rmap_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 3) .newest)
    (bpull_m (𝒞 := 𝒞) (.bound 9) (.bound 8) (.bound 4) .newest (.bound 1) (.bound 2))))) }
  have hp i d : φ.denote ρ i d ↔ ∃ c f, M.PairMember I i c H ∧ Rmap_d I B J i f ∧ Bpull_d I ω A E f c d := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, rmap_sat_l I hZF.1, bpull_sat_l I hZF.1]; rfl
  have total i (hi : M.mem i D) : ∃ d, φ.denote ρ i d := by
    obtain ⟨c, hc⟩ := (hD i).mp hi
    obtain ⟨f, hf, _⟩ := rmap_exists_l I hZF hB hA hJ (hH.2 i c hc).1
    obtain ⟨d, hd, _⟩ := bpull_exists_l I hZF (f := f) hB.1 hA he (hH.2 i c hc).2
    exact ⟨d, (hp i d).mpr ⟨c, f, hc, hf, hd⟩⟩
  have unique i (_ : M.mem i D) d e (hd : φ.denote ρ i d) (he' : φ.denote ρ i e) : d = e := by
    obtain ⟨c, f, hc, hf, hd⟩ := (hp i d).mp hd
    obtain ⟨c', f', hc', hf', he'⟩ := (hp i e).mp he'
    exact bpull_unique_l I hZF.1 hd (hH.1.2 i c' c hc' hc ▸ rmap_unique_l I hZF.1 hf' hf ▸ he')
  obtain ⟨C, hC⟩ := ZF.exists_functionalImageOn hZF φ ρ D total unique
  obtain ⟨G, hg, eg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun i d hi hd => (hC d).mpr ⟨i, hi, hd⟩)
  have data i d (hd : M.PairMember I i d G) : ∃ c f, M.PairMember I i c H ∧
      Rmap_d I B J i f ∧ Bpull_d I ω A E f c d := (hp i d).mp ((eg i d).mp hd).2
  have fam : Bfam_d I ω A A G := by
    refine ⟨hg.1, fun i d hd => ?_⟩
    obtain ⟨c, f, hc, _, hcd⟩ := data i d hd
    obtain ⟨e, he', hec⟩ := bpull_exists_l I hZF (f := f) hB.1 hA he (hH.2 i c hc).2
    exact ⟨(hH.2 i c hc).1, bpull_unique_l I hZF.1 he' hcd ▸ hec⟩
  have value i c d w x (hc : M.PairMember I i c H) (hd : M.PairMember I i d G)
      (hw : M.mem w B) (hr : Row_d I J i w x) : Bsat_d I ω A A d w ↔ Pm_d I ω A B J z c x := by
    obtain ⟨c', f, hc', hf, hcd⟩ := data i d hd
    have ec := hH.1.2 i c' c hc' hc
    subst c'
    obtain ⟨f', hf', hfC⟩ := rmap_exists_l I hZF hB hA hJ (hH.2 i c hc).1
    have e := rmap_unique_l I hZF.1 hf' hf
    subst f'
    have hx := row_mem_l I hZF hB hJ (hH.2 i c hc).1 hw hr
    exact (bpull_correct_l I hZF hB.1 hA he hfC (hH.2 i c hc).2 hcd w x ((hf.2 w x).mpr ⟨hw, hr⟩)).trans
      ((pm_zero_l I hZF hB.1 hz).trans ⟨And.right, fun h => ⟨hx, h⟩⟩).symm
  cases b
  · obtain ⟨c, hc, cv⟩ := bcode_countable_inter_l I hZF hB.1 hA fam
    refine ⟨c, hc, fun w hw => (cv w).trans ⟨?_, ?_⟩⟩
    · intro hall i d x hid hr
      obtain ⟨e, _, he'⟩ := hg.2.2 i ((hD i).mpr ⟨d, hid⟩)
      exact (value i d e w x hid he' hw hr).mp (hall i e he')
    · intro hall i d hid
      obtain ⟨c, f, hic, hf, _⟩ := data i d hid
      obtain ⟨x, _, hfx⟩ := hf.1.2.2 w hw
      have hr := ((hf.2 w x).mp hfx).2
      exact (value i c d w x hic hid hw hr).mpr (hall i c x hic hr)
  · obtain ⟨c, hc, cv⟩ := bcode_union_l I hZF hB.1 hA fam
    refine ⟨c, hc, fun w hw => (cv w).trans ⟨?_, ?_⟩⟩
    · rintro ⟨i, d, hid, hd⟩
      obtain ⟨c, f, hic, hf, _⟩ := data i d hid
      obtain ⟨x, _, hfx⟩ := hf.1.2.2 w hw
      have hr := ((hf.2 w x).mp hfx).2
      exact ⟨i, c, x, hic, hr, (value i c d w x hic hid hw hr).mp hd⟩
    · rintro ⟨i, c, x, hic, hr, hx⟩
      obtain ⟨d, _, hid⟩ := hg.2.2 i ((hD i).mpr ⟨c, hic⟩)
      exact ⟨i, d, hid, (value i c d w x hic hid hw hr).mpr hx⟩

end YesMetaZFC.SetTheory.Descriptive
