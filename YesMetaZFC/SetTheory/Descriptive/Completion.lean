import YesMetaZFC.SetTheory.Descriptive.Metric
import YesMetaZFC.SetTheory.Descriptive.Noncompact
import YesMetaZFC.SetTheory.Descriptive.Comparison

/-! # 距离柯西完备性与具体空间终点

以共尾半径 2⁻ⁿ 定义数值闭球、距离柯西性与距离极限，并逐项证明它们和前缀
判据等价。极限是模型内部唯一的实际点。最后装配两个空间的完备性与紧致性结论。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ball_d (ω D z o n f g : M.Domain) : Prop := ∃ q r,
  Dist_d I ω D z o f g q ∧ Dyad_d I ω D z o n r ∧ Qle_d I z o q r
def ball_m {d} (ω D z o n f g : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (dist_m (𝒞 := 𝒞) ω.weaken.weaken D.weaken.weaken z.weaken.weaken o.weaken.weaken
    f.weaken.weaken g.weaken.weaken (.bound 1)) (.conj
    (dyad_m (𝒞 := 𝒞) ω.weaken.weaken D.weaken.weaken z.weaken.weaken o.weaken.weaken n.weaken.weaken .newest)
    (qle_m (𝒞 := 𝒞) z.weaken.weaken o.weaken.weaken (.bound 1) .newest))))
derive_free_closed ball_m
theorem ball_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D z o n f g : Term d) :
    Formula.satisfies ρ (ball_m (𝒞 := 𝒞) ω D z o n f g) ↔
      Ball_d I (ω.eval ρ) (D.eval ρ) (z.eval ρ) (o.eval ρ) (n.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [ball_m, Ball_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    dist_sat_l I hE, dyad_sat_l I hE, qle_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem ds_ball_iff_l (hZF : M.Models ZF) {ω X D z o n f g} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o)
    (hn : M.mem n ω) (hf : M.IsSetFunctionFromTo I f ω X) (hg : M.IsSetFunctionFromTo I g ω X) :
    Ball_d I ω D z o n f g ↔ Senv_agree_d I n f g := by
  have hD := ds_two_mem_l hZF.1 hω ⟨o, ho, hd⟩
  refine ⟨fun ⟨q, r, hq, hr, h⟩ => (ds_dist_ball_l I hZF hω hz ho hd hg hn hq hr).mp h, fun h => ?_⟩
  obtain ⟨q, hq⟩ := ds_dist_exists_l I hZF hω hD hf hg
  obtain ⟨r, hr⟩ := dyad_exists_l I hZF hω hD (z := z) (o := o) (Or.inr hn)
  exact ⟨q, r, hq, hr, (ds_dist_ball_l I hZF hω hz ho hd hg hn hq hr).mpr h⟩

/-- 原拓扑恰由这些数值距离球生成，而非仅在收敛列上吻合。 -/
theorem ds_metric_open_l (hZF : M.Models ZF) {ω X B S D z o U} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o)
    (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S) :
    Open_d S B U ↔ M.MemberSubset U B ∧ ∀ f, M.mem f U →
      ∃ n, M.mem n ω ∧ ∀ g, M.mem g B → Ball_d I ω D z o n f g → M.mem g U := by
  constructor
  · intro hU
    refine ⟨hU.1, fun f hf => ?_⟩
    obtain ⟨s, hs, hsf, hu⟩ := hU.2 f hf
    obtain ⟨n, hn, hsn⟩ := (hS s).mp hs
    have hff := (hB f).mp (hU.1 f hf)
    have hr := (ds_restrict_iff_l I hsn hff.1).mpr hsf
    refine ⟨n, hn, fun g hg hfg => ?_⟩
    have hgg := (hB g).mp hg
    have ha := (ds_ball_iff_l I hZF hω hz ho hd hn hff hgg).mp hfg
    exact hu g hg ((ds_restrict_iff_l I hsn hgg.1).mp ((ds_agree_restrict_l I hr).mp ha))
  · rintro ⟨hUB, hU⟩
    refine ⟨hUB, fun f hf => ?_⟩
    obtain ⟨n, hn, hball⟩ := hU f hf
    have hff := (hB f).mp (hUB f hf)
    obtain ⟨s, hs, hr, _⟩ := ds_prefix_l I hZF hω hff hn
    refine ⟨s, (hS s).mpr ⟨n, hn, hs⟩, (ds_restrict_iff_l I hs hff.1).mp hr, fun g hg hsg => ?_⟩
    have hgg := (hB g).mp hg
    exact hball g hg ((ds_ball_iff_l I hZF hω hz ho hd hn hff hgg).mpr
      ((ds_agree_restrict_l I hr).mpr ((ds_restrict_iff_l I hs hgg.1).mpr hsg)))

def MCauchy_d (ω D z o H : M.Domain) : Prop := ∀ n, M.mem n ω → ∃ k, M.mem k ω ∧
  ∀ i, M.mem i ω → ∀ j, M.mem j ω → ¬ M.mem i k → ¬ M.mem j k →
    ∀ f g, M.PairMember I i f H → M.PairMember I j g H → Ball_d I ω D z o n f g
def MLimit_d (ω D z o H f : M.Domain) : Prop := ∀ n, M.mem n ω → ∃ k, M.mem k ω ∧
  ∀ j, M.mem j ω → ¬ M.mem j k → ∀ g, M.PairMember I j g H → Ball_d I ω D z o n g f

def mcauchy_m {d} (ω D z o H : Term d) : Formula 1 d := Formula.forallMem ω (.existsE
  (.conj (.mem .newest ω.weaken.weaken) (Formula.forallMem ω.weaken.weaken
    (Formula.forallMem ω.weaken.weaken.weaken (.imp (.neg (.mem (.bound 1) (.bound 2)))
      (.imp (.neg (.mem .newest (.bound 2))) (.forallE (.forallE
        (.imp (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) H.weaken.weaken.weaken.weaken.weaken.weaken)
          (.imp (Formula.orderedPairMem 𝒞 (.bound 2) .newest H.weaken.weaken.weaken.weaken.weaken.weaken)
            (ball_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken.weaken
              D.weaken.weaken.weaken.weaken.weaken.weaken z.weaken.weaken.weaken.weaken.weaken.weaken
              o.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 1) .newest)))))))))))
derive_free_closed mcauchy_m
def mlimit_m {d} (ω D z o H f : Term d) : Formula 1 d := Formula.forallMem ω (.existsE
  (.conj (.mem .newest ω.weaken.weaken) (Formula.forallMem ω.weaken.weaken
    (.imp (.neg (.mem .newest (.bound 1))) (.forallE
      (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken.weaken.weaken)
        (ball_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken
          z.weaken.weaken.weaken.weaken o.weaken.weaken.weaken.weaken (.bound 3) .newest
          f.weaken.weaken.weaken.weaken)))))))
derive_free_closed mlimit_m

theorem mcauchy_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D z o H : Term d) :
    Formula.satisfies ρ (mcauchy_m (𝒞 := 𝒞) ω D z o H) ↔
      MCauchy_d I (ω.eval ρ) (D.eval ρ) (z.eval ρ) (o.eval ρ) (H.eval ρ) := by
  simp only [mcauchy_m, MCauchy_d, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_forall_iff, Formula.satisfies_orderedPairMem_iff I,
    ball_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem mlimit_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D z o H f : Term d) :
    Formula.satisfies ρ (mlimit_m (𝒞 := 𝒞) ω D z o H f) ↔
      MLimit_d I (ω.eval ρ) (D.eval ρ) (z.eval ρ) (o.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [mlimit_m, MLimit_d, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_forall_iff, Formula.satisfies_orderedPairMem_iff I,
    ball_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem ds_mcauchy_iff_l (hZF : M.Models ZF) {ω X B D z o H} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o)
    (hB : M.IsFunctionSpace I B ω X) (hH : M.IsSetFunctionFromTo I H ω B) :
    MCauchy_d I ω D z o H ↔ Cauchy_d I ω H := by
  have ball (n : M.Domain) (hn : M.mem n ω) {i j f g} (hf : M.PairMember I i f H) (hg : M.PairMember I j g H) :=
    ds_ball_iff_l I hZF hω hz ho hd hn ((hB f).mp (hH.output_mem_of_pairMember hf))
      ((hB g).mp (hH.output_mem_of_pairMember hg))
  constructor <;> intro h n hn <;> obtain ⟨k, hk, ht⟩ := h n hn
  · exact ⟨k, hk, fun i hi j hj hik hjk f g hf hg => (ball n hn hf hg).mp (ht i hi j hj hik hjk f g hf hg)⟩
  · exact ⟨k, hk, fun i hi j hj hik hjk f g hf hg => (ball n hn hf hg).mpr (ht i hi j hj hik hjk f g hf hg)⟩

theorem ds_mlimit_iff_l (hZF : M.Models ZF) {ω X B D z o H f} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o)
    (hB : M.IsFunctionSpace I B ω X) (hH : M.IsSetFunctionFromTo I H ω B) (hf : M.mem f B) :
    MLimit_d I ω D z o H f ↔ Limit_d I ω H f := by
  have ball (n : M.Domain) (hn : M.mem n ω) {j g} (hg : M.PairMember I j g H) := ds_ball_iff_l I hZF hω hz ho hd hn
    ((hB g).mp (hH.output_mem_of_pairMember hg)) ((hB f).mp hf)
  constructor <;> intro h n hn <;> obtain ⟨k, hk, ht⟩ := h n hn
  · exact ⟨k, hk, fun j hj hjk g hg => (ball n hn hg).mp (ht j hj hjk g hg)⟩
  · exact ⟨k, hk, fun j hj hjk g hg => (ball n hn hg).mpr (ht j hj hjk g hg)⟩

theorem ds_limit_unique_l (hZF : M.Models ZF) {ω X B H f g} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) (hH : M.IsSetFunctionFromTo I H ω B)
    (hf : M.mem f B) (hg : M.mem g B) (hl : Limit_d I ω H f) (hm : Limit_d I ω H g) : f = g := by
  apply Classical.byContradiction
  intro e
  obtain ⟨i, x, y, hi, hx, hy, hxy⟩ := ds_differ_l I hZF.1 ((hB f).mp hf) ((hB g).mp hg) e
  obtain ⟨n, hn, hnω⟩ := hω.1.2 i hi
  obtain ⟨k, hk, ha⟩ := hl n hnω
  obtain ⟨l, hll, hb⟩ := hm n hnω
  obtain ⟨m, hmn, hmk, hml⟩ := ds_tail_l hZF.1 (hω.isOrdinal hZF) hk hll
  obtain ⟨t, _, ht⟩ := hH.2.2 m hmn
  have hab : Senv_agree_d I n f g := fun j a hj =>
    (ha m hmn hmk t ht j a hj).symm.trans (hb m hmn hml t ht j a hj)
  exact ds_diff_not_agree_l I ((hB g).mp hg).1 ⟨x, y, hx, hy, hxy⟩ hn.predecessor_mem hab

/-- 数值距离柯西列有唯一的内部距离极限。 -/
theorem ds_metric_complete_l (hZF : M.Models ZF) {ω X B D z o H} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o)
    (hB : M.IsFunctionSpace I B ω X) (hH : M.IsSetFunctionFromTo I H ω B)
    (hc : MCauchy_d I ω D z o H) : ∃ f, M.mem f B ∧ MLimit_d I ω D z o H f ∧
      ∀ g, M.mem g B → MLimit_d I ω D z o H g → g = f := by
  obtain ⟨f, hf, hl⟩ := ds_complete_l I hZF hω hB hH ((ds_mcauchy_iff_l I hZF hω hz ho hd hB hH).mp hc)
  exact ⟨f, hf, (ds_mlimit_iff_l I hZF hω hz ho hd hB hH hf).mpr hl, fun g hg hm =>
    ds_limit_unique_l I hZF hω hB hH hg hf ((ds_mlimit_iff_l I hZF hω hz ho hd hB hH hg).mp hm) hl⟩

/-- 同一个距离的收敛就是模型内部原拓扑的收敛。 -/
theorem ds_metric_topology_l (hZF : M.Models ZF) {ω X B S τ D z o H f} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o)
    (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hτ : ∀ U, M.mem U τ ↔ Open_d S B U) (hH : M.IsSetFunctionFromTo I H ω B) (hf : M.mem f B) :
    MLimit_d I ω D z o H f ↔ Tendsto_d I ω τ H f :=
  (ds_mlimit_iff_l I hZF hω hz ho hd hB hH hf).trans (ds_limit_topology_l I hZF hω hB hS hτ hH hf)

def Complete_d (ω D z o B : M.Domain) : Prop := ∀ H, M.IsSetFunctionFromTo I H ω B →
  MCauchy_d I ω D z o H → ∃ f, M.mem f B ∧ MLimit_d I ω D z o H f
def complete_m {d} (ω D z o B : Term d) : Formula 1 d := .forallE
  (.imp (Formula.isFunctionFromTo 𝒞 .newest ω.weaken B.weaken)
    (.imp (mcauchy_m (𝒞 := 𝒞) ω.weaken D.weaken z.weaken o.weaken .newest)
      (Formula.existsMem B.weaken (mlimit_m (𝒞 := 𝒞) ω.weaken.weaken D.weaken.weaken
        z.weaken.weaken o.weaken.weaken (.bound 1) .newest))))
derive_free_closed complete_m

theorem complete_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D z o B : Term d) :
    Formula.satisfies ρ (complete_m (𝒞 := 𝒞) ω D z o B) ↔
      Complete_d I (ω.eval ρ) (D.eval ρ) (z.eval ρ) (o.eval ρ) (B.eval ρ) := by
  simp only [complete_m, Complete_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, mcauchy_sat_l I hE, Formula.satisfies_existsMem_iff,
    mlimit_sat_l I hE, Definitional.Term.eval_weaken]; rfl

/-- 所需空间、拓扑、距离常量与三个终局性质同时实际构造。 -/
theorem baire_cantor_complete_compact_l (hZF : M.Models ZF) : ∃ ω D z o B C S T τ υ,
    Baire_d I ω B ∧ Cantor_d I ω C ∧ (∀ x, ¬ M.mem x z) ∧ M.IsOrdinalOne o ∧ M.SuccessorOf D o ∧
    Fseq_space_d I ω ω S ∧ Fseq_space_d I ω D T ∧ Top_d B τ ∧ Top_d C υ ∧
    (∀ U, M.mem U τ ↔ Open_d S B U) ∧ (∀ U, M.mem U υ ↔ Open_d T C U) ∧
    Complete_d I ω D z o B ∧ Complete_d I ω D z o C ∧ Compact_d I ω C υ ∧ ¬ Compact_d I ω B τ := by
  obtain ⟨ω, D, B, C, S, T, τ, υ, hB, hD, hC, hS, _, hT, _, hτ, hυ, ht, hu⟩ := baire_cantor_l I hZF
  obtain ⟨o, ⟨z, hz, ho⟩, hd⟩ := hD
  have hone : M.IsOrdinalOne o := ⟨z, hz, ho⟩
  have complete {X Y} (hY : M.IsFunctionSpace I Y ω X) : Complete_d I ω D z o Y := fun H hH hc =>
    (ds_metric_complete_l I hZF hB.1 hz hone hd hY hH hc).imp fun f hf => ⟨hf.1, hf.2.1⟩
  exact ⟨ω, D, z, o, B, C, S, T, τ, υ, hB, ⟨hB.1, D, ⟨o, hone, hd⟩, hC⟩,
    hz, hone, hd, hS, hT, hτ, hυ, ht, hu, complete hB.2, complete hC,
    cantor_compact_l I hZF hB.1 ⟨o, hone, hd⟩ hC hT hu, baire_not_compact_l I hZF hB hS ht⟩

end YesMetaZFC.SetTheory.Descriptive
