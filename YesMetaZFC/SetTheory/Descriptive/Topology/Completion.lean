import YesMetaZFC.SetTheory.Descriptive.Topology.Topology
import YesMetaZFC.Model.SetTheory.Internal.Theory
import YesMetaZFC.SetTheory.Ord.Arithmetic.Comparison
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
import YesMetaZFC.SetTheory.Card.Finite
import YesMetaZFC.SetTheory.Card.Arithmetic.PowerSet

/-! # 内部前缀尺度的柯西列与极限

尺度 n 表示前 n 个坐标一致，即通常前缀超度量的闭球半径 2⁻ⁿ。
列、阈值、尺度均在模型内部；极限通过唯一的逐坐标稳定值构造。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Cauchy_d (ω H : M.Domain) : Prop := ∀ n, M.mem n ω → ∃ k, M.mem k ω ∧
  ∀ i, M.mem i ω → ∀ j, M.mem j ω → ¬ M.mem i k → ¬ M.mem j k →
    ∀ f g, M.PairMember I i f H → M.PairMember I j g H → Senv_agree_d I n f g
def Limit_d (ω H f : M.Domain) : Prop := ∀ n, M.mem n ω → ∃ k, M.mem k ω ∧
  ∀ j, M.mem j ω → ¬ M.mem j k → ∀ g, M.PairMember I j g H → Senv_agree_d I n g f
def Stable_d (ω H i x : M.Domain) : Prop := ∃ k, M.mem k ω ∧
  ∀ j, M.mem j ω → ¬ M.mem j k → ∀ f, M.PairMember I j f H → M.PairMember I i x f

def stable_m {d} (ω H i x : Term d) : Formula 1 d := .existsE (.conj (.mem .newest ω.weaken)
  (Formula.forallMem ω.weaken (.imp (.neg (.mem .newest (.bound 1))) (.forallE
    (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken.weaken)
      (Formula.orderedPairMem 𝒞 i.weaken.weaken.weaken x.weaken.weaken.weaken .newest))))))
derive_free_closed stable_m
theorem stable_sat_l {d} (ρ : Env M d) (ω H i x : Term d) :
    Formula.satisfies ρ (stable_m (𝒞 := 𝒞) ω H i x) ↔
      Stable_d I (ω.eval ρ) (H.eval ρ) (i.eval ρ) (x.eval ρ) := by
  simp only [stable_m, Stable_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_forall_iff, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

def cauchy_m {d} (ω H : Term d) : Formula 1 d := Formula.forallMem ω (.existsE
  (.conj (.mem .newest ω.weaken.weaken) (Formula.forallMem ω.weaken.weaken
    (Formula.forallMem ω.weaken.weaken.weaken (.imp (.neg (.mem (.bound 1) (.bound 2)))
      (.imp (.neg (.mem .newest (.bound 2))) (.forallE (.forallE
        (.imp (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) H.weaken.weaken.weaken.weaken.weaken.weaken)
          (.imp (Formula.orderedPairMem 𝒞 (.bound 2) .newest H.weaken.weaken.weaken.weaken.weaken.weaken)
            (senv_agree_m (𝒞 := 𝒞) (.bound 5) (.bound 1) .newest)))))))))))
derive_free_closed cauchy_m
def limit_m {d} (ω H f : Term d) : Formula 1 d := Formula.forallMem ω (.existsE
  (.conj (.mem .newest ω.weaken.weaken) (Formula.forallMem ω.weaken.weaken
    (.imp (.neg (.mem .newest (.bound 1))) (.forallE
      (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken.weaken.weaken)
        (senv_agree_m (𝒞 := 𝒞) (.bound 3) .newest f.weaken.weaken.weaken.weaken)))))))
derive_free_closed limit_m


theorem cauchy_sat_l {d} (ρ : Env M d) (ω H : Term d) :
    Formula.satisfies ρ (cauchy_m (𝒞 := 𝒞) ω H) ↔ Cauchy_d I (ω.eval ρ) (H.eval ρ) := by
  simp only [cauchy_m, Cauchy_d, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_forall_iff, Formula.satisfies_orderedPairMem_iff I,
    senv_agree_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem limit_sat_l {d} (ρ : Env M d) (ω H f : Term d) :
    Formula.satisfies ρ (limit_m (𝒞 := 𝒞) ω H f) ↔ Limit_d I (ω.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [limit_m, Limit_d, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_forall_iff, Formula.satisfies_orderedPairMem_iff I,
    senv_agree_sat_l I, Definitional.Term.eval_weaken]; rfl

omit I in
/-- 内部序数线性序保证两个尾部有共同指标。 -/
theorem ds_tail_l (hE : Extensional M) {ω i j : M.Domain} (hω : M.IsOrdinal ω)
    (hi : M.mem i ω) (hj : M.mem j ω) : ∃ k, M.mem k ω ∧ ¬ M.mem k i ∧ ¬ M.mem k j := by
  have irr x hx := hω.wellOrder.linear.irrefl x hx
  rcases hω.wellOrder.linear.compare i hi j hj with he | hij | hji
  · have he := hE.eq_of_same_members i j he
    subst j
    exact ⟨i, hi, irr i hi, irr i hi⟩
  · exact ⟨j, hj, fun h => irr j hj ((hω.mem hj).transitive i hij j h), irr j hj⟩
  · exact ⟨i, hi, irr i hi, fun h => irr i hi ((hω.mem hi).transitive j hji i h)⟩

/-- 柯西列的每个坐标有唯一的稳定值。 -/
theorem ds_stable_l (hZF : M.Models ZF) {ω X B H} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) (hH : M.IsSetFunctionFromTo I H ω B)
    (hc : Cauchy_d I ω H) {i} (hi : M.mem i ω) :
    ∃ x, Stable_d I ω H i x ∧ M.mem x X ∧ ∀ y, Stable_d I ω H i y → y = x := by
  obtain ⟨n, hn, hnω⟩ := hω.1.2 i hi
  obtain ⟨k, hk, ht⟩ := hc n hnω
  obtain ⟨f, hfB, hf⟩ := hH.2.2 k hk
  obtain ⟨x, hx, hix⟩ := ((hB f).mp hfB).2.2 i hi
  have hs : Stable_d I ω H i x := ⟨k, hk, fun j hj hjk g hg =>
    (ht k hk j hj (KP.mem_irrefl_d (ZF.modelsKP hZF) k) hjk f g hf hg i x hn.predecessor_mem).mp hix⟩
  refine ⟨x, hs, hx, fun y hy => ?_⟩
  obtain ⟨l, hl, hy⟩ := hy
  obtain ⟨m, hm, hmk, hml⟩ := ds_tail_l hZF.1 (hω.isOrdinal (ZF.modelsKP hZF)) hk hl
  obtain ⟨g, hgB, hg⟩ := hH.2.2 m hm
  exact ((hB g).mp hgB).1.2 i y x (hy m hm hml g hg)
    ((ht k hk m hm (KP.mem_irrefl_d (ZF.modelsKP hZF) k) hmk f g hf hg i x hn.predecessor_mem).mp hix)

/-- 任意内部离散字母表的全部 ω 列在前缀尺度下完备。 -/
theorem ds_complete_l (hZF : M.Models ZF) {ω X B H} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) (hH : M.IsSetFunctionFromTo I H ω B)
    (hc : Cauchy_d I ω H) : ∃ f, M.mem f B ∧ Limit_d I ω H f := by
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push H
  let φ : BinarySchema 2 := { body := stable_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp i x : φ.denote ρ i x ↔ Stable_d I ω H i x := stable_sat_l I _ _ _ _ _
  have stable i hi := ds_stable_l I hZF hω hB hH hc (i := i) hi
  obtain ⟨f, hf, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := X)
    (fun i hi => (stable i hi).elim fun x hx => ⟨x, (hp i x).mpr hx.1⟩)
    (fun i hi x y hx hy => (stable i hi).elim fun z hz =>
      (hz.2.2 x ((hp i x).mp hx)).trans (hz.2.2 y ((hp i y).mp hy)).symm)
    (fun i x hi hx => (stable i hi).elim fun z hz => (hz.2.2 x ((hp i x).mp hx)).symm ▸ hz.2.1)
  refine ⟨f, (hB f).mpr hf, fun n hn => ?_⟩
  obtain ⟨k, hk, ht⟩ := hc n hn
  refine ⟨k, hk, fun j hj hjk g hg i x hin => ?_⟩
  have hi := hω.transitive (ZF.modelsKP hZF) n hn i hin
  have into y (hy : M.PairMember I i y g) : M.PairMember I i y f :=
    (he i y).mpr ⟨hi, (hp i y).mpr ⟨k, hk, fun l hl hlk t htH =>
      (ht j hj l hl hjk hlk g t hg htH i y hin).mp hy⟩⟩
  refine ⟨into x, fun hx => ?_⟩
  obtain ⟨y, _, hy⟩ := ((hB g).mp (hH.output_mem_of_pairMember hg)).2.2 i hi
  exact hf.1.2 i y x (into y hy) hx ▸ hy

/-- 前缀一致恰好说明两个图具有同一个给定限制。 -/
theorem ds_agree_restrict_l {n s f g : M.Domain} (hs : M.IsRestrictionOf I s f n) :
    Senv_agree_d I n f g ↔ M.IsRestrictionOf I s g n := by
  refine ⟨fun h => ⟨hs.1, fun i x => (hs.2 i x).trans (and_congr_right fun hi => h i x hi)⟩, ?_⟩
  intro h i x hi
  exact ⟨fun hx => ((h.2 i x).mp ((hs.2 i x).mpr ⟨hi, hx⟩)).2,
    fun hx => ((hs.2 i x).mp ((h.2 i x).mpr ⟨hi, hx⟩)).2⟩

def Tendsto_d (ω τ H f : M.Domain) : Prop := ∀ U, M.mem U τ → M.mem f U →
  ∃ k, M.mem k ω ∧ ∀ j, M.mem j ω → ¬ M.mem j k → ∀ g, M.PairMember I j g H → M.mem g U
def tendsto_m {d} (ω τ H f : Term d) : Formula 1 d := Formula.forallMem τ
  (.imp (.mem f.weaken .newest) (.existsE (.conj (.mem .newest ω.weaken.weaken)
    (Formula.forallMem ω.weaken.weaken (.imp (.neg (.mem .newest (.bound 1))) (.forallE
      (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken.weaken.weaken)
        (.mem .newest (.bound 3)))))))))
derive_free_closed tendsto_m

theorem tendsto_sat_l {d} (ρ : Env M d) (ω τ H f : Term d) :
    Formula.satisfies ρ (tendsto_m (𝒞 := 𝒞) ω τ H f) ↔
      Tendsto_d I (ω.eval ρ) (τ.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [tendsto_m, Tendsto_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_forall_iff, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken]; rfl

/-- 前缀尺度收敛与上一层实际拓扑的邻域收敛完全一致。 -/
theorem ds_limit_topology_l (hZF : M.Models ZF) {ω X B S τ H f}
    (hω : M.IsOmega ω) (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hτ : ∀ U, M.mem U τ ↔ Open_d S B U) (hH : M.IsSetFunctionFromTo I H ω B) (hf : M.mem f B) :
    Limit_d I ω H f ↔ Tendsto_d I ω τ H f := by
  constructor
  · intro h U hU hfU
    obtain ⟨s, hs, hsf, hu⟩ := ((hτ U).mp hU).2 f hfU
    obtain ⟨n, hn, hsn⟩ := (hS s).mp hs
    obtain ⟨k, hk, ht⟩ := h n hn
    refine ⟨k, hk, fun j hj hjk g hg => ?_⟩
    have hgB := hH.output_mem_of_pairMember hg
    have hsF := (ds_restrict_iff_l I hsn ((hB f).mp hf).1).mpr hsf
    exact hu g hgB ((ds_restrict_iff_l I hsn ((hB g).mp hgB).1).mp
      ((ds_agree_restrict_l I hsF).mp (ht j hj hjk g hg).symm_l))
  · intro h n hn
    obtain ⟨s, hs, hr, _⟩ := ds_prefix_l I hZF hω ((hB f).mp hf) hn
    obtain ⟨U, hU⟩ := cyl_exists_l (ZF.modelsKP hZF) B s
    have hsS := (hS s).mpr ⟨n, hn, hs⟩
    obtain ⟨k, hk, ht⟩ := h U ((hτ U).mpr (ds_open_cyl_l hsS hU))
      ((hU f).mpr ⟨hf, (ds_restrict_iff_l I hs ((hB f).mp hf).1).mp hr⟩)
    refine ⟨k, hk, fun j hj hjk g hg => ?_⟩
    have hh := (hU g).mp (ht j hj hjk g hg)
    exact ((ds_agree_restrict_l I hr).mpr ((ds_restrict_iff_l I hs ((hB g).mp hh.1).1).mpr hh.2)).symm_l

end YesMetaZFC.SetTheory.Descriptive

/-! ## 前缀距离的规范有理数码

距离值是实际有序对 (0,1) 或 (1,2ⁿ)，指数及幂均由模型解释。只对这组规范
非负分数比较大小：零最小，正单位分数按分母反序。ω 用作零距离的指数标记。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Dyad_d (ω D z o n q : M.Domain) : Prop :=
  (n = ω ∧ I.Codes q z o) ∨ (M.mem n ω ∧ ∃ p, M.mem p ω ∧
    M.IsOrdinalExponentiation I p D n ∧ I.Codes q o p)
def Qle_d (z o q r : M.Domain) : Prop := (∃ p, I.Codes q z p) ∨
  ∃ p t, I.Codes q o p ∧ I.Codes r o t ∧ M.MemberSubset t p

def dyad_m {d} (ω D z o n q : Term d) : Formula 1 d := .disj
  (.conj (Formula.extensionalEq n ω) (𝒞.code q z o)) (.conj (.mem n ω) (.existsE
    (.conj (.mem .newest ω.weaken) (.conj (Formula.isOrdinalExponentiation 𝒞 .newest D.weaken n.weaken)
      (𝒞.code q.weaken o.weaken .newest)))))
derive_free_closed dyad_m
def qle_m {d} (z o q r : Term d) : Formula 1 d := .disj
  (.existsE (𝒞.code q.weaken z.weaken .newest)) (.existsE (.existsE (.conj
    (𝒞.code q.weaken.weaken o.weaken.weaken (.bound 1)) (.conj
      (𝒞.code r.weaken.weaken o.weaken.weaken .newest) (Formula.subset .newest (.bound 1))))))
derive_free_closed qle_m
theorem dyad_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D z o n q : Term d) :
    Formula.satisfies ρ (dyad_m (𝒞 := 𝒞) ω D z o n q) ↔
      Dyad_d I (ω.eval ρ) (D.eval ρ) (z.eval ρ) (o.eval ρ) (n.eval ρ) (q.eval ρ) := by
  simp only [dyad_m, Dyad_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, I.satisfies_code_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_isOrdinalExponentiation_iff I hE,
    Definitional.Term.eval_weaken]; rfl
theorem qle_sat_l {d} (ρ : Env M d) (z o q r : Term d) :
    Formula.satisfies ρ (qle_m (𝒞 := 𝒞) z o q r) ↔
      Qle_d I (z.eval ρ) (o.eval ρ) (q.eval ρ) (r.eval ρ) := by
  simp only [qle_m, Qle_d, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, I.satisfies_code_iff, Formula.satisfies_subset_iff,
    Definitional.Term.eval_weaken]; rfl

theorem dyad_exists_l (hZF : M.Models ZF) {ω D z o n} (hω : M.IsOmega ω)
    (hD : M.mem D ω) (hn : n = ω ∨ M.mem n ω) : ∃ q, Dyad_d I ω D z o n q := by
  rcases hn with rfl | hn
  · obtain ⟨q, hq⟩ := I.total z o
    exact ⟨q, Or.inl ⟨rfl, hq⟩⟩
  · obtain ⟨p, hp, _⟩ := ZF.ordinalExponentiation_existsUnique hZF I
      ((hω.isOrdinal (ZF.modelsKP hZF)).mem hD) ((hω.isOrdinal (ZF.modelsKP hZF)).mem hn)
    obtain ⟨q, hq⟩ := I.total o p
    exact ⟨q, Or.inr ⟨hn, p, ZF.ordinalExponentiation_mem_omega hZF I hω hD hn hp, hp, hq⟩⟩

theorem dyad_unique_l (hZF : M.Models ZF) {ω D z o n q r} (hω : M.IsOmega ω)
    (hD : M.IsOrdinal D) (hq : Dyad_d I ω D z o n q) (hr : Dyad_d I ω D z o n r) : q = r := by
  rcases hq with ⟨en, hq⟩ | ⟨hn, p, _, hp, hq⟩ <;>
    rcases hr with ⟨e, hr⟩ | ⟨hn', t, _, ht, hr⟩
  · exact I.unique hq hr
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ω (en ▸ hn')).elim
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ω (e ▸ hn)).elim
  · obtain ⟨v, _, hv⟩ := ZF.ordinalExponentiation_existsUnique hZF I hD ((hω.isOrdinal (ZF.modelsKP hZF)).mem hn)
    have e := (hv p hp).trans (hv t ht).symm
    subst t
    exact I.unique hq hr

omit I in
theorem ds_nat_le_l (hE : Extensional M) {ω i j : M.Domain} (hω : M.IsOrdinal ω)
    (hi : M.mem i ω) (hj : M.mem j ω) : M.MemberSubset i j ↔ i = j ∨ M.mem i j := by
  refine ⟨fun h => ?_, fun h => h.elim (fun e => e ▸ (fun _ h => h)) ((hω.mem hj).transitive i)⟩
  rcases hω.wellOrder.linear.compare i hi j hj with he | hij | hji
  · exact Or.inl (hE.eq_of_same_members i j he)
  · exact Or.inr hij
  · exact (hω.wellOrder.linear.irrefl j hj (h j hji)).elim

/-- 单位分数的数值次序恰是指数的反序；零距离作为最大指数。 -/
theorem dyad_le_l (hZF : M.Models ZF) {ω D z o n m q r} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o)
    (hq : Dyad_d I ω D z o n q) (hr : Dyad_d I ω D z o m r) :
    Qle_d I z o q r ↔ n = ω ∨ m = n ∨ M.mem m n := by
  have hD := Structure.IsOrdinalTwo.isOrdinal (ZF.modelsKP hZF) ⟨o, ho, hd⟩
  have hzo : o ≠ z := fun e => ho.elim fun a ha => hz a (e ▸ ha.2.predecessor_mem)
  rcases hq with ⟨en, hq⟩ | ⟨hn, p, hpω, hp, hq⟩
  · exact iff_of_true (Or.inl ⟨o, hq⟩) (Or.inl en)
  · have hne : n ≠ ω := fun e => KP.mem_irrefl_d (ZF.modelsKP hZF) ω (e ▸ hn)
    rcases hr with ⟨em, hr⟩ | ⟨hm, t, htω, ht, hr⟩
    · refine iff_of_false ?_ ?_
      · rintro (⟨p', h⟩ | ⟨p', t', h, k, _⟩)
        · exact hzo (I.injective hq h).1
        · exact hzo (I.injective k hr).1
      · rintro (e | e | h)
        · exact hne e
        · exact hne (e.symm.trans em)
        · exact KP.mem_irrefl_d (ZF.modelsKP hZF) ω (hω.transitive (ZF.modelsKP hZF) n hn ω (em ▸ h))
    · have order : M.MemberSubset t p ↔ m = n ∨ M.mem m n := by
        rw [ds_nat_le_l hZF.1 (hω.isOrdinal (ZF.modelsKP hZF)) htω hpω]
        apply or_congr
        · refine ⟨fun e => ZF.ordinalExponentiation_exponent_injective hZF I hD ho hd.predecessor_mem
            ((hω.isOrdinal (ZF.modelsKP hZF)).mem hm) ((hω.isOrdinal (ZF.modelsKP hZF)).mem hn) (e ▸ ht) hp, fun e => ?_⟩
          subst m
          obtain ⟨v, _, hv⟩ := ZF.ordinalExponentiation_existsUnique hZF I hD ((hω.isOrdinal (ZF.modelsKP hZF)).mem hn)
          exact (hv t ht).trans (hv p hp).symm
        · exact ZF.ordinalExponentiation_values_mem_iff hZF I hD ho hd.predecessor_mem
            ((hω.isOrdinal (ZF.modelsKP hZF)).mem hm) ((hω.isOrdinal (ZF.modelsKP hZF)).mem hn) ht hp
      refine ⟨fun h => Or.inr (order.mp ?_), fun h => ?_⟩
      · rcases h with ⟨v, hv⟩ | ⟨v, w, hv, hw, h⟩
        · exact (hzo (I.injective hq hv).1).elim
        · have ev := (I.injective hv hq).2
          have ew := (I.injective hw hr).2
          exact ev ▸ ew ▸ h
      · exact Or.inr ⟨p, t, hq, hr, order.mpr (h.resolve_left hne)⟩

omit I in
/-- 内部归纳集直接提供 0、1、2 的实际实例。 -/
theorem ds_digits_l {ω : M.Domain} (hω : M.IsOmega ω) : ∃ z o D,
    (∀ x, ¬ M.mem x z) ∧ M.mem z ω ∧ M.IsOrdinalOne o ∧ M.mem o ω ∧
    M.SuccessorOf D o ∧ M.mem D ω := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨o, ho, hoω⟩ := hω.1.2 z hzω
  obtain ⟨D, hd, hdω⟩ := hω.1.2 o hoω
  exact ⟨z, o, D, hz, hzω, ⟨z, hz, ho⟩, hoω, hd, hdω⟩

/-- 正距离的分母非零，因此实际有理数码不含零分母。 -/
theorem dyad_denominator_pos_l (hZF : M.Models ZF) {ω D o n p} (hω : M.IsOmega ω)
    (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o) (hn : M.mem n ω)
    (hp : M.IsOrdinalExponentiation I p D n) : ∃ a, M.mem a p :=
  ZF.ordinalExponentiation_isNonemptyOnOrdinals hZF I
    (Structure.IsOrdinalTwo.isOrdinal (ZF.modelsKP hZF) ⟨o, ho, hd⟩) ⟨o, hd.predecessor_mem⟩
    n ((hω.isOrdinal (ZF.modelsKP hZF)).mem hn) p hp

/-- 2 的幂在内部自然数中无界；这些单位分数构成趋向零的共尾尺度。 -/
theorem dyad_cofinal_l (hZF : M.Models ZF) {ω D o m} (hω : M.IsOmega ω)
    (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o) (hm : M.mem m ω) :
    ∃ n p, M.mem n ω ∧ M.mem p ω ∧ M.IsOrdinalExponentiation I p D n ∧ M.mem m p := by
  have hD : M.IsOrdinal D := Structure.IsOrdinalTwo.isOrdinal (ZF.modelsKP hZF) ⟨o, ho, hd⟩
  obtain ⟨n, hn, hnω⟩ := hω.1.2 m hm
  have hno := (hω.isOrdinal (ZF.modelsKP hZF)).mem hnω
  obtain ⟨p, hp, _⟩ := ZF.ordinalExponentiation_existsUnique hZF I hD hno
  have hpω := ZF.ordinalExponentiation_mem_omega hZF I hω
    (ds_two_mem_l hZF.1 hω ⟨o, ho, hd⟩) hnω hp
  refine ⟨n, p, hnω, hpω, hp, ?_⟩
  exact (ZF.ordinalExponentiation_exponent_eq_or_mem hZF I hD ho hd.predecessor_mem hno hp).elim
    (fun e => e ▸ hn.predecessor_mem)
    (fun h => ((hω.isOrdinal (ZF.modelsKP hZF)).mem hpω).transitive n h m hn.predecessor_mem)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 首差坐标与规范有理数距离

对不同点取模型内部的最小差异坐标 n，距离为有理数码 (1,2ⁿ)；相同点取 (0,1)。
最小元来自原公式分离，涵盖非标准坐标，并不要求外部可搜索这些坐标。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Diff_d (f g n : M.Domain) : Prop :=
  ∃ x y, M.PairMember I n x f ∧ M.PairMember I n y g ∧ x ≠ y
def diff_m {d} (f g n : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (Formula.orderedPairMem 𝒞 n.weaken.weaken (.bound 1) f.weaken.weaken) (.conj
    (Formula.orderedPairMem 𝒞 n.weaken.weaken .newest g.weaken.weaken)
    (.neg (Formula.extensionalEq (.bound 1) .newest)))))
derive_free_closed diff_m
theorem diff_sat_l (hE : Extensional M) {d} (ρ : Env M d) (f g n : Term d) :
    Formula.satisfies ρ (diff_m (𝒞 := 𝒞) f g n) ↔ Diff_d I (f.eval ρ) (g.eval ρ) (n.eval ρ) := by
  simp only [diff_m, Diff_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]; rfl

def Sep_d (ω f g n : M.Domain) : Prop :=
  (n = ω ∧ f = g) ∨ (M.mem n ω ∧ Senv_agree_d I n f g ∧ Diff_d I f g n)
def sep_m {d} (ω f g n : Term d) : Formula 1 d := .disj
  (.conj (Formula.extensionalEq n ω) (Formula.extensionalEq f g))
  (.conj (.mem n ω) (.conj (senv_agree_m (𝒞 := 𝒞) n f g) (diff_m (𝒞 := 𝒞) f g n)))
derive_free_closed sep_m
theorem sep_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω f g n : Term d) :
    Formula.satisfies ρ (sep_m (𝒞 := 𝒞) ω f g n) ↔ Sep_d I (ω.eval ρ) (f.eval ρ) (g.eval ρ) (n.eval ρ) := by
  simp only [sep_m, Sep_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_mem_iff,
    senv_agree_sat_l I, diff_sat_l I hE]

theorem ds_diff_not_agree_l {f g n i : M.Domain} (hg : M.IsSetFunction I g)
    (hd : Diff_d I f g i) (hi : M.mem i n) : ¬ Senv_agree_d I n f g := by
  rintro ha
  obtain ⟨x, y, hx, hy, hxy⟩ := hd
  exact hxy (hg.2 i x y ((ha i x hi).mp hx) hy)

theorem ds_sep_exists_l (hZF : M.Models ZF) {ω X f g} (hω : M.IsOmega ω)
    (hf : M.IsSetFunctionFromTo I f ω X) (hg : M.IsSetFunctionFromTo I g ω X) :
    ∃ n, Sep_d I ω f g n := by
  classical
  by_cases e : f = g
  · exact ⟨ω, Or.inl ⟨rfl, e⟩⟩
  obtain ⟨i, x, y, hi, hx, hy, hxy⟩ := ds_differ_l I hZF.1 hf hg e
  let ρ : Env M 2 := (⟨fun _ => f, fun _ => f⟩ : Env M 1).push g
  let φ : UnarySchema 2 := { body := diff_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest }
  obtain ⟨T, hT'⟩ := ZF.separation_exists_d hZF φ ρ ω
  have hT j : M.mem j T ↔ M.mem j ω ∧ Diff_d I f g j :=
    (hT' j).trans (and_congr_right fun _ => diff_sat_l I hZF.1 _ _ _ _)
  obtain ⟨n, hn, hm⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF)
    ⟨i, (hT i).mpr ⟨hi, x, y, hx, hy, hxy⟩⟩
  obtain ⟨hnω, hd⟩ := (hT n).mp hn
  refine ⟨n, Or.inr ⟨hnω, fun j a hj => ?_, hd⟩⟩
  have hjω := hω.transitive (ZF.modelsKP hZF) n hnω j hj
  have eqv b c (hb : M.PairMember I j b f) (hc : M.PairMember I j c g) : b = c :=
    Classical.byContradiction (fun h => hm j ((hT j).mpr ⟨hjω, b, c, hb, hc, h⟩) hj)
  constructor
  · intro h
    obtain ⟨b, _, hb⟩ := hg.2.2 j hjω
    exact (eqv a b h hb).symm ▸ hb
  · intro h
    obtain ⟨b, _, hb⟩ := hf.2.2 j hjω
    exact eqv b a hb h ▸ hb

/-- 首差指数的反序比较，精确对应有限前缀一致。 -/
theorem ds_sep_ball_l (hZF : M.Models ZF) {ω X f g i n} (hω : M.IsOmega ω)
    (hg : M.IsSetFunctionFromTo I g ω X) (hs : Sep_d I ω f g i) (hn : M.mem n ω) :
    (i = ω ∨ n = i ∨ M.mem n i) ↔ Senv_agree_d I n f g := by
  rcases hs with ⟨hi, e⟩ | ⟨hi, ha, hd⟩
  · exact iff_of_true (Or.inl hi) (by subst g; exact fun _ _ _ => Iff.rfl)
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with e | e | hni
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ω (e ▸ hi)).elim
      · exact e.symm ▸ ha
      · exact fun j x hj => ha j x ((hω.isOrdinal (ZF.modelsKP hZF)).mem hi |>.transitive n hni j hj)
    · rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn i hi with e | hni | hin
      · exact Or.inr (Or.inl (hZF.1.eq_of_same_members n i e))
      · exact Or.inr (Or.inr hni)
      · exact (ds_diff_not_agree_l I hg.1 hd hin h).elim

theorem ds_sep_unique_l (hZF : M.Models ZF) {ω X f g n m} (hω : M.IsOmega ω)
    (hg : M.IsSetFunctionFromTo I g ω X) (hn : Sep_d I ω f g n) (hm : Sep_d I ω f g m) : n = m := by
  rcases hn with ⟨en, e⟩ | ⟨hn, ha, hd⟩ <;> rcases hm with ⟨em, e'⟩ | ⟨hm, hb, he⟩
  · exact en.trans em.symm
  · obtain ⟨x, y, hx, hy, hxy⟩ := he
    exact (hxy (hg.1.2 m x y (e ▸ hx) hy)).elim
  · obtain ⟨x, y, hx, hy, hxy⟩ := hd
    exact (hxy (hg.1.2 n x y (e' ▸ hx) hy)).elim
  · rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn m hm with e | hnm | hmn
    · exact hZF.1.eq_of_same_members n m e
    · exact (ds_diff_not_agree_l I hg.1 hd hnm hb).elim
    · exact (ds_diff_not_agree_l I hg.1 he hmn ha).elim

def Dist_d (ω D z o f g q : M.Domain) : Prop := ∃ n, Sep_d I ω f g n ∧ Dyad_d I ω D z o n q
def dist_m {d} (ω D z o f g q : Term d) : Formula 1 d := .existsE (.conj
  (sep_m (𝒞 := 𝒞) ω.weaken f.weaken g.weaken .newest)
  (dyad_m (𝒞 := 𝒞) ω.weaken D.weaken z.weaken o.weaken .newest q.weaken))
derive_free_closed dist_m

theorem dist_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω D z o f g q : Term d) :
    Formula.satisfies ρ (dist_m (𝒞 := 𝒞) ω D z o f g q) ↔
      Dist_d I (ω.eval ρ) (D.eval ρ) (z.eval ρ) (o.eval ρ) (f.eval ρ) (g.eval ρ) (q.eval ρ) := by
  simp only [dist_m, Dist_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sep_sat_l I hE, dyad_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem ds_dist_exists_l (hZF : M.Models ZF) {ω X D z o f g} (hω : M.IsOmega ω)
    (hD : M.mem D ω) (hf : M.IsSetFunctionFromTo I f ω X) (hg : M.IsSetFunctionFromTo I g ω X) :
    ∃ q, Dist_d I ω D z o f g q := by
  obtain ⟨n, hn⟩ := ds_sep_exists_l I hZF hω hf hg
  obtain ⟨q, hq⟩ := dyad_exists_l I hZF hω hD (hn.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  exact ⟨q, n, hn, hq⟩

theorem ds_dist_unique_l (hZF : M.Models ZF) {ω X D z o f g q r} (hω : M.IsOmega ω)
    (hD : M.IsOrdinal D) (hg : M.IsSetFunctionFromTo I g ω X)
    (hq : Dist_d I ω D z o f g q) (hr : Dist_d I ω D z o f g r) : q = r := by
  obtain ⟨n, hn, hq⟩ := hq
  obtain ⟨m, hm, hr⟩ := hr
  have e := ds_sep_unique_l I hZF hω hg hn hm
  subst m
  exact dyad_unique_l I hZF hω hD hq hr

/-- 数值闭球 d(f,g)≤2⁻ⁿ 恰是长度 n 的前缀一致关系。 -/
theorem ds_dist_ball_l (hZF : M.Models ZF) {ω X D z o f g n q r} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o)
    (hg : M.IsSetFunctionFromTo I g ω X) (hn : M.mem n ω)
    (hq : Dist_d I ω D z o f g q) (hr : Dyad_d I ω D z o n r) :
    Qle_d I z o q r ↔ Senv_agree_d I n f g := by
  obtain ⟨i, hi, hq⟩ := hq
  exact (dyad_le_l I hZF hω hz ho hd hq hr).trans (ds_sep_ball_l I hZF hω hg hi hn)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 内部前缀超度量及距离图

距离是模型内规范有理数对的实际函数图。对称性、零距离分离、超度量不等式和
闭球刻画均在同一表示下证明；不从外部实数或外部函数空间取得任何模型数据。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Dist_d.symm_l {ω D z o f g q : M.Domain} (h : Dist_d I ω D z o f g q) :
    Dist_d I ω D z o g f q := by
  obtain ⟨n, hn, hq⟩ := h
  refine ⟨n, ?_, hq⟩
  rcases hn with ⟨en, e⟩ | ⟨hn, ha, x, y, hx, hy, hxy⟩
  · exact Or.inl ⟨en, e.symm⟩
  · exact Or.inr ⟨hn, ha.symm_l, y, x, hy, hx, fun e => hxy e.symm⟩

theorem ds_dist_zero_l (hKP : M.Models KP) {ω X D z o f g q}
    (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o) (hg : M.IsSetFunctionFromTo I g ω X)
    (h : Dist_d I ω D z o f g q) : I.Codes q z o ↔ f = g := by
  have hzo : o ≠ z := fun e => ho.elim fun a ha => hz a (e ▸ ha.2.predecessor_mem)
  obtain ⟨n, hs, hd⟩ := h
  constructor
  · intro hq
    rcases hd with ⟨en, _⟩ | ⟨_, p, _, _, hq'⟩
    · exact hs.elim And.right (fun h => (KP.mem_irrefl_d hKP ω (en ▸ h.1)).elim)
    · exact (hzo (I.injective hq' hq).1).elim
  · intro e
    have en : n = ω := hs.elim And.left (fun ⟨_, _, x, y, hx, hy, hxy⟩ =>
      (hxy (hg.1.2 n x y (e ▸ hx) hy)).elim)
    exact hd.elim And.right (fun h => (KP.mem_irrefl_d hKP ω (en ▸ h.1)).elim)

/-- d(f,h)≤max(d(f,g),d(g,h))，用全序上等价的两个比较之一表达。 -/
theorem ds_ultrametric_l (hZF : M.Models ZF) {ω X D z o f g h p q r} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ho : M.IsOrdinalOne o) (hd : M.SuccessorOf D o)
    (hg : M.IsSetFunctionFromTo I g ω X) (hh : M.IsSetFunctionFromTo I h ω X)
    (hp : Dist_d I ω D z o f g p) (hq : Dist_d I ω D z o g h q)
    (hr : Dist_d I ω D z o f h r) : Qle_d I z o r p ∨ Qle_d I z o r q := by
  have hD := Structure.IsOrdinalTwo.isOrdinal (ZF.modelsKP hZF) ⟨o, ho, hd⟩
  have refl {n v} (h : Dyad_d I ω D z o n v) : Qle_d I z o v v :=
    (dyad_le_l I hZF hω hz ho hd h h).mpr (Or.inr (Or.inl rfl))
  obtain ⟨n, hs, hpn⟩ := hp
  obtain ⟨m, ht, hqm⟩ := hq
  rcases hs with ⟨_, e⟩ | ⟨hn, ha, hb⟩
  · subst g
    have e := ds_dist_unique_l I hZF hω hD hh hr ⟨m, ht, hqm⟩
    exact Or.inr (e.symm ▸ refl hqm)
  · rcases ht with ⟨_, e⟩ | ⟨hm, hc, he⟩
    · subst h
      have e := ds_dist_unique_l I hZF hω hD hg hr ⟨n, Or.inr ⟨hn, ha, hb⟩, hpn⟩
      exact Or.inl (e.symm ▸ refl hpn)
    · have left (hsub : M.MemberSubset n m) : Qle_d I z o r p :=
        (ds_dist_ball_l I hZF hω hz ho hd hh hn hr hpn).mpr
          (fun i x hi => (ha i x hi).trans (hc i x (hsub i hi)))
      have right (hsub : M.MemberSubset m n) : Qle_d I z o r q :=
        (ds_dist_ball_l I hZF hω hz ho hd hh hm hr hqm).mpr
          (fun i x hi => (ha i x (hsub i hi)).trans (hc i x hi))
      rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn m hm with e | hnm | hmn
      · exact Or.inl (left (fun i hi => (e i).mp hi))
      · exact Or.inl (left (((hω.isOrdinal (ZF.modelsKP hZF)).mem hm).transitive n hnm))
      · exact Or.inr (right (((hω.isOrdinal (ZF.modelsKP hZF)).mem hn).transitive m hmn))

/-- 实际构造 0、1、2、点对域、分数码域和全部距离组成的模型内函数图。 -/
theorem ds_metric_graph_l (hZF : M.Models ZF) {ω X B} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) : ∃ z o D P Q F,
    (∀ x, ¬ M.mem x z) ∧ M.IsOrdinalOne o ∧ M.SuccessorOf D o ∧
    M.IsCartesianProduct I P B B ∧ M.IsCartesianProduct I Q ω ω ∧
    M.IsSetFunctionFromTo I F P Q ∧ ∀ f g p q, I.Codes p f g →
      (M.PairMember I p q F ↔ M.mem f B ∧ M.mem g B ∧ Dist_d I ω D z o f g q) := by
  obtain ⟨z, o, D, hz, hzω, ho, hoω, hd, hdω⟩ := ds_digits_l hω
  have hD := (hω.isOrdinal (ZF.modelsKP hZF)).mem hdω
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I B B
  obtain ⟨Q, hQ⟩ := ZF.exists_cartesianProduct hZF I ω ω
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push D).push z).push o
  let φ : BinarySchema 4 := {
    body := .existsE (.existsE (.conj (𝒞.code (.bound 3) (.bound 1) .newest)
      (dist_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest (.bound 2)))) }
  have hp p q : φ.denote ρ p q ↔ ∃ f g, I.Codes p f g ∧ Dist_d I ω D z o f g q := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, dist_sat_l I hZF.1]; rfl
  obtain ⟨F, hF, hf⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := P) (target := Q)
    (by
      intro p hpP
      obtain ⟨f, hf, g, hg, hfg⟩ := (hP p).mp hpP
      obtain ⟨q, hq⟩ := ds_dist_exists_l I hZF hω hdω ((hB f).mp hf) ((hB g).mp hg)
      exact ⟨q, (hp p q).mpr ⟨f, g, hfg, hq⟩⟩)
    (by
      intro p hpP q r hq hr
      obtain ⟨f, g, hfg, hq⟩ := (hp p q).mp hq
      obtain ⟨f', g', hfg', hr⟩ := (hp p r).mp hr
      obtain ⟨rfl, rfl⟩ := I.injective hfg hfg'
      obtain ⟨u, _, v, hv, huv⟩ := (hP p).mp hpP
      obtain ⟨rfl, rfl⟩ := I.injective hfg huv
      exact ds_dist_unique_l I hZF hω hD ((hB g).mp hv) hq hr)
    (by
      intro p q _ hq
      obtain ⟨f, g, _, n, _, hq⟩ := (hp p q).mp hq
      exact (hQ q).mpr (hq.elim (fun h => ⟨z, hzω, o, hoω, h.2⟩)
        (fun ⟨_, v, hv, _, h⟩ => ⟨o, hoω, v, hv, h⟩)))
  refine ⟨z, o, D, P, Q, F, hz, ho, hd, hP, hQ, hF, fun f g p q hfg => ?_⟩
  rw [hf p q, hp p q]
  constructor
  · rintro ⟨hpP, u, v, huv, hq⟩
    obtain ⟨rfl, rfl⟩ := I.injective hfg huv
    obtain ⟨u, hu, v, hv, huv⟩ := (hP p).mp hpP
    obtain ⟨rfl, rfl⟩ := I.injective hfg huv
    exact ⟨hu, hv, hq⟩
  · rintro ⟨hfB, hgB, hq⟩
    exact ⟨(hP p).mpr ⟨f, hfB, g, hgB, hfg⟩, f, g, hfg, hq⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 内部开覆盖紧致性

有限子覆盖由模型内部的有限集合见证。Cantor 的证明先构造不能有限覆盖的前缀树，
再由其二分后继生成内部坏分支，与原开覆盖矛盾；整个证明仅用 ZF。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Cover_d (B A : M.Domain) : Prop := ∀ f, M.mem f B → ∃ U, M.mem U A ∧ M.mem f U
def cover_m {d} (B A : Term d) : Formula 1 d :=
  Formula.forallMem B (Formula.existsMem A.weaken (.mem (.bound 1) .newest))
derive_free_closed cover_m
theorem cover_sat_l {d} (ρ : Env M d) (B A : Term d) :
    Formula.satisfies ρ (cover_m B A) ↔ Cover_d (M := M) (B.eval ρ) (A.eval ρ) := by
  simp only [cover_m, Cover_d, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

def Fcyl_d (ω B A s : M.Domain) : Prop := ∃ K, Finite_d I ω K ∧ M.MemberSubset K A ∧
  ∀ f, M.mem f B → M.MemberSubset s f → ∃ U, M.mem U K ∧ M.mem f U
def fcyl_m {d} (ω B A s : Term d) : Formula 1 d := .existsE (.conj
  (finite_m 𝒞 ω.weaken .newest) (.conj (Formula.subset .newest A.weaken)
    (Formula.forallMem B.weaken (.imp (Formula.subset s.weaken.weaken .newest)
      (Formula.existsMem (.bound 1) (.mem (.bound 1) .newest))))))
derive_free_closed fcyl_m
theorem fcyl_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B A s : Term d) :
    Formula.satisfies ρ (fcyl_m (𝒞 := 𝒞) ω B A s) ↔ Fcyl_d I (ω.eval ρ) (B.eval ρ) (A.eval ρ) (s.eval ρ) := by
  simp only [fcyl_m, Fcyl_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    finite_sat_l I hE, Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

def Compact_d (ω B τ : M.Domain) : Prop := ∀ A, M.MemberSubset A τ → Cover_d B A →
  ∃ K, Finite_d I ω K ∧ M.MemberSubset K A ∧ Cover_d B K
def compact_m {d} (ω B τ : Term d) : Formula 1 d := .forallE
  (.imp (Formula.subset .newest τ.weaken) (.imp (cover_m B.weaken .newest) (.existsE
    (.conj (finite_m 𝒞 ω.weaken.weaken .newest) (.conj (Formula.subset .newest (.bound 1))
      (cover_m B.weaken.weaken .newest))))))
derive_free_closed compact_m

theorem compact_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B τ : Term d) :
    Formula.satisfies ρ (compact_m (𝒞 := 𝒞) ω B τ) ↔ Compact_d I (ω.eval ρ) (B.eval ρ) (τ.eval ρ) := by
  simp only [compact_m, Compact_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, cover_sat_l, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, finite_sat_l I hE, Definitional.Term.eval_weaken]; rfl

/-- 两个后继柱集的有限覆盖合并为父柱集的有限覆盖。 -/
theorem ds_fcyl_join_l (hZF : M.Models ZF) {ω D B A s n t u a b}
    (hω : M.IsOmega ω) (hB : M.IsFunctionSpace I B ω D)
    (hD : ∀ x, M.mem x D ↔ x = a ∨ x = b) (hn : M.mem n ω)
    (hs : M.IsSetFunctionFromTo I s n D) (ht : Fseq_end_d I ω t s a) (hu : Fseq_end_d I ω u s b)
    (h : Fcyl_d I ω B A t) (k : Fcyl_d I ω B A u) : Fcyl_d I ω B A s := by
  obtain ⟨K, hk, hKA, hc⟩ := h
  obtain ⟨L, hl, hLA, hd⟩ := k
  obtain ⟨J, hJ⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) K L
  refine ⟨J, ZF.finite_union_l I hZF hω hk hl hJ,
    fun V hV => ((hJ V).mp hV).elim (hKA V) (hLA V), fun f hf hsf => ?_⟩
  obtain ⟨x, hx, hnx⟩ := ((hB f).mp hf).2.2 n hn
  rcases (hD x).mp hx with rfl | rfl
  · obtain ⟨V, hV, hfV⟩ := hc f hf (ds_append_sub_l I hZF.1 hs ht hsf hnx)
    exact ⟨V, (hJ V).mpr (Or.inl hV), hfV⟩
  · obtain ⟨V, hV, hfV⟩ := hd f hf (ds_append_sub_l I hZF.1 hs hu hsf hnx)
    exact ⟨V, (hJ V).mpr (Or.inr hV), hfV⟩

/-- 任意内部二元字母表的序列空间满足开覆盖紧致性。 -/
theorem ds_binary_compact_l (hZF : M.Models ZF) {ω D B S τ a b}
    (hω : M.IsOmega ω) (hD : ∀ x, M.mem x D ↔ x = a ∨ x = b)
    (hB : M.IsFunctionSpace I B ω D) (hS : Fseq_space_d I ω D S)
    (hτ : ∀ U, M.mem U τ ↔ Open_d S B U) : Compact_d I ω B τ := by
  classical
  intro A hA hcover
  apply Classical.byContradiction
  intro hno
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push B).push A
  let φ : UnarySchema 3 := { body := .neg (fcyl_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest) }
  obtain ⟨T, hT'⟩ := ZF.separation_exists_d hZF φ ρ S
  have hT s : M.mem s T ↔ M.mem s S ∧ ¬ Fcyl_d I ω B A s := by
    have h := hT' s
    simp only [φ, Formula.satisfies_neg_iff, fcyl_sat_l I hZF.1] at h
    exact h
  obtain ⟨e, he, heω⟩ := hω.1.1
  have het : M.mem e T := (hT e).mpr ⟨(hS e).mpr ⟨e, heω, ds_empty_fun_l I he⟩,
    fun ⟨K, hk, hKA, hc⟩ => hno ⟨K, hk, hKA, fun f hf => hc f hf (fun p hp => (he p hp).elim)⟩⟩
  have serial s (hsT : M.mem s T) : ∃ t, M.mem t T ∧
      (Fseq_end_d I ω t s a ∨ Fseq_end_d I ω t s b) := by
    obtain ⟨hsS, hsbad⟩ := (hT s).mp hsT
    obtain ⟨n, hn, hs⟩ := (hS s).mp hsS
    obtain ⟨m, t, hm, ht, hta⟩ := ZF.fseq_end_exists_l I hZF hω hn hs ((hD a).mpr (Or.inl rfl))
    obtain ⟨k, u, hk, hu, hub⟩ := ZF.fseq_end_exists_l I hZF hω hn hs ((hD b).mpr (Or.inr rfl))
    by_cases h : Fcyl_d I ω B A t
    · exact ⟨u, (hT u).mpr ⟨(hS u).mpr ⟨k, hk, hu⟩,
        fun g => hsbad (ds_fcyl_join_l I hZF hω hB hD hn hs hta hub h g)⟩, Or.inr hub⟩
    · exact ⟨t, (hT t).mpr ⟨(hS t).mpr ⟨m, hm, ht⟩, h⟩, Or.inl hta⟩
  obtain ⟨f, hf, branch⟩ := ds_binary_path_l I hZF hω
    (fun s hs => (hS s).mp ((hT s).mp hs).1) he het serial
  obtain ⟨U, hUA, hfU⟩ := hcover f ((hB f).mpr hf)
  obtain ⟨s, hsS, hsf, hU⟩ := ((hτ U).mp (hA U hUA)).2 f hfU
  obtain ⟨n, hn, hs⟩ := (hS s).mp hsS
  obtain ⟨t, htT, ht, htf⟩ := branch n hn
  have e := ((ds_restrict_iff_l I hs hf.1).mpr hsf).eq hZF.1 ((ds_restrict_iff_l I ht hf.1).mpr htf)
  subst t
  apply ((hT s).mp htT).2
  obtain ⟨E, hE⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨K, hK⟩ := KP.exists_insert (ZF.modelsKP hZF) E U
  have hk := ZF.finite_insert_l I hZF hω (ZF.finite_empty_l I hZF hω hE) hK
  exact ⟨K, hk, fun V hV => ((hK V).mp hV).elim (fun h => (hE V h).elim) (fun e => e ▸ hUA),
    fun g hg hsg => ⟨U, (hK U).mpr (Or.inr rfl), hU g hg hsg⟩⟩

/-- Cantor 紧致性的最终接口；字母表和二分选择均由已有具体构造提供。 -/
theorem cantor_compact_l (hZF : M.Models ZF) {ω D C S τ}
    (hω : M.IsOmega ω) (hD : M.IsOrdinalTwo D) (hC : M.IsFunctionSpace I C ω D)
    (hS : Fseq_space_d I ω D S) (hτ : ∀ U, M.mem U τ ↔ Open_d S C U) : Compact_d I ω C τ := by
  obtain ⟨a, b, _, hd⟩ := ds_two_l hZF.1 hD
  exact ds_binary_compact_l I hZF hω hd hC hS hτ

end YesMetaZFC.SetTheory.Descriptive

/-! ## Baire 空间的具体非紧致开覆盖

按第零坐标的值分割为空间的开切片。任意有限子覆盖都会把 ω 单射进其有限索引集，
与内部自然数的无限性矛盾。覆盖族和这张单射都在模型内构造。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Slice_d (B z a U : M.Domain) : Prop := ∀ f, M.mem f U ↔ M.mem f B ∧ M.PairMember I z a f
def slice_m {d} (B z a U : Term d) : Formula 1 d := .forallE
  (.iff (.mem .newest U.weaken) (.conj (.mem .newest B.weaken)
    (Formula.orderedPairMem 𝒞 z.weaken a.weaken .newest)))
derive_free_closed slice_m
theorem slice_sat_l {d} (ρ : Env M d) (B z a U : Term d) :
    Formula.satisfies ρ (slice_m (𝒞 := 𝒞) B z a U) ↔
      Slice_d I (B.eval ρ) (z.eval ρ) (a.eval ρ) (U.eval ρ) := by
  simp only [slice_m, Slice_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken]; rfl

theorem ds_slice_open_l (hZF : M.Models ZF) {ω X B S z a U}
    (hω : M.IsOmega ω) (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hz : M.mem z ω) (hU : Slice_d I B z a U) : Open_d S B U := by
  refine ⟨fun f hf => ((hU f).mp hf).1, fun f hf => ?_⟩
  obtain ⟨hfB, hfa⟩ := (hU f).mp hf
  obtain ⟨n, hn, hnω⟩ := hω.1.2 z hz
  obtain ⟨s, hs, hr, _⟩ := ds_prefix_l I hZF hω ((hB f).mp hfB) hnω
  refine ⟨s, (hS s).mpr ⟨n, hnω, hs⟩, (ds_restrict_iff_l I hs ((hB f).mp hfB).1).mp hr,
    fun g hg hsg => (hU g).mpr ⟨hg, ?_⟩⟩
  have hsa := (hr.2 z a).mpr ⟨hn.predecessor_mem, hfa⟩
  exact hsa.elim fun p hp => ⟨p, hp.1, hsg p hp.2⟩

/-- 返回没有内部有限子覆盖的实际开覆盖族。 -/
theorem baire_noncompact_cover_l (hZF : M.Models ZF) {ω B S τ}
    (hB : Baire_d I ω B) (hS : Fseq_space_d I ω ω S)
    (hτ : ∀ U, M.mem U τ ↔ Open_d S B U) : ∃ A, M.MemberSubset A τ ∧ Cover_d B A ∧
      ∀ K, Finite_d I ω K → M.MemberSubset K A → ¬ Cover_d B K := by
  obtain ⟨z, _, hz⟩ := hB.1.1.1
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push B).push z
  let φ : UnarySchema 3 := {
    body := Formula.existsMem (.bound 3)
      (slice_m (𝒞 := 𝒞) (.bound 3) (.bound 2) .newest (.bound 1)) }
  have hp U : φ.denote ρ U ↔ ∃ a, M.mem a ω ∧ Slice_d I B z a U := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, slice_sat_l I]; rfl
  obtain ⟨A, hA'⟩ := ZF.separation_exists_d hZF φ ρ P
  have hA U : M.mem U A ↔ ∃ a, M.mem a ω ∧ Slice_d I B z a U :=
    ((hA' U).trans (and_congr_right fun _ => hp U)).trans
      ⟨And.right, fun h => ⟨(hP U).mpr (fun f hf => h.elim fun a ha => ((ha.2 f).mp hf).1), h⟩⟩
  refine ⟨A, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨a, _, ha⟩ := (hA U).mp hU
    exact (hτ U).mpr (ds_slice_open_l I hZF hB.1 hB.2 hS hz ha)
  · intro f hf
    obtain ⟨a, ha, hfa⟩ := ((hB.2 f).mp hf).2.2 z hz
    let ψ : UnarySchema 2 := { body := Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) .newest }
    obtain ⟨U, hU'⟩ := ZF.separation_exists_d hZF ψ
      ((⟨fun _ => z, fun _ => z⟩ : Env M 1).push a) B
    have hU : Slice_d I B z a U := fun g => (hU' g).trans (and_congr_right fun _ =>
      Formula.satisfies_orderedPairMem_iff I _ _ _ _)
    exact ⟨U, (hA U).mpr ⟨a, ha, hU⟩, (hU f).mpr ⟨hf, hfa⟩⟩
  · intro K ⟨n, hn, E, hE⟩ hKA hcover
    let δ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push z).push K
    let ψ : BinarySchema 3 := {
      body := .conj (.mem .newest (.bound 2))
        (slice_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 1) .newest) }
    have hψ a U : ψ.denote δ a U ↔ M.mem U K ∧ Slice_d I B z a U := by
      simp only [ψ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, slice_sat_l I]; rfl
    obtain ⟨F, hF⟩ := ZF.exists_setInjectionFromTo_of_denote hZF I ψ δ (source := ω) (target := K)
      (by
        intro a ha
        obtain ⟨f, hf, he⟩ := ZF.exists_constantFunction hZF I (source := ω) ha
        obtain ⟨U, hUK, hfU⟩ := hcover f ((hB.2 f).mpr hf)
        obtain ⟨b, _, hb⟩ := (hA U).mp (hKA U hUK)
        have e := ((he z b).mp ((hb f).mp hfU).2).2
        exact ⟨U, (hψ a U).mpr ⟨hUK, e ▸ hb⟩⟩)
      (fun a _ U V hU hV => hZF.1.eq_of_same_members U V
        (fun f => (((hψ a U).mp hU).2 f).trans (((hψ a V).mp hV).2 f).symm))
      (fun a U _ hU => ((hψ a U).mp hU).1)
      (by
        intro a b U ha _ hau hbu
        obtain ⟨f, hf, he⟩ := ZF.exists_constantFunction hZF I (source := ω) ha
        have hfU := (((hψ a U).mp hau).2 f).mpr ⟨(hB.2 f).mpr hf, (he z a).mpr ⟨hz, rfl⟩⟩
        exact (((he z b).mp ((((hψ b U).mp hbu).2 f).mp hfU).2).2).symm)
    exact ZF.omega_not_le_finite_l I hZF hB.1 n hn (ZF.exists_compositionInjection hZF I hF hE)

theorem baire_not_compact_l (hZF : M.Models ZF) {ω B S τ}
    (hB : Baire_d I ω B) (hS : Fseq_space_d I ω ω S)
    (hτ : ∀ U, M.mem U τ ↔ Open_d S B U) : ¬ Compact_d I ω B τ := by
  obtain ⟨A, hA, hc, hn⟩ := baire_noncompact_cover_l I hZF hB hS hτ
  intro h
  obtain ⟨K, hk, hKA, hcover⟩ := h A hA hc
  exact hn K hk hKA hcover

end YesMetaZFC.SetTheory.Descriptive

/-! ## Baire 与 Cantor 空间的具体比较

两空间使用同一内部 ω 和同一配对约定。Cantor 的拓扑正是 Baire 的子空间拓扑；
Cantor 在 Baire 中闭且无处稠密。其点集通过已有特征函数构造与内部幂集等势。
-/

namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 一次取得两个空间、内部可数前缀集、完整拓扑及各自的开集判据。 -/
theorem baire_cantor_l (hZF : M.Models ZF) : ∃ ω D B C S T τ υ,
    Baire_d I ω B ∧ M.IsOrdinalTwo D ∧ M.IsFunctionSpace I C ω D ∧
    Fseq_space_d I ω ω S ∧ M.CardinalLessOrEqual I S ω ∧
    Fseq_space_d I ω D T ∧ M.CardinalLessOrEqual I T ω ∧
    Top_d B τ ∧ Top_d C υ ∧
    (∀ U, M.mem U τ ↔ Open_d S B U) ∧ (∀ U, M.mem U υ ↔ Open_d T C U) := by
  obtain ⟨ω, D, B, C, S, T, hB, hD, hC, hS, hs, hT, ht⟩ := ds_spaces_l I hZF
  obtain ⟨τ, hτ, hτ'⟩ := ds_topology_l I hZF hB.1 hB.2 hS
  obtain ⟨υ, hυ, hυ'⟩ := ds_topology_l I hZF hB.1 hC hT
  exact ⟨ω, D, B, C, S, T, τ, υ, hB, hD, hC, hS, hs, hT, ht, hτ, hυ, hτ', hυ'⟩

theorem cantor_nonempty_l (hZF : M.Models ZF) {ω C} (hC : Cantor_d I ω C) : ∃ f, M.mem f C := by
  obtain ⟨_, D, hD, hC⟩ := hC
  obtain ⟨a, ha⟩ := hD.nonempty
  obtain ⟨f, hf, _⟩ := ZF.exists_constantFunction hZF I (source := ω) ha
  exact ⟨f, (hC f).mpr hf⟩

theorem baire_nonempty_l (hZF : M.Models ZF) {ω B} (hB : Baire_d I ω B) : ∃ f, M.mem f B := by
  obtain ⟨a, _, ha⟩ := hB.1.1.1
  obtain ⟨f, hf, _⟩ := ZF.exists_constantFunction hZF I (source := ω) ha
  exact ⟨f, (hB.2 f).mpr hf⟩

/-- Cantor 空间的相对补可由非二元坐标的有限前缀见证。 -/
theorem cantor_closed_l (hZF : M.Models ZF) {ω B C S}
    (hB : Baire_d I ω B) (hC : Cantor_d I ω C) (hS : Fseq_space_d I ω ω S) :
    ∃ V, (∀ f, M.mem f V ↔ M.mem f B ∧ ¬ M.mem f C) ∧ Open_d S B V := by
  obtain ⟨_, D, _, hc⟩ := hC
  obtain ⟨V, hV⟩ := KP.difference_exists_d (ZF.modelsKP hZF) C B
  refine ⟨V, hV, fun f hf => ((hV f).mp hf).1, fun f hf => ?_⟩
  obtain ⟨hfB, hfC⟩ := (hV f).mp hf
  have hf := (hB.2 f).mp hfB
  have bad : ∃ i a, M.mem i ω ∧ M.PairMember I i a f ∧ ¬ M.mem a D := by
    apply Classical.byContradiction
    intro h
    apply hfC
    apply (hc f).mpr
    refine ⟨hf.1, hf.2.1, fun i hi => ?_⟩
    obtain ⟨a, _, ha⟩ := hf.2.2 i hi
    exact ⟨a, Classical.byContradiction (fun hn => h ⟨i, a, hi, ha, hn⟩), ha⟩
  obtain ⟨i, a, hi, hia, ha⟩ := bad
  obtain ⟨n, hni, hn⟩ := hB.1.1.2 i hi
  obtain ⟨s, hs, hsf, _⟩ := ds_prefix_l I hZF hB.1 hf hn
  refine ⟨s, (hS s).mpr ⟨n, hn, hs⟩, (ds_restrict_iff_l I hs hf.1).mp hsf, fun g hg hsg => ?_⟩
  apply (hV g).mpr
  refine ⟨hg, fun hgc => ?_⟩
  have hr := (ds_restrict_iff_l I hs ((hB.2 g).mp hg).1).mpr hsg
  exact ha (((hc g).mp hgc).output_mem_of_pairMember
    ((hr.2 i a).mp ((hsf.2 i a).mpr ⟨hni.predecessor_mem, hia⟩)).2)

/-- 每个非空 Baire 开集都有非二元点；结合闭性即 Cantor 的无处稠密性。 -/
theorem cantor_empty_interior_l (hZF : M.Models ZF) {ω B C S U}
    (hB : Baire_d I ω B) (hC : Cantor_d I ω C) (hS : Fseq_space_d I ω ω S)
    (hU : Open_d S B U) (hn : ∃ f, M.mem f U) : ∃ g, M.mem g U ∧ ¬ M.mem g C := by
  obtain ⟨hω, D, hD, hC⟩ := hC
  obtain ⟨f, hf⟩ := hn
  obtain ⟨s, hs, _, hu⟩ := hU.2 f hf
  obtain ⟨n, hn, hsn⟩ := (hS s).mp hs
  obtain ⟨g, hg, hr, hng⟩ := ds_extend_l I hZF hω hn hsn (ds_two_mem_l hZF.1 hω hD)
  exact ⟨g, hu g ((hB.2 g).mpr hg) ((ds_restrict_iff_l I hsn hg.1).mp hr),
    fun hgc => KP.mem_irrefl_d (ZF.modelsKP hZF) D (((hC g).mp hgc).output_mem_of_pairMember hng)⟩

/-- 内部子字母表空间的开集恰为大空间开集的相对迹。 -/
theorem ds_subspace_l (hZF : M.Models ZF) {ω X Y B C S T V}
    (hω : M.IsOmega ω) (hXY : M.MemberSubset Y X)
    (hB : M.IsFunctionSpace I B ω X) (hC : M.IsFunctionSpace I C ω Y)
    (hS : Fseq_space_d I ω X S) (hT : Fseq_space_d I ω Y T) :
    Open_d T C V ↔ ∃ U, Open_d S B U ∧ ∀ f, M.mem f V ↔ M.mem f C ∧ M.mem f U := by
  have hCB := ds_space_mono_l I hXY hC hB
  constructor
  · intro hV
    let ρ : Env M 3 := ((⟨fun _ => T, fun _ => T⟩ : Env M 1).push C).push V
    let φ : UnarySchema 3 := {
      body := Formula.existsMem (.bound 3)
        (.conj (Formula.subset .newest (.bound 1)) (Formula.forallMem (.bound 3)
          (.imp (Formula.subset (.bound 1) .newest) (.mem .newest (.bound 3))))) }
    have hp f : φ.denote ρ f ↔ ∃ s, M.mem s T ∧ M.MemberSubset s f ∧
        ∀ g, M.mem g C → M.MemberSubset s g → M.mem g V := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
        Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
        Formula.satisfies_mem_iff]
      rfl
    obtain ⟨U, hU'⟩ := ZF.separation_exists_d hZF φ ρ B
    have hU f : M.mem f U ↔ M.mem f B ∧ ∃ s, M.mem s T ∧ M.MemberSubset s f ∧
        ∀ g, M.mem g C → M.MemberSubset s g → M.mem g V :=
      (hU' f).trans (and_congr_right fun _ => hp f)
    refine ⟨U, ⟨fun f hf => ((hU f).mp hf).1, fun f hf => ?_⟩, fun f => ?_⟩
    · obtain ⟨_, s, hs, hsf, hh⟩ := (hU f).mp hf
      exact ⟨s, ds_nodes_mono_l I hXY hT hS s hs, hsf, fun g hg hsg =>
        (hU g).mpr ⟨hg, s, hs, hsg, hh⟩⟩
    · exact ⟨fun hf => ⟨hV.1 f hf, (hU f).mpr ⟨hCB f (hV.1 f hf), hV.2 f hf⟩⟩,
        fun ⟨hf, hu⟩ => ((hU f).mp hu).2.elim fun s h => h.2.2 f hf h.2.1⟩
  · rintro ⟨U, hU, he⟩
    refine ⟨fun f hf => ((he f).mp hf).1, fun f hf => ?_⟩
    obtain ⟨hfC, hfU⟩ := (he f).mp hf
    obtain ⟨s, hs, hsf, hu⟩ := hU.2 f hfU
    obtain ⟨n, hn, hsn⟩ := (hS s).mp hs
    have hr := (ds_restrict_iff_l I hsn ((hB f).mp (hCB f hfC)).1).mpr hsf
    have hsY := hr.isSetFunctionFromTo ((hC f).mp hfC) (hω.transitive (ZF.modelsKP hZF) n hn)
    exact ⟨s, (hT s).mpr ⟨n, hn, hsY⟩, hsf, fun g hg hsg => (he g).mpr ⟨hg, hu g (hCB g hg) hsg⟩⟩

/-- 对实际二元字母表实例化子空间定理。 -/
theorem cantor_subspace_l (hZF : M.Models ZF) {ω D B C S T V}
    (hB : Baire_d I ω B) (hD : M.IsOrdinalTwo D) (hC : M.IsFunctionSpace I C ω D)
    (hS : Fseq_space_d I ω ω S) (hT : Fseq_space_d I ω D T) :
    Open_d T C V ↔ ∃ U, Open_d S B U ∧ ∀ f, M.mem f V ↔ M.mem f C ∧ M.mem f U :=
  ds_subspace_l I hZF hB.1 (hB.1.transitive (ZF.modelsKP hZF) D (ds_two_mem_l hZF.1 hB.1 hD)) hB.2 hC hS hT

/-- Cantor 点集与内部自然数幂集的等势由实际特征函数双射给出。 -/
theorem cantor_power_l (hZF : M.Models ZF) {ω C P} (hC : Cantor_d I ω C)
    (hP : M.IsPowerSetOf P ω) : M.Equinumerous I P C := by
  obtain ⟨_, D, hD, hC⟩ := hC
  obtain ⟨z, o, hzo, hd⟩ := ds_two_l hZF.1 hD
  exact ZF.equinumerous_powerSet_functionSpace hZF I hP hd hzo hC

end YesMetaZFC.SetTheory.Descriptive

/-! ## 距离柯西完备性与具体空间终点

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
  obtain ⟨m, hmn, hmk, hml⟩ := ds_tail_l hZF.1 (hω.isOrdinal (ZF.modelsKP hZF)) hk hll
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
