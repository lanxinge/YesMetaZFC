import YesMetaZFC.SetTheory.Descriptive.Topology
import YesMetaZFC.Model.SetTheory.Internal.SupportSyntax

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
  obtain ⟨m, hm, hmk, hml⟩ := ds_tail_l hZF.1 (hω.isOrdinal hZF) hk hl
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
  have hi := hω.transitive hZF n hn i hin
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
