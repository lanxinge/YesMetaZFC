import YesMetaZFC.SetTheory.Descriptive.Dyadic

/-! # 首差坐标与规范有理数距离

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
  have hjω := hω.transitive hZF n hnω j hj
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
      · exact fun j x hj => ha j x ((hω.isOrdinal hZF).mem hi |>.transitive n hni j hj)
    · rcases (hω.isOrdinal hZF).wellOrder.linear.compare n hn i hi with e | hni | hin
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
  · rcases (hω.isOrdinal hZF).wellOrder.linear.compare n hn m hm with e | hnm | hmn
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
