import YesMetaZFC.SetTheory.Ord.Natural

/-! # 模型内部的成员归纳

沿模型自己的 ω 递归取并，得到包含给定对象的传递集。对实际公式分离反例，
再使用基础公理；全过程不要求模型的成员关系在宿主中良基。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable (M : Structure.{u})

/-- 只对对象语言的实际公式授予归纳，不包含任意外部谓词。 -/
def Mem_ind_d : Prop := ∀ {n} (φ : UnarySchema n) (ρ : Env M n),
  (∀ x, (∀ y, M.mem y x → φ.denote ρ y) → φ.denote ρ x) → ∀ x, φ.denote ρ x

private def hull_step_m (C : OrderedPairConvention) {n} (x F v : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest v.weaken) (.disj (Formula.extensionalEq .newest x.weaken)
    (.existsE (.existsE (.existsE (.conj
      (Formula.orderedPairMem C (.bound 2) (.bound 1) F.weaken.weaken.weaken.weaken)
      (.conj (.mem .newest (.bound 1)) (.mem (.bound 3) .newest))))))))

derive_free_closed hull_step_m

private def Hull_step_d {C : OrderedPairConvention} (I : C.Interpretation M)
    (x F v : M.Domain) : Prop :=
  ∀ z, M.mem z v ↔ z = x ∨ ∃ i t y, M.PairMember I i t F ∧ M.mem y t ∧ M.mem z y

private theorem hull_step_sat_l {C : OrderedPairConvention} (I : C.Interpretation M)
    (hE : Extensional M) {n} (ρ : Env M n) (x F v : Term n) :
    Formula.satisfies ρ (hull_step_m C x F v) ↔ Hull_step_d M I (x.eval ρ) (F.eval ρ) (v.eval ρ) := by
  simp only [hull_step_m, Hull_step_d, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push,
    Term.eval_bound_three_push]

/-- 传递包络由内部递归序列实际构造，允许模型内部有非标准自然数。 -/
theorem ZF.mem_hull_l (hZF : M.Models ZF) {C : OrderedPairConvention}
    (I : C.Interpretation M) (x : M.Domain) :
    ∃ S, M.mem x S ∧ M.TransitiveSet S := by
  let ρ : Env M 1 := ⟨fun _ => x, fun _ => x⟩
  let φ : BinarySchema 1 := { body := hull_step_m C (.bound 2) (.bound 1) (.bound 0) }
  have hφ F v : φ.denote ρ F v ↔ Hull_step_d M I x F v :=
    hull_step_sat_l M I hZF.1 ((ρ.push F).push v) (.bound 2) (.bound 1) (.bound 0)
  have ho : M.IsClassFunctionOnTransfiniteSequences I (φ.denote ρ) := by
    rintro F ⟨a, ha⟩
    obtain ⟨R, hR⟩ := ZF.exists_range_of_setFunction hZF I ha.2.1 ha.2.2
    obtain ⟨S, hS⟩ := KP.exists_union (ZF.modelsKP hZF) R
    obtain ⟨T, hT⟩ := KP.exists_union (ZF.modelsKP hZF) S
    obtain ⟨v, hv⟩ := KP.exists_insert (ZF.modelsKP hZF) T x
    have h : Hull_step_d M I x F v := by
      intro z
      rw [hv z]
      constructor
      · rintro (hz | hz)
        · obtain ⟨y, hy, hz⟩ := (hT z).mp hz
          obtain ⟨t, ht, hy⟩ := (hS y).mp hy
          obtain ⟨i, hi⟩ := (hR t).mp ht
          exact Or.inr ⟨i, t, y, hi, hy, hz⟩
        · exact Or.inl hz
      · rintro (hz | ⟨i, t, y, hi, hy, hz⟩)
        · exact Or.inr hz
        · exact Or.inl ((hT z).mpr ⟨y, (hS y).mpr ⟨t, (hR t).mpr ⟨i, hi⟩, hy⟩, hz⟩)
    exact ⟨v, (hφ F v).mpr h, fun w hw =>
      hZF.1.eq_of_same_members w v (fun z => ((hφ F w).mp hw z).trans (h z).symm)⟩
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨F, hF⟩ := ZF.recursiveSequence_exists hZF I ρ φ ho (hω.isOrdinal hZF)
  obtain ⟨R, hR⟩ := ZF.exists_range_of_setFunction hZF I hF.1.2.1 hF.1.2.2
  obtain ⟨S, hS⟩ := KP.exists_union (ZF.modelsKP hZF) R
  have hs z : M.mem z S ↔ ∃ i t, M.PairMember I i t F ∧ M.mem z t := by
    constructor
    · intro hz
      obtain ⟨t, ht, hz⟩ := (hS z).mp hz
      obtain ⟨i, hi⟩ := (hR t).mp ht
      exact ⟨i, t, hi, hz⟩
    · rintro ⟨i, t, hi, hz⟩
      exact (hS z).mpr ⟨t, (hR t).mpr ⟨i, hi⟩, hz⟩
  refine ⟨S, ?_, ?_⟩
  · obtain ⟨i, _, hi⟩ := hω.1.1
    obtain ⟨t, ht⟩ := (hF.1.2.2 i).mp hi
    obtain ⟨P, _, hp⟩ := hF.2 i hi t ht
    exact (hs x).mpr ⟨i, t, ht, ((hφ P t).mp hp x).mpr (Or.inl rfl)⟩
  · intro z hz y hy
    obtain ⟨i, t, hi, hz⟩ := (hs z).mp hz
    have hiω := (hF.1.2.2 i).mpr ⟨t, hi⟩
    obtain ⟨j, hj, hjω⟩ := hω.1.2 i hiω
    obtain ⟨v, hv⟩ := (hF.1.2.2 j).mp hjω
    obtain ⟨P, hp, hstep⟩ := hF.2 j hjω v hv
    exact (hs y).mpr ⟨j, v, hv, ((hφ P v).mp hstep y).mpr
      (Or.inr ⟨i, t, z, (hp.2 i t).mpr ⟨hj.predecessor_mem, hi⟩, hz, hy⟩)⟩

/-- 原 ZF 模型自动满足实际公式的成员归纳模式。 -/
theorem ZF.mem_ind_l (hZF : M.Models ZF) {C : OrderedPairConvention}
    (I : C.Interpretation M) : Mem_ind_d M := by
  intro n φ ρ h x
  classical
  obtain ⟨S, hx, hS⟩ := ZF.mem_hull_l M hZF I x
  obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF φ.neg ρ S
  have ht y : M.mem y T ↔ M.mem y S ∧ ¬ φ.denote ρ y := by
    simpa only [UnarySchema.neg, Formula.satisfies_neg_iff, UnarySchema.denote] using hT y
  apply Classical.byContradiction
  intro hn
  obtain ⟨y, hy, hm⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) ⟨x, (ht x).mpr ⟨hx, hn⟩⟩
  apply ((ht y).mp hy).2
  apply h y
  intro z hz
  apply Classical.byContradiction
  intro hnz
  exact hm z ((ht z).mpr ⟨hS y ((ht y).mp hy).1 z hz, hnz⟩) hz

end YesMetaZFC.SetTheory
