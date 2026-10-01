import YesMetaZFC.SetTheory.Card.CountableUnion

/-! # 内部可数多值闭包

每个对象指定一个实际可数后继集合。幂集上的一步闭包由分离构造，沿模型的 ω
迭代并取并，得到包含任意可数种子的可数闭集。全过程使用内部函数图。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Cc_closed_d (F N : M.Domain) : Prop :=
  ∀ x Y, M.mem x N → M.PairMember I x Y F → M.MemberSubset Y N

def cc_closed_m (𝒞 : OrderedPairConvention) {n} (F N : Term n) : Formula 1 n :=
  Formula.forallMem N (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
    (Formula.subset .newest N.weaken.weaken)))
derive_free_closed cc_closed_m

theorem cc_closed_sat_l {n} (ρ : Env M n) (F N : Term n) :
    Formula.satisfies ρ (cc_closed_m 𝒞 F N) ↔ Cc_closed_d I (F.eval ρ) (N.eval ρ) := by
  simp only [cc_closed_m, Cc_closed_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_subset_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_one_push]
  exact ⟨fun h x Y hx => h x hx Y, fun h x hx Y => h x Y hx⟩

def Cc_step_d (F A C : M.Domain) : Prop :=
  ∀ y, M.mem y C ↔ M.mem y A ∨ ∃ x Y, M.mem x A ∧ M.PairMember I x Y F ∧ M.mem y Y

def cc_step_m (𝒞 : OrderedPairConvention) {n} (F A C : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest C.weaken) (.disj (.mem .newest A.weaken)
    (.existsE (.existsE (.conj (.mem (.bound 1) A.weaken.weaken.weaken)
      (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken.weaken) (.mem (.bound 2) .newest)))))))
derive_free_closed cc_step_m

theorem cc_step_sat_l {n} (ρ : Env M n) (F A C : Term n) :
    Formula.satisfies ρ (cc_step_m 𝒞 F A C) ↔ Cc_step_d I (F.eval ρ) (A.eval ρ) (C.eval ρ) := by
  simp only [cc_step_m, Cc_step_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

namespace ZFC
variable (hZFC : M.Models ZFC) {ω X P F} (hω : M.IsOmega ω)
    (hP : M.IsPowerSetOf P X) (hF : M.IsSetFunctionFromTo I F X P)
    (hval : ∀ x Y, M.PairMember I x Y F → M.CardinalLessOrEqual I Y ω)
include hZFC hω hP hF hval

omit hP in
/-- 一步闭包保持内部可数性。 -/
theorem cc_step_countable_l {A C} (hA : M.MemberSubset A X) (ha : M.CardinalLessOrEqual I A ω)
    (hC : Cc_step_d I F A C) : M.CardinalLessOrEqual I C ω := by
  let hZF := models_zf_l hZFC
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : BinarySchema 1 := {
    body := .disj (Formula.extensionalEq .newest (.bound 1)) (.existsE
      (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3)) (.mem (.bound 1) .newest))) }
  have hφ x y : φ.denote ρ x y ↔ y = x ∨ ∃ Y, M.PairMember I x Y F ∧ M.mem y Y := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff]
    rfl
  apply countable_cover_l I hZFC hω φ ρ ha
  · intro x hx D hD
    obtain ⟨Y, _, hxy⟩ := hF.2.2 x (hA x hx)
    obtain ⟨T, hT⟩ := KP.exists_insert (ZF.modelsKP hZF) Y x
    obtain ⟨f, hf⟩ := ZF.countable_insert_l I hZF hω (hval x Y hxy) hT
    obtain ⟨g, hg⟩ := ZF.exists_inclusionInjection hZF I (show M.MemberSubset D T from fun y hy => by
      rcases (hφ x y).mp ((hD y).mp hy).2 with he | ⟨Z, hxz, hyz⟩
      · exact (hT y).mpr (Or.inr he)
      · exact (hT y).mpr (Or.inl (hF.1.2 x Z Y hxz hxy ▸ hyz)))
    exact ZF.exists_compositionInjection hZF I hg hf
  · intro y hy
    rcases (hC y).mp hy with hy | ⟨x, Y, hx, hxy, hyY⟩
    · exact ⟨y, hy, (hφ y y).mpr (Or.inl rfl)⟩
    · exact ⟨x, hx, (hφ x y).mpr (Or.inr ⟨Y, hxy, hyY⟩)⟩

/-- 内部可数多值函数的可数闭包真实存在；种子与闭包都是原模型中的集合。 -/
theorem cc_hull_l {A} (hA : M.MemberSubset A X) (ha : M.CardinalLessOrEqual I A ω) : ∃ N,
    M.MemberSubset A N ∧ M.MemberSubset N X ∧ M.CardinalLessOrEqual I N ω ∧ Cc_closed_d I F N := by
  let hZF := models_zf_l hZFC
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : BinarySchema 1 := { body := cc_step_m 𝒞 (.bound 2) (.bound 1) .newest }
  have hφ C D : φ.denote ρ C D ↔ Cc_step_d I F C D := cc_step_sat_l I _ _ _ _
  have total C (hCP : M.mem C P) : ∃ D, φ.denote ρ C D := by
    let η := ρ.push C
    let ψ : UnarySchema 2 := {
      body := .disj (.mem .newest (.bound 1)) (.existsE (.existsE
        (.conj (.mem (.bound 1) (.bound 3)) (.conj
          (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4)) (.mem (.bound 2) .newest))))) }
    obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF ψ η X
    refine ⟨D, (hφ C D).mpr (fun y => ?_)⟩
    rw [hD y]
    simp only [ψ, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I]
    change (M.mem y X ∧ (M.mem y C ∨ ∃ x Y, M.mem x C ∧ M.PairMember I x Y F ∧ M.mem y Y)) ↔ _
    exact ⟨And.right, fun h => ⟨h.elim ((hP C).mp hCP y)
      (fun ⟨x, Y, _, hxy, hy⟩ => (hP Y).mp (hF.output_mem_of_pairMember hxy) y hy), h⟩⟩
  obtain ⟨G, hG, hg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := P) (target := P) total
    (fun C _ D E hD hE => hZF.1.eq_of_same_members D E (fun y => ((hφ C D).mp hD y).trans ((hφ C E).mp hE y).symm))
    (fun C D hC hD => (hP D).mpr (fun y hy => ((hφ C D).mp hD y).mp hy |>.elim ((hP C).mp hC y)
      (fun ⟨x, Y, _, hxy, hyY⟩ => (hP Y).mp (hF.output_mem_of_pairMember hxy) y hyY)))
  obtain ⟨Q, hQ, hz, hs⟩ := iterate_l I hZF hω hG ((hP A).mpr hA)
  have step {i j C D} (hji : M.SuccessorOf j i) (hi : M.PairMember I i C Q) (hj : M.PairMember I j D Q) : Cc_step_d I F C D :=
    (hφ C D).mp ((hg C D).mp (hs i j C D hji hi hj)).2
  let η : Env M 2 := (⟨fun _ => Q, fun _ => Q⟩ : Env M 1).push ω
  let ψ : UnarySchema 2 := {
    body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))
      (Formula.cardinalLessOrEqual 𝒞 .newest (.bound 2))) }
  have hψ i : ψ.denote η i ↔ ∀ C, M.PairMember I i C Q → M.CardinalLessOrEqual I C ω := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_cardinalLessOrEqual_iff I hZF.1]
    rfl
  have count : ∀ i, M.mem i ω → ∀ C, M.PairMember I i C Q → M.CardinalLessOrEqual I C ω := by
    apply hω.induction (fun i => ∀ C, M.PairMember I i C Q → M.CardinalLessOrEqual I C ω)
    · obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF ψ η ω
      exact ⟨D, fun i => (hD i).trans (and_congr_right fun _ => hψ i)⟩
    · intro e he C hC
      exact hQ.1.2 e A C (hz e he) hC ▸ ha
    · intro i hi ih j hji D hj
      obtain ⟨C, hC, hiC⟩ := hQ.2.2 i hi
      exact cc_step_countable_l I hZFC hω hF hval ((hP C).mp hC) (ih C hiC) (step hji hiC hj)
  obtain ⟨Y, hY⟩ := ZF.exists_range_of_setFunction hZF I hQ.1 hQ.2.1
  obtain ⟨N, hN⟩ := KP.exists_union (ZF.modelsKP hZF) Y
  have hQY : M.IsSetFunctionFromTo I Q ω Y := ⟨hQ.1, hQ.2.1, fun i hi => by
    obtain ⟨C, _, hC⟩ := hQ.2.2 i hi
    exact ⟨C, (hY C).mpr ⟨i, hC⟩, hC⟩⟩
  have hy : M.CardinalLessOrEqual I Y ω := surjection_bound_l I hZFC hQY (fun C hC => by
    obtain ⟨i, hi⟩ := (hY C).mp hC
    exact ⟨i, hQ.input_mem_of_pairMember hi, hi⟩)
  obtain ⟨e, he, _⟩ := hω.1.1
  refine ⟨N, fun x hx => (hN x).mpr ⟨A, (hY A).mpr ⟨e, hz e he⟩, hx⟩, ?_,
    countable_union_l I hZFC hω hy hN (fun C hC => ?_), ?_⟩
  · intro x hx
    obtain ⟨C, hC, hxC⟩ := (hN x).mp hx
    obtain ⟨i, hi⟩ := (hY C).mp hC
    exact (hP C).mp (hQ.output_mem_of_pairMember hi) x hxC
  · obtain ⟨i, hi⟩ := (hY C).mp hC
    exact count i (hQ.input_mem_of_pairMember hi) C hi
  · intro x C hx hxC y hyC
    obtain ⟨D, hD, hxD⟩ := (hN x).mp hx
    obtain ⟨i, hi⟩ := (hY D).mp hD
    obtain ⟨j, hji, hj⟩ := hω.1.2 i (hQ.input_mem_of_pairMember hi)
    obtain ⟨E, _, hjE⟩ := hQ.2.2 j hj
    exact (hN y).mpr ⟨E, (hY E).mpr ⟨j, hjE⟩, (step hji hi hjE y).mpr (Or.inr ⟨x, C, hxD, hxC, hyC⟩)⟩

end ZFC
end YesMetaZFC.SetTheory
