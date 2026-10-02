import YesMetaZFC.SetTheory.Card.CountableUnion

/-! # 内部可数子集上的闭无界集

闭性消费沿内部 ω 编码的递增序列，所有成员、并与可数性均是模型中的实际集合。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Cc_union_d (f N : M.Domain) : Prop :=
  ∀ x, M.mem x N ↔ ∃ i A, M.PairMember I i A f ∧ M.mem x A

def cc_union_m (𝒞 : OrderedPairConvention) {n} (f N : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest N.weaken) (.existsE (.existsE
    (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest f.weaken.weaken.weaken) (.mem (.bound 2) .newest)))))
derive_free_closed cc_union_m

def Cc_increasing_d (f : M.Domain) : Prop := ∀ i j A B,
  M.mem i j → M.PairMember I i A f → M.PairMember I j B f → M.MemberSubset A B

def cc_increasing_m (𝒞 : OrderedPairConvention) {n} (f : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 3) (.bound 2))
    (.imp (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) f.weaken.weaken.weaken.weaken)
      (.imp (Formula.orderedPairMem 𝒞 (.bound 2) .newest f.weaken.weaken.weaken.weaken)
        (Formula.subset (.bound 1) .newest)))))))
derive_free_closed cc_increasing_m

structure Cc_club_d (ω X C : M.Domain) : Prop where
  members : ∀ N, M.mem N C → M.MemberSubset N X ∧ M.CardinalLessOrEqual I N ω
  unbounded : ∀ A, M.MemberSubset A X → M.CardinalLessOrEqual I A ω → ∃ N, M.mem N C ∧ M.MemberSubset A N
  closed : ∀ f N, M.IsSetFunctionFromTo I f ω C → Cc_increasing_d I f → Cc_union_d I f N → M.mem N C

def cc_club_m (𝒞 : OrderedPairConvention) {n} (ω X C : Term n) : Formula 1 n :=
  .conj (Formula.forallMem C (.conj (Formula.subset .newest X.weaken) (Formula.cardinalLessOrEqual 𝒞 .newest ω.weaken)))
    (.conj (.forallE (.imp (Formula.subset .newest X.weaken)
      (.imp (Formula.cardinalLessOrEqual 𝒞 .newest ω.weaken) (.existsE (.conj (.mem .newest C.weaken.weaken)
        (Formula.subset (.bound 1) .newest))))))
      (.forallE (.forallE (.imp (Formula.isFunctionFromTo 𝒞 (.bound 1) ω.weaken.weaken C.weaken.weaken)
        (.imp (cc_increasing_m 𝒞 (.bound 1)) (.imp (cc_union_m 𝒞 (.bound 1) .newest) (.mem .newest C.weaken.weaken)))))))
derive_free_closed cc_club_m

theorem cc_union_sat_l {n} (ρ : Env M n) (f N : Term n) :
    Formula.satisfies ρ (cc_union_m 𝒞 f N) ↔ Cc_union_d I (f.eval ρ) (N.eval ρ) := by
  simp only [cc_union_m, Cc_union_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

theorem cc_increasing_sat_l {n} (ρ : Env M n) (f : Term n) :
    Formula.satisfies ρ (cc_increasing_m 𝒞 f) ↔ Cc_increasing_d I (f.eval ρ) := by
  simp only [cc_increasing_m, Cc_increasing_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
  rfl

theorem cc_club_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω X C : Term n) :
    Formula.satisfies ρ (cc_club_m 𝒞 ω X C) ↔ Cc_club_d I (ω.eval ρ) (X.eval ρ) (C.eval ρ) := by
  simp only [cc_club_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_cardinalLessOrEqual_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    cc_increasing_sat_l I, cc_union_sat_l I, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.members, h.unbounded, h.closed⟩⟩

/-- 一条内部 ω 序列的值均为 κ 小时，其实际并为 κ 小。 -/
theorem ZFC.cc_union_bound_l (hZFC : M.Models ZFC) {ω κ X f N} (hω : M.IsOmega ω)
    (hκ : M.IsInfiniteCardinal I ω κ)
    (hf : M.IsSetFunctionFromTo I f ω X) (hu : Cc_union_d I f N)
    (hc : ∀ A, M.mem A X → M.CardinalLessOrEqual I A κ) : M.CardinalLessOrEqual I N κ := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨Y, hY⟩ := ZF.exists_range_of_setFunction hZF I hf.1 hf.2.1
  have hfY : M.IsSetFunctionFromTo I f ω Y := ⟨hf.1, hf.2.1, fun i hi => by
    obtain ⟨A, _, hiA⟩ := hf.2.2 i hi
    exact ⟨A, (hY A).mpr ⟨i, hiA⟩, hiA⟩⟩
  obtain ⟨G, hG⟩ := ZFC.surjection_bound_l I hZFC hfY (fun A hA => by
    obtain ⟨i, hi⟩ := (hY A).mp hA
    exact ⟨i, hf.input_mem_of_pairMember hi, hi⟩)
  obtain ⟨H, hH⟩ := hκ.2
  apply ZFC.infinite_union_l I hZFC hω hκ (ZF.exists_compositionInjection hZF I hG hH)
  · intro x
    exact (hu x).trans ⟨fun ⟨i, A, hi, hx⟩ => ⟨A, (hY A).mpr ⟨i, hi⟩, hx⟩,
      fun ⟨A, hA, hx⟩ => (hY A).mp hA |>.elim fun i hi => ⟨i, A, hi, hx⟩⟩
  · intro A hA
    obtain ⟨i, hi⟩ := (hY A).mp hA
    exact hc A (hf.output_mem_of_pairMember hi)

/-- 一张内部可数序列的值均可数时，其实际并可数。 -/
theorem ZFC.cc_union_countable_l (hZFC : M.Models ZFC) {ω X f N} (hω : M.IsOmega ω)
    (hf : M.IsSetFunctionFromTo I f ω X) (hu : Cc_union_d I f N)
    (hc : ∀ A, M.mem A X → M.CardinalLessOrEqual I A ω) : M.CardinalLessOrEqual I N ω := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨F, hF⟩ := ZF.exists_identityBijection hZF I ω
  exact ZFC.cc_union_bound_l I hZFC hω ⟨ZF.omega_cardinal_l I hZF hω, F, hF.1⟩ hf hu hc

/-- 全部内部可数子集组成实际 club，供闭包构造直接使用。 -/
theorem ZFC.cc_all_l (hZFC : M.Models ZFC) {ω} (hω : M.IsOmega ω) (X : M.Domain) :
    ∃ C, Cc_club_d I ω X C ∧
      ∀ N, M.mem N C ↔ M.MemberSubset N X ∧ M.CardinalLessOrEqual I N ω := by
  let hZF := models_zf_l hZFC
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF X
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  let φ : UnarySchema 1 := { body := Formula.cardinalLessOrEqual 𝒞 .newest (.bound 1) }
  obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ P
  have hc N : M.mem N C ↔ M.MemberSubset N X ∧ M.CardinalLessOrEqual I N ω :=
    (hC N).trans (and_congr (hP N) (Formula.satisfies_cardinalLessOrEqual_iff I hZF.1 _ _ _))
  refine ⟨C, ⟨fun N hN => (hc N).mp hN,
    fun A hA ha => ⟨A, (hc A).mpr ⟨hA, ha⟩, fun _ h => h⟩, ?_⟩, hc⟩
  intro f N hf _ hu
  refine (hc N).mpr ⟨?_, cc_union_countable_l I hZFC hω hf hu (fun A hA => ((hc A).mp hA).2)⟩
  intro x hx
  obtain ⟨i, A, hi, hx⟩ := (hu x).mp hx
  exact ((hc A).mp (hf.output_mem_of_pairMember hi)).1 x hx

end YesMetaZFC.SetTheory
