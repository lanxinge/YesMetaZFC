import YesMetaZFC.SetTheory.Card.FiniteSequenceCountable
import YesMetaZFC.SetTheory.Ord.Arithmetic.Noncommutative

/-! # 模型内部的 Baire 与 Cantor 空间

空间成员是模型中的函数图，定义域为模型自身的 ω。有限列也沿同一个 ω
取长度；本层没有外部标准性、良基性或选择公理要求。
-/

namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- Baire 空间由全部内部自然数值序列组成。 -/
def Baire_d (ω B : M.Domain) : Prop := M.IsOmega ω ∧ M.IsFunctionSpace I B ω ω

/-- Cantor 空间的字母表是内部序数二，故不依赖另选的两个标签。 -/
def Cantor_d (ω C : M.Domain) : Prop :=
  M.IsOmega ω ∧ ∃ D, M.IsOrdinalTwo D ∧ M.IsFunctionSpace I C ω D

def baire_m {d} (ω B : Term d) : Formula 1 d :=
  .conj (Formula.isOmega ω) (Formula.isFunctionSpace 𝒞 B ω ω)
@[simp] theorem baire_free_l {d} (ω B : Term d)
    (hω : ω.freeSupport = []) (hB : B.freeSupport = []) :
    (baire_m (𝒞 := 𝒞) ω B).FreeClosed := by
  simp -implicitDefEqProofs [baire_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed, hω, hB]

def cantor_m {d} (ω C : Term d) : Formula 1 d := .conj (Formula.isOmega ω)
  (.existsE (.conj (.existsE (.conj (Formula.isOrdinalOne .newest)
    (Formula.isSuccessor (.bound 1) .newest)))
    (Formula.isFunctionSpace 𝒞 C.weaken ω.weaken .newest)))
@[simp] theorem cantor_free_l {d} (ω C : Term d)
    (hω : ω.freeSupport = []) (hC : C.freeSupport = []) :
    (cantor_m (𝒞 := 𝒞) ω C).FreeClosed := by
  simp -implicitDefEqProofs [cantor_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed, hω, hC]

@[prove_auto_norm semantic]
theorem baire_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B : Term d) :
    Formula.satisfies ρ (baire_m (𝒞 := 𝒞) ω B) ↔ Baire_d I (ω.eval ρ) (B.eval ρ) := by
  simp only [baire_m, Baire_d, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isFunctionSpace_iff I hE]

@[prove_auto_norm semantic]
theorem cantor_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω C : Term d) :
    Formula.satisfies ρ (cantor_m (𝒞 := 𝒞) ω C) ↔ Cantor_d I (ω.eval ρ) (C.eval ρ) := by
  simp only [cantor_m, Cantor_d, Structure.IsOrdinalTwo, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, Formula.satisfies_exists_iff, Formula.satisfies_isOrdinalOne_iff,
    Formula.satisfies_isSuccessor_iff, Formula.satisfies_isFunctionSpace_iff I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 固定定义域和字母表的内部函数空间唯一。 -/
theorem ds_space_unique_l (hE : Extensional M) {D X B C : M.Domain}
    (hB : M.IsFunctionSpace I B D X) (hC : M.IsFunctionSpace I C D X) : B = C :=
  hE.eq_of_same_members B C (fun f => (hB f).trans (hC f).symm)

/-- 扩大字母表保留原函数图，因而得到空间的字面包含。 -/
theorem ds_space_mono_l {D X Y B C : M.Domain} (hXY : M.MemberSubset X Y)
    (hB : M.IsFunctionSpace I B D X) (hC : M.IsFunctionSpace I C D Y) : M.MemberSubset B C := by
  intro f hf
  have h := (hB f).mp hf
  exact (hC f).mpr ⟨h.1, h.2.1, fun i hi => (h.2.2 i hi).elim fun x hx =>
    ⟨x, hXY x hx.1, hx.2⟩⟩

/-- 字母表包含保留全部内部有限列，包括非标准有限长度。 -/
theorem ds_nodes_mono_l {ω X Y S T : M.Domain} (hXY : M.MemberSubset X Y)
    (hS : Fseq_space_d I ω X S) (hT : Fseq_space_d I ω Y T) : M.MemberSubset S T := by
  intro s hs
  obtain ⟨n, hn, hf⟩ := (hS s).mp hs
  exact (hT s).mpr ⟨n, hn, hf.1, hf.2.1, fun i hi => (hf.2.2 i hi).elim fun x hx =>
    ⟨x, hXY x hx.1, hx.2⟩⟩

omit I in
/-- 序数二的两个成员及其不等性只需要外延性。 -/
theorem ds_two_l (hE : Extensional M) {D : M.Domain} (hD : M.IsOrdinalTwo D) :
    ∃ z o, z ≠ o ∧ (∀ x, M.mem x D ↔ x = z ∨ x = o) := by
  obtain ⟨o, ⟨z, hz, ho⟩, hD⟩ := hD
  have one x : M.mem x o ↔ x = z := by
    rw [ho x]
    exact ⟨fun h => h.elim (fun h => (hz x h).elim) (hE.eq_of_same_members _ _),
      fun h => Or.inr (h ▸ (fun _ => Iff.rfl))⟩
  refine ⟨z, o, fun h => hz z (h.symm ▸ ho.predecessor_mem), fun x => ?_⟩
  exact (hD x).trans (or_congr (one x)
    ⟨hE.eq_of_same_members _ _, fun h => h ▸ (fun _ => Iff.rfl)⟩)

omit I in
/-- 任意最小归纳集都包含内部序数二。 -/
theorem ds_two_mem_l (hE : Extensional M) {ω D : M.Domain}
    (hω : M.IsOmega ω) (hD : M.IsOrdinalTwo D) : M.mem D ω := by
  obtain ⟨o, ho, hD⟩ := hD
  obtain ⟨p, hp, hpω⟩ := hω.exists_ordinalOne_mem
  have e := Structure.IsOrdinalOne.eq hE ho hp
  subst p
  obtain ⟨s, hs, hsω⟩ := hω.1.2 o hpω
  exact Structure.SuccessorOf.eq hE hs hD ▸ hsω

theorem baire_unique_l (hE : Extensional M) {ω B C}
    (hB : Baire_d I ω B) (hC : Baire_d I ω C) : B = C := ds_space_unique_l I hE hB.2 hC.2

theorem cantor_unique_l (hE : Extensional M) {ω B C}
    (hB : Cantor_d I ω B) (hC : Cantor_d I ω C) : B = C := by
  obtain ⟨_, D, ⟨o, ho, hD⟩, hB⟩ := hB
  obtain ⟨_, E, ⟨p, hp, hE'⟩, hC⟩ := hC
  have e := Structure.IsOrdinalOne.eq hE ho hp
  subst p
  have e := Structure.SuccessorOf.eq hE hD hE'
  subst E
  exact ds_space_unique_l I hE hB hC

/-- Cantor 空间是 Baire 空间中取值于序数二的那些原函数图。 -/
theorem cantor_subset_baire_l (hZF : M.Models ZF) {ω B C}
    (hB : Baire_d I ω B) (hC : Cantor_d I ω C) : M.MemberSubset C B := by
  obtain ⟨hω, D, hD, hC⟩ := hC
  exact ds_space_mono_l I (hω.transitive hZF D (ds_two_mem_l hZF.1 hω hD)) hC hB.2

theorem baire_exists_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) : ∃ B, Baire_d I ω B := by
  obtain ⟨B, hB⟩ := ZF.exists_functionSpace hZF I ω ω
  exact ⟨B, hω, hB⟩

theorem cantor_exists_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) : ∃ C, Cantor_d I ω C := by
  obtain ⟨D, hD⟩ := KP.exists_ordinalTwo (ZF.modelsKP hZF)
  obtain ⟨C, hC⟩ := ZF.exists_functionSpace hZF I ω D
  exact ⟨C, hω, D, hD, hC⟩

/-- 同时构造两个空间及各自可数的全部内部有限列，调用者无需提供空间实例。 -/
theorem ds_spaces_l (hZF : M.Models ZF) : ∃ ω D B C S T,
    Baire_d I ω B ∧ M.IsOrdinalTwo D ∧ M.IsFunctionSpace I C ω D ∧
    Fseq_space_d I ω ω S ∧ M.CardinalLessOrEqual I S ω ∧
    Fseq_space_d I ω D T ∧ M.CardinalLessOrEqual I T ω := by
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨D, hD⟩ := KP.exists_ordinalTwo (ZF.modelsKP hZF)
  obtain ⟨B, hB⟩ := baire_exists_l I hZF hω
  obtain ⟨C, hC⟩ := ZF.exists_functionSpace hZF I ω D
  obtain ⟨e, he⟩ := ZF.exists_identityBijection hZF I ω
  obtain ⟨S, hS, hs⟩ := ZF.fseq_countable_space_l I hZF hω ⟨e, he.1⟩
  obtain ⟨f, hf⟩ := ZF.exists_inclusionInjection hZF I
    (hω.transitive hZF D (ds_two_mem_l hZF.1 hω hD))
  obtain ⟨T, hT, ht⟩ := ZF.fseq_countable_space_l I hZF hω ⟨f, hf⟩
  exact ⟨ω, D, B, C, S, T, hB, hD, hC, hS, hs, hT, ht⟩

end YesMetaZFC.SetTheory.Descriptive
