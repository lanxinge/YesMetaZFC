import YesMetaZFC.Model.Forcing.Internal.Extension.Separation
import YesMetaZFC.Model.Forcing.Internal.Extension.Collection
import YesMetaZFC.Model.Forcing.Internal.Extension.Power
import YesMetaZFC.Model.Forcing.Internal.Extension.Operations
import YesMetaZFC.Model.Forcing.Internal.Extension.Foundation

/-! # 地模型内部名称扩张保持原 ZF

逐条核验仓库原公理及全分离、全收集模式。扩张域是内部名称模泛型等价的商，
外部非良基地模型使用同一接口；基础公理由模型内部归纳和泛型性证明。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
include O hZF hU

attribute [local simp] Formula.satisfies_mem_iff Formula.satisfies_neg_iff
  Formula.satisfies_conj_iff Formula.satisfies_disj_iff Formula.satisfies_imp_iff
  Formula.satisfies_iff_iff Formula.satisfies_forall_iff Formula.satisfies_exists_iff
  Formula.satisfies_subset_iff

/-- 给出原 ZF 模型性，包括任意有限参数的原分离、收集模式。 -/
theorem preserves_zf_l : (E).Models ZF := by
  refine ⟨extension_ext_l O hZF hU, fun s hs => ?_⟩
  cases hs with
  | extensionality =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simpa [Axioms.extensionality, Sentence.ofFormula,
      Formula.satisfies_extensionalEq_iff_eq (extension_ext_l O hZF hU)] using
      (extension_ext_l O hZF hU).eq_of_same_members
  | emptySet =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
    obtain ⟨x, hx⟩ := name_value_l (R := R) (z := z) (U := U)
      (name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B e he)
    have h : ∃ x : (E).Domain, ∀ y, ¬ (E).mem y x := ⟨x, fun y hy => by
      obtain ⟨s, b, ⟨p, _, hp⟩, _⟩ := (qval_mem_l O hZF hU hx).mp hy
      exact he p hp⟩
    simpa [Axioms.emptySet, Sentence.ofFormula] using h
  | foundation =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simpa [Axioms.foundation, Sentence.ofFormula] using internal_foundation_l O hZF hU
  | pairing =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simp only [Axioms.pairing, Sentence.ofFormula, Formula.satisfies_forall_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_iff_iff, Formula.satisfies_disj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq (extension_ext_l O hZF hU),
      Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
    simpa only [extension_l] using internal_pair_l O hZF hU
  | union =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simpa [Axioms.union, Sentence.ofFormula, extension_l] using internal_union_l O hZF hU
  | powerSet =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simpa [Axioms.powerSet, Sentence.ofFormula, extension_l] using internal_power_l O hZF hU
  | infinity =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simp only [Axioms.infinity, Sentence.ofFormula, Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_iff_iff, Formula.satisfies_disj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq (extension_ext_l O hZF hU),
      Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
    simpa only [extension_l] using internal_infinity_l O hZF hU
  | separation φ =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    apply (Formula.satisfies_forallClosure_iff (ℳ := E) f (Axioms.Schema.separationCore φ)).mpr
    intro b
    apply (Axioms.Schema.separation_sat_iff_d _ φ).mpr
    simpa only [extension_l] using internal_separation_l O hZF hU φ (⟨b, f⟩ : Env E _)
  | collection φ =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    apply (Formula.satisfies_forallClosure_iff (ℳ := E) f (Axioms.Schema.collectionCore φ)).mpr
    intro b
    apply (Axioms.Schema.collection_sat_iff_d _ φ).mpr
    simpa only [extension_l] using internal_collection_l O hZF hU φ (⟨b, f⟩ : Env E _)

end YesMetaZFC.Model.Forcing.Internal
