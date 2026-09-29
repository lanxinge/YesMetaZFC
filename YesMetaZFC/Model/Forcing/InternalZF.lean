import YesMetaZFC.Model.Forcing.InternalSeparation
import YesMetaZFC.Model.Forcing.InternalCollection
import YesMetaZFC.Model.Forcing.InternalPower
import YesMetaZFC.Model.Forcing.InternalZFOperations
import YesMetaZFC.Model.Forcing.ZFCBase

/-! # 地模型内部名称扩张保持原 ZF

逐条核验仓库原公理及全分离、全收集模式。扩张域是全部内部名称的小图解释像，
不使用全宿主名称宇宙或预设的公理保持合同。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
  (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M) (hN : ∃ t, Name_d M B t)
local notation "N" => name_domain_l M hM hL B hN
local notation "E" => ext_structure_l N U
include O hZF hU

attribute [local simp] Formula.satisfies_mem_iff Formula.satisfies_neg_iff
  Formula.satisfies_conj_iff Formula.satisfies_disj_iff Formula.satisfies_imp_iff
  Formula.satisfies_iff_iff Formula.satisfies_forall_iff Formula.satisfies_exists_iff
  Formula.satisfies_subset_iff

/-- 给出原 ZF 模型性，包括任意有限参数的原分离、收集模式。 -/
theorem internal_models_zf_l : (E).Models ZF := by
  refine ⟨ext_extensional_l N U, fun s hs => ?_⟩
  cases hs with
  | extensionality => exact (ext_zfc_base_l N U).1
  | emptySet => exact (ext_zfc_base_l N U).2.1
  | foundation => exact (ext_zfc_base_l N U).2.2
  | pairing =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simp only [Axioms.pairing, Sentence.ofFormula, Formula.satisfies_forall_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_iff_iff, Formula.satisfies_disj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq (ext_extensional_l N U),
      Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
    simpa only [ext_structure_l] using internal_pair_l hZF hU hM hL hN
  | union =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simpa [Axioms.union, Sentence.ofFormula, ext_structure_l] using internal_union_l hZF hU hM hL hN
  | powerSet =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simpa [Axioms.powerSet, Sentence.ofFormula, ext_structure_l] using internal_power_l O hZF hU hM hL hN
  | infinity =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simp only [Axioms.infinity, Sentence.ofFormula, Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_iff_iff, Formula.satisfies_disj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq (ext_extensional_l N U),
      Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
    simpa only [ext_structure_l] using internal_infinity_l hZF hU hM hL hN
  | separation φ =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simp only [Axioms.Schema.separation, Sentence.forallClosure, Formula.satisfies_forallClosure_iff]
    intro b
    apply (Axioms.Schema.separation_sat_iff_d _ φ).mpr
    simpa only [ext_structure_l] using internal_separation_l O hZF hU hM hL hN φ (⟨b, f⟩ : Env E _)
  | collection φ =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simp only [Axioms.Schema.collection, Sentence.forallClosure, Formula.satisfies_forallClosure_iff]
    intro b
    apply (Axioms.Schema.collection_sat_iff_d _ φ).mpr
    simpa only [ext_structure_l] using internal_collection_l O hZF hU hM hL hN φ (⟨b, f⟩ : Env E _)

omit O hU in
theorem zf_name_exists_l : ∃ t, Name_d M B t := by
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  exact ⟨e, name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B e he⟩

/-- 地模型内部名称的实际解释扩张，非空性由原 ZF 的空名称自动提供。 -/
def extension_l (M : SetTheory.Structure.{u}) (hZF : M.Models ZF)
    (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M)
    (B : M.Domain) (U : M.Domain → Prop) : SetTheory.Structure.{v+1} :=
  ext_structure_l (name_domain_l M hM hL B (zf_name_exists_l (B := B) hZF)) U

/-- 一次调用取得全部原 ZF 公理及模式的保持。 -/
theorem preserves_zf_l : (extension_l M hZF hM hL B U).Models ZF :=
  internal_models_zf_l O hZF hU hM hL (zf_name_exists_l (B := B) hZF)

end YesMetaZFC.Model.Forcing.Internal
