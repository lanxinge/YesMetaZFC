import YesMetaZFC.Model.Forcing.Domain
import YesMetaZFC.Model.SmallGraph.Choice
import YesMetaZFC.Model.SmallGraph.Infinity
import YesMetaZFC.Model.SetTheory.ProjectSemantics
import YesMetaZFC.SetTheory.Axioms.ZFC

/-! # 扩张中 ZFC 的基础公理

外延性、空集与基础公理只消费已实现的非空、传递解释像；无穷公理只另需 ω
属于该像。结论直接使用仓库原公理，不引入代替 ZFC 的新理论或保持性合同。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean SmallGraph SetTheory SetTheory.Definitional.Project
universe u v
variable {B : Type v} (N : Name_domain_l.{u, v} B) (U : B → Prop)

attribute [local simp] Formula.satisfies_mem_iff Formula.satisfies_neg_iff
  Formula.satisfies_conj_iff Formula.satisfies_disj_iff Formula.satisfies_imp_iff
  Formula.satisfies_iff_iff Formula.satisfies_forall_iff Formula.satisfies_exists_iff

theorem ext_empty_l : ∃ e : (ext_structure_l N U).Domain,
    ∀ z, ¬ (ext_structure_l N U).mem z e := by
  classical
  have h (x : (ext_structure_l N U).Domain) : ∃ e : (ext_structure_l N U).Domain,
      ∀ z, ¬ (ext_structure_l N U).mem z e := by
    induction x using (ext_wf_l N U).induction with
    | h x ih =>
      by_cases hx : ∃ z, (ext_structure_l N U).mem z x
      · obtain ⟨z, hz⟩ := hx
        exact ih z hz
      · exact ⟨x, fun z hz => hx ⟨z, hz⟩⟩
  obtain ⟨x⟩ := (ext_structure_l N U).nonempty
  exact h x

theorem ext_foundation_l (x : (ext_structure_l N U).Domain)
    (h : ∃ a, (ext_structure_l N U).mem a x) :
    ∃ a, (ext_structure_l N U).mem a x ∧
      ∀ z, (ext_structure_l N U).mem z x → ¬ (ext_structure_l N U).mem z a := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb, hm⟩ := SG_set.foundation x.1 ⟨a.1, ha⟩
  exact ⟨⟨b, ext_transitive_l N U x.2 hb⟩, hb, fun z hz => hm z.1 hz⟩

/-- 将实际 ω 的空元与后继见证保留在传递扩张内。 -/
theorem ext_infinity_l (hω : Ext_l N U SG_set.omega) :
    ∃ o : (ext_structure_l N U).Domain,
      (∃ e, (∀ z, ¬ (ext_structure_l N U).mem z e) ∧ (ext_structure_l N U).mem e o) ∧
      ∀ x, (ext_structure_l N U).mem x o → ∃ s,
        (∀ z, (ext_structure_l N U).mem z s ↔ (ext_structure_l N U).mem z x ∨ z = x) ∧
        (ext_structure_l N U).mem s o := by
  obtain ⟨⟨e, he, heω⟩, hs⟩ := SG_set.infinity.{u}
  refine ⟨⟨SG_set.omega, hω⟩, ⟨⟨e, ext_transitive_l N U hω heω⟩,
    fun z => he z.1, heω⟩, fun x hx => ?_⟩
  obtain ⟨s, hsz, hsω⟩ := hs x.1 hx
  refine ⟨⟨s, ext_transitive_l N U hω hsω⟩, fun z => ?_, hsω⟩
  exact (hsz z.1).trans (or_congr Iff.rfl ⟨fun h => Subtype.ext h, congrArg Subtype.val⟩)

/-- 三条原公理无需超滤子或完备布尔代数假设。 -/
theorem ext_zfc_base_l :
    (ext_structure_l N U).SatisfiesSentence Axioms.extensionality ∧
    (ext_structure_l N U).SatisfiesSentence Axioms.emptySet ∧
    (ext_structure_l N U).SatisfiesSentence Axioms.foundation := by
  refine ⟨?_, ?_, ?_⟩
  · rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simpa [Axioms.extensionality, Sentence.ofFormula,
      Formula.satisfies_extensionalEq_iff_eq (ext_extensional_l N U)] using
      (ext_extensional_l N U).eq_of_same_members
  · rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simpa [Axioms.emptySet, Sentence.ofFormula] using ext_empty_l N U
  · rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simpa [Axioms.foundation, Sentence.ofFormula] using ext_foundation_l N U

theorem ext_zfc_infinity_l (hω : Ext_l N U SG_set.omega) :
    (ext_structure_l N U).SatisfiesSentence Axioms.infinity := by
  rw [SetTheory.Structure.satisfiesSentence_iff]
  intro f
  simpa [Axioms.infinity, Sentence.ofFormula,
    Formula.satisfies_extensionalEq_iff_eq (ext_extensional_l N U)] using ext_infinity_l N U hω

end YesMetaZFC.Model.Forcing
