import YesMetaZFC.SetTheory.InnerModel.Relative.Schemas

/-! # 任意传递基集上的 Jensen 并类满足原 ZF -/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}} (S : M.Domain) (hZF : M.Models ZF) (hS : M.TransitiveSet S)

include hS

theorem la_model_zf_l : (la_model_l S (ZF.models_kpi_l hZF)).Models ZF := by
  let hM := ZF.models_kpi_l hZF
  let N := la_model_l S hM
  have hE := la_model_ext_l S (ZF.models_kpi_l hZF) hS
  have same (x y : N.Domain) : N.SameMembers x y ↔ x.val = y.val :=
    ⟨fun h => congrArg Subtype.val (hE.eq_of_same_members x y h),
      fun h => (show x = y from Subtype.ext h) ▸ (fun _ => Iff.rfl)⟩
  refine ⟨hE, fun s hs => ?_⟩
  rw [Structure.satisfiesSentence_iff]
  intro f
  cases hs with
  | extensionality =>
    simp only [Axioms.extensionality, Sentence.ofFormula, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_extensionalEq_iff_eq hE]
    exact hE.eq_of_same_members
  | emptySet =>
    obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
    exact (Axioms.satisfies_emptySet_iff f).mpr
      ⟨⟨e, la_ordinal_l S (ZF.models_kpi_l hZF) hS (Structure.IsOrdinal.of_no_members he)⟩, fun z => he z.val⟩
  | pairing =>
    apply (Axioms.satisfies_pairing_iff f).mpr
    intro x y
    obtain ⟨p, hp⟩ := KP.exists_pair (ZF.modelsKP hZF) x.val y.val
    exact ⟨⟨p, la_closed_l S (ZF.models_kpi_l hZF) .pair x.property y.property y.property hp⟩,
      fun z => (hp z.val).trans (or_congr (same z x).symm (same z y).symm)⟩
  | union =>
    apply (Axioms.satisfies_union_iff f).mpr
    intro x
    obtain ⟨y, hy⟩ := KP.exists_union (ZF.modelsKP hZF) x.val
    refine ⟨⟨y, la_closed_l S (ZF.models_kpi_l hZF) .union x.property x.property x.property hy⟩, fun z => (hy z.val).trans ?_⟩
    exact ⟨fun ⟨a, ha, hz⟩ => ⟨⟨a, la_transitive_l S hM hS x.property ha⟩, ha, hz⟩,
      fun ⟨a, ha, hz⟩ => ⟨a.val, ha, hz⟩⟩
  | powerSet => exact (Axioms.satisfies_powerSet_iff f).mpr (la_model_power_l S hZF hS)
  | infinity =>
    apply (Axioms.satisfies_infinity_iff f).mpr
    obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
    have hL := la_ordinal_l S (ZF.models_kpi_l hZF) hS (hω.isOrdinal hZF)
    refine ⟨⟨ω, hL⟩, ?_, fun x hx => ?_⟩
    · obtain ⟨e, he, heω⟩ := hω.1.1
      exact ⟨⟨e, la_transitive_l S hM hS hL heω⟩, fun z => he z.val, heω⟩
    · obtain ⟨s, hs, hsω⟩ := hω.1.2 x.val hx
      refine ⟨⟨s, la_transitive_l S hM hS hL hsω⟩, fun z => (hs z.val).trans (or_congr_right ?_), hsω⟩
      exact ⟨fun h v => h v.val, fun h => (same z x).mp h ▸ (fun _ => Iff.rfl)⟩
  | foundation =>
    apply (Axioms.foundation_sat_iff_d f).mpr
    intro x hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨a, ha, hm⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) ⟨z.val, hz⟩
    exact ⟨⟨a, la_transitive_l S hM hS x.property ha⟩, ha, fun z hz => hm z.val hz⟩
  | separation φ =>
    apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.separationCore φ)).mpr
    intro b
    exact (Axioms.Schema.separation_sat_iff_d ⟨b, f⟩ φ).mpr (la_full_separation_l S hZF hS φ ⟨b, f⟩)
  | collection φ =>
    apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.collectionCore φ)).mpr
    intro b
    exact (Axioms.Schema.collection_sat_iff_d ⟨b, f⟩ φ).mpr (la_full_collection_l S hZF hS φ ⟨b, f⟩)

end YesMetaZFC.SetTheory.InnerModel.Relative
