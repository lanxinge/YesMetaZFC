import YesMetaZFC.SetTheory.InnerModel.HOD.Schemas

/-! # HOD[A] 与 HOD(A) 满足原 ZF

同一传递类解释逐项验证原公理；全分离、全收集消费任意生产公式模式。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem ha_model_zf_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) : (ha_model_l hZF k A).Models ZF := by
  let N := ha_model_l hZF k A
  have hE := ha_model_ext_l hZF k A
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
      ⟨⟨e, ha_ordinal_l hZF k A (Structure.IsOrdinal.of_no_members he)⟩, fun z => he z.val⟩
  | pairing =>
    apply (Axioms.satisfies_pairing_iff f).mpr
    intro x y
    obtain ⟨p, hp, hP⟩ := ha_pair_l hZF x.property y.property
    exact ⟨⟨p, hp⟩, fun z => (hP z.val).trans (or_congr (same z x).symm (same z y).symm)⟩
  | union =>
    apply (Axioms.satisfies_union_iff f).mpr
    intro X
    obtain ⟨U, hu, hU⟩ := ha_union_l hZF X.property
    refine ⟨⟨U, hu⟩, fun z => (hU z.val).trans ?_⟩
    exact ⟨fun ⟨y, hy, hz⟩ => ⟨⟨y, ha_trans_l X.property hy⟩, hy, hz⟩, fun ⟨y, hy, hz⟩ => ⟨y.val, hy, hz⟩⟩
  | powerSet =>
    apply (Axioms.satisfies_powerSet_iff f).mpr
    intro X
    obtain ⟨P, hp, hP⟩ := ha_power_l hZF X.property
    refine ⟨⟨P, hp⟩, fun z => (hP z.val).trans ?_⟩
    exact ⟨fun h y hy => h.1 y.val hy, fun h =>
      ⟨fun y hy => h ⟨y, ha_trans_l z.property hy⟩ hy, z.property⟩⟩
  | infinity =>
    apply (Axioms.satisfies_infinity_iff f).mpr
    obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
    have hH := ha_ordinal_l hZF k A (hω.isOrdinal hZF)
    refine ⟨⟨ω, hH⟩, ?_, fun x hx => ?_⟩
    · obtain ⟨e, he, heω⟩ := hω.1.1
      exact ⟨⟨e, ha_trans_l hH heω⟩, fun z => he z.val, heω⟩
    · obtain ⟨s, hs, hsω⟩ := hω.1.2 x.val hx
      refine ⟨⟨s, ha_trans_l hH hsω⟩, fun z => (hs z.val).trans (or_congr_right ?_), hsω⟩
      exact ⟨fun h v => h v.val, fun h => (same z x).mp h ▸ (fun _ => Iff.rfl)⟩
  | foundation =>
    apply (Axioms.foundation_sat_iff_d f).mpr
    intro X hn
    obtain ⟨z, hz⟩ := hn
    obtain ⟨x, hx, hm⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) ⟨z.val, hz⟩
    exact ⟨⟨x, ha_trans_l X.property hx⟩, hx, fun y hy => hm y.val hy⟩
  | separation φ =>
    apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.separationCore φ)).mpr
    intro b
    exact (Axioms.Schema.separation_sat_iff_d ⟨b, f⟩ φ).mpr (ha_model_separation_l hZF k A φ ⟨b, f⟩)
  | collection φ =>
    apply (Formula.satisfies_forallClosure_iff f (Axioms.Schema.collectionCore φ)).mpr
    intro b
    exact (Axioms.Schema.collection_sat_iff_d ⟨b, f⟩ φ).mpr (ha_model_collection_l hZF k A φ ⟨b, f⟩)

abbrev hb_model_l (hZF : M.Models ZF) (A : M.Domain) := ha_model_l hZF false A
abbrev hp_model_l (hZF : M.Models ZF) (A : M.Domain) := ha_model_l hZF true A

theorem hb_model_zf_l (hZF : M.Models ZF) (A : M.Domain) : (hb_model_l hZF A).Models ZF := ha_model_zf_l hZF false A
theorem hp_model_zf_l (hZF : M.Models ZF) (A : M.Domain) : (hp_model_l hZF A).Models ZF := ha_model_zf_l hZF true A

end YesMetaZFC.SetTheory.InnerModel
