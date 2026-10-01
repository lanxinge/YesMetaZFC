import YesMetaZFC.Model.Forcing.Iteration.Condition.Support
import YesMetaZFC.SetTheory.Card.CountableUnion

/-! # 内部可数条件族的支撑并

实际函数图与值域把条件族的可数性传给支撑集合族，再由原 ZFC 可数并定理计数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

/-- 可数条件族的可数坐标并；各支撑只需可数。 -/
theorem row_countable_coords_l (hZFC : M.Models ZFC) {ω J} (hω : M.IsOmega ω)
    (hJ : M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) J ω)
    (hS : ∀ p, M.mem p J → Row_supp_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) true ω p) : ∃ C,
    (∀ i, M.mem i C ↔ ∃ p, M.mem p J ∧ ∃ s, Entry_d M i s p) ∧
    M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) C ω := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let φ : BinarySchema 0 := { body := coord_m (.bound 1) .newest }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => J⟩
  have hφ p D : φ.denote ρ p D ↔ Coord_d M p D := coord_sat_l M hZF.1 _ _ _
  have total p (_ : M.mem p J) : ∃ D, φ.denote ρ p D := by
    obtain ⟨D, hD⟩ := coord_exists_l M hZF p
    exact ⟨D, (hφ p D).mpr hD⟩
  have unique p (_ : M.mem p J) D E (hD : φ.denote ρ p D) (hE : φ.denote ρ p E) : D = E :=
    coord_unique_l M hZF.1 ((hφ p D).mp hD) ((hφ p E).mp hE)
  obtain ⟨X, hX⟩ := ZF.exists_functionalImageOn hZF φ ρ J total unique
  obtain ⟨F, hF, hFF⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun p D hp hD => (hX D).mpr ⟨p, hp, hD⟩)
  obtain ⟨f, hf⟩ := ZFC.surjection_bound_l I hZFC hF (by
    intro D hD
    obtain ⟨p, hp, hpd⟩ := (hX D).mp hD
    exact ⟨p, hp, (hFF p D).mpr ⟨hp, hpd⟩⟩)
  obtain ⟨g, hg⟩ := hJ
  obtain ⟨C, hC⟩ := KP.exists_union (ZF.modelsKP hZF) X
  refine ⟨C, fun i => ?_, ZFC.countable_union_l I hZFC hω
    (ZF.exists_compositionInjection hZF I hf hg) hC (fun D hD => ?_)⟩
  · constructor
    · rintro hi
      obtain ⟨D, hD, hiD⟩ := (hC i).mp hi
      obtain ⟨p, hp, hpd⟩ := (hX D).mp hD
      exact ⟨p, hp, ((hφ p D).mp hpd i).mp hiD⟩
    · rintro ⟨p, hp, hi⟩
      obtain ⟨D, hD⟩ := total p hp
      exact (hC i).mpr ⟨D, (hX D).mpr ⟨p, hp, hD⟩, ((hφ p D).mp hD i).mpr hi⟩
  · obtain ⟨p, hp, hpd⟩ := (hX D).mp hD
    obtain ⟨E, hE, he⟩ := hS p hp
    exact coord_unique_l M hZF.1 hE ((hφ p D).mp hpd) ▸ he

end YesMetaZFC.Model.Forcing.Internal
