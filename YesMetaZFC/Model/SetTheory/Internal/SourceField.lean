import YesMetaZFC.Model.SetTheory.Internal.SeparationSource
import YesMetaZFC.SetTheory.Filter.SourceUltrafilter
import YesMetaZFC.SetTheory.Filter.Projection

/-! # 实际初等源中的子集代数与限制超滤

在源中分离差集和交集，得到完整的源内部容许代数，再实际限制已有超滤。
本构造只用 ZF 与源的全内部分离；初始模型和后继模型共用同一理论接口。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sc_source_field_l (hZF : M.Models ZF) {ω c X R D}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (hD : M.mem D X) :
    ∃ P, Source_d X D P ∧ Field_d D P := by
  let φ : Delta0UnarySchema 1 := { body := Formula.subset .newest (.bound 1), delta0 := .atom _ _ _ }
  obtain ⟨P, hp⟩ := KP.separation_exists_d (ZF.modelsKP hZF) φ ⟨fun _ => D, fun _ => D⟩ X
  have hP : Source_d X D P := fun A => (hp A).trans (and_congr_right fun _ => Formula.satisfies_subset_iff ..)
  refine ⟨P, hP, ⟨fun A hA => ((hP A).mp hA).2, (hP D).mpr ⟨hD, fun _ h => h⟩, ?_, ?_⟩⟩
  · intro A hA
    let ψ : UnarySchema 1 := { body := .neg (.mem .newest (.bound 1)) }
    obtain ⟨B, hBX, hb⟩ := sc_separate_source_l I hZF hω hX hm theory ψ (.neg (.mem _ _))
      ⟨fun _ => A, fun _ => A⟩ (fun _ => ((hP A).mp hA).1) hD
    have spec v : M.mem v B ↔ M.mem v D ∧ ¬ M.mem v A := by
      apply (hb v).trans
      simp only [ψ, UnarySchema.denote, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff]
      rfl
    exact ⟨B, (hP B).mpr ⟨hBX, fun v hv => ((spec v).mp hv).1⟩, spec⟩
  · intro A B hA hB
    let ψ : UnarySchema 1 := { body := .mem .newest (.bound 1) }
    obtain ⟨C, hCX, hc⟩ := sc_separate_source_l I hZF hω hX hm theory ψ (.mem _ _)
      ⟨fun _ => B, fun _ => B⟩ (fun _ => ((hP B).mp hB).1) ((hP A).mp hA).1
    have spec v : M.mem v C ↔ M.mem v A ∧ M.mem v B :=
      (hc v).trans (and_congr_right fun _ => Formula.satisfies_mem_iff ..)
    exact ⟨C, (hP C).mpr ⟨hCX, fun v hv => ((hP A).mp hA).2 v ((spec v).mp hv).1⟩, spec⟩

theorem sc_source_ultrafilter_l (hZF : M.Models ZF) {ω c X R D U}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R)
    (hD : M.mem D X) (hU : Sf_ultra_d X D U) :
    ∃ P V, Source_d X D P ∧ Rel_ultra_d D P V ∧ ∀ A, M.mem A V ↔ M.mem A P ∧ M.mem A U := by
  obtain ⟨P, hP, hp⟩ := sc_source_field_l I hZF hω hX hm theory hD
  obtain ⟨V, hV, hv⟩ := hU.restrict_l (ZF.modelsKP hZF) (fun A hA => ((hP A).mp hA).1) hp
  exact ⟨P, V, hP, hV, hv⟩

end YesMetaZFC.SetTheory.Internal
