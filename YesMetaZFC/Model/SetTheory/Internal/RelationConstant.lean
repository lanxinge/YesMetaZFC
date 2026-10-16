import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.Model.SetTheory.Internal.RelationEvaluation
import YesMetaZFC.Model.SetTheory.Internal.Extensionality

/-! # 全内部初等像中的源内常值函数

封闭句子的搬运覆盖目标的全部新参数，函数仍由原关系读取。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_constant_raw_l {ω b X R c C W i : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I b X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c C W) (hi : Smap_d I ω b c X C i)
    (en : Extensional (smdl_structure_l I (R := W) model.2.1))
    (d x : (smdl_structure_l I (R := W) model.2.1).Domain) :
    ∃ B f : (smdl_structure_l I (R := W) model.2.1).Domain,
      Fn0_d d B f ∧ ∀ s, Rd_entry_d s.val d.val W → Rd_entry_d s x f := by
  obtain ⟨z, hz⟩ := mx.1.2.1
  let ψ : Formula 1 4 := .conj (fn0_m (.bound 3) (.bound 1) .newest)
    (Formula.forallMem (.bound 3) (rd_entry0_m .newest (.bound 3) (.bound 1)))
  let φ : Formula 1 0 := .forallE (.forallE (.existsE (.existsE ψ)))
  let ρ : Env (smdl_structure_l I (R := R) mx.1.2.1) 0 := ⟨Fin.elim0, fun _ => ⟨z, hz⟩⟩
  let η : Env (smdl_structure_l I (R := W) model.2.1) 0 := ⟨Fin.elim0, fun _ => d⟩
  have valid : Formula.satisfies ρ φ := by
    apply (smem_formula_l I mx ⟨⟨z, hz⟩⟩ φ ⟨ρ.bound, ρ.free⟩).mp
    simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff]
    intro D z
    obtain ⟨f, B, hf, hB, ff, value⟩ := sc_constant_l hZF hω hX mx theory D.property z.property
    refine ⟨⟨B, hB⟩, ⟨f, hf⟩, ?_⟩
    apply (rt_model_delta_l hX _ (φ := ψ)
      (.conj (fn0_delta_l ..) (.forallMem _ (rd_entry0_delta_l ..))) _).mpr
    simp only [ψ, Formula.satisfies_conj_iff, fn0_sat_l hZF.1, Formula.satisfies_forallMem_iff, rd_entry0_sat_l hZF.1]
    exact ⟨ff, fun s hs => (value s z.val).mpr ⟨hs, rfl⟩⟩
  have moved := (smap_source_l I hZF hω mx.1 model hi φ
    (by simp -implicitDefEqProofs [φ, ψ, Definitional.Formula.FreeClosed, Formula.forallMem]) ρ η (fun i => Fin.elim0 i)).mp valid
  simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff] at moved
  obtain ⟨B, f, hf⟩ := moved d x
  simp only [ψ, Formula.satisfies_conj_iff, fn0_sat_l en, Formula.satisfies_forallMem_iff, rd_entry0_sat_l en] at hf
  exact ⟨B, f, hf⟩

end YesMetaZFC.SetTheory.Internal
