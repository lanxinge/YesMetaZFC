import YesMetaZFC.Model.SetTheory.Internal.SourceSmall
import YesMetaZFC.Model.SetTheory.Internal.RelationSubset

/-! # 共同小容器内新参数的原关系编号

传递小容器的每个成员都由源内同一编号图控制。搬运其全称闭包后，
原关系低层的任意新集合也取得内部序数编号，足以直接调用小集合收集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.small_raw_l {ω c X R c' Y S q B H : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q) (hBH : Rd_entry_d B H q)
    (trans : M.TransitiveSet B) (small : Sc_small_d X B) : Rr_small_d I Y S H := by
  have hB := hq.1.1.input_mem_of_pairMember hBH
  have hH := hq.1.1.output_mem_of_pairMember hBH
  let φ : Formula 1 1 := Formula.forallMem .newest (sc_small_m .newest)
  let ρ : Env (smdl_structure_l I (R := R) hm.1.2.1) 1 := ⟨fun _ => ⟨B, hB⟩, fun _ => ⟨B, hB⟩⟩
  let η : Env (smdl_structure_l I (R := S) model.2.1) 1 := ⟨fun _ => ⟨H, hH⟩, fun _ => ⟨H, hH⟩⟩
  have valid : Formula.satisfies ρ φ := by
    apply (smem_formula_l I hm ⟨⟨B, hB⟩⟩ φ ⟨ρ.bound, ρ.free⟩).mp
    rw [Formula.satisfies_forallMem_iff]
    intro a ha
    exact (sc_small_sat_l (ZF.modelsKP hZF) hX _ _ .newest).mpr (small.mono_l (trans a.val ha))
  have moved := (smap_source_l I hZF hω hm.1 model hq φ
    (by simp -implicitDefEqProofs [φ, Formula.forallMem, Definitional.Formula.FreeClosed])
    ρ η (fun _ => hBH)).mp valid
  exact (rr_small_native_l I model.2.1 ⟨H, hH⟩).mp moved

end YesMetaZFC.SetTheory.Internal
