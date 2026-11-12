import YesMetaZFC.SetTheory.Descriptive.Coding.RelationCode
import YesMetaZFC.SetTheory.InnerModel.OD.Brackets

/-! # 二值实数仍唯一定义原实数

规范配对解码只使用这一个二值实数及序数 ω。因此换用二值参数保留
原 OD[A] 定义能力，不把另选的自然数编号图加入参数。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}}

theorem bc_read_ob_l (hZF : M.Models ZF) {ω b r : M.Domain} (hω : M.IsOmega ω)
    (read : Bc_read_d (kp_pair_l (ZF.modelsKP hZF)) ω b r) : Ob_d b r := by
  let φ : BinarySchema 1 := { body := bc_read_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 1 := ⟨fun _ => ω,fun _ => ω⟩
  exact ob_source_l hZF φ ρ (fun _ => hω.isOrdinal (ZF.modelsKP hZF))
    (fun t => (bc_read_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1 ((ρ.push b).push t) (.bound 2) (.bound 1) .newest).trans
      ⟨fun h => bc_read_unique_l (ZF.modelsKP hZF) h read,fun eq => eq.symm ▸ read⟩)

end YesMetaZFC.SetTheory.InnerModel
