import YesMetaZFC.Model.SetTheory.Internal.UniformizationCode
import YesMetaZFC.Model.SetTheory.Internal.Collection
import YesMetaZFC.SetTheory.HereditaryAlgebra

/-! # 源模型中的实际统一见证函数

收集构造给出的函数图是 D×C 的子集，故它确实属于正则 H(χ)。
一般源之间的统一化回拉在 SourceCollection 中直接消费小定义域闭包。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem h_uniform_l {ω χ H R E F n r i j f D} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H) (hD : M.mem D H)
    (hh : Scollect_d I H R E F n r i j f D H) :
    ∃ B C, M.mem B H ∧ M.mem C H ∧ Suniform_d I H R E F n r i j f D C B := by
  obtain ⟨C, B, hC, hB, select⟩ := h_collect_function_l I hZFC hω hχ hωχ hH hD hh
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I D C
  have hb := fn0_of_function_l (ZF.modelsKP hZF) hB
  have hBH := ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH (ZFC.h_product_l hZFC hω hχ hωχ hH hD hC hP) B
    (fun p hp => (hP p).mpr (hb.1 p hp))
  exact ⟨B, C, hBH, hC, hb, select⟩


end YesMetaZFC.SetTheory.Internal
