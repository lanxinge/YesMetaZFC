import YesMetaZFC.SetTheory.HereditaryAlgebra
import YesMetaZFC.SetTheory.InnerModel.Recursion.FunctionGraph

/-! # 正则 Hχ 对小定义域函数的封闭

函数可在背景中先构造；其像由正则性仍是遗传小集合，整张图随之属于 Hχ。
-/
namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem h_function_l (hZFC : M.Models ZFC) {ω χ H D F : M.Domain} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (InnerModel.kp_pair_l (ZF.modelsKP (models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hH : H_d (InnerModel.kp_pair_l (ZF.modelsKP (models_zf_l hZFC))) χ H)
    (hD : M.mem D H) (hf : M.IsSetFunctionFromTo (InnerModel.kp_pair_l (ZF.modelsKP (models_zf_l hZFC))) F D H) :
    M.mem F H := by
  let hZF := models_zf_l hZFC
  let I := InnerModel.kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨μ, hμ, hDμ⟩ := ZF.hmem_size_l I hZF ((hH D).mp hD)
  obtain ⟨R, hr⟩ := ZF.exists_range_of_setFunction hZF I hf.1 hf.2.1
  have fn : M.IsSetFunctionFromTo I F D R := ⟨hf.1, hf.2.1, fun x hx =>
    (hf.2.2 x hx).imp fun y hy => ⟨(hr y).mpr ⟨x, hy.2⟩, hy.2⟩⟩
  have hRμ := ZF.ordinal_image_bound_l I hZF (hχ.isCardinal.1.mem hμ) hDμ fn
    (fun y hy => ((hr y).mp hy).imp fun x hx => ⟨hf.input_mem_of_pairMember hx, hx⟩)
  have hRH := h_small_closed_l I hZFC hω hχ hωχ hH
    (fun y hy => ((hr y).mp hy).elim fun _ hx => hf.output_mem_of_pairMember hx) hμ hRμ
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I D R
  exact ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH (h_product_l hZFC hω hχ hωχ hH hD hRH hP) F
    (fun p hp => (hP p).mpr ((InnerModel.fn0_of_function_l (ZF.modelsKP hZF) fn).1 p hp))

end YesMetaZFC.SetTheory.ZFC
