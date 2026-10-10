import YesMetaZFC.SetTheory.LargeCardinal.IterationHistorySyntax
import YesMetaZFC.Model.SetTheory.Internal.SourceFunctionSize

/-! # 下降递归的初始行

可数传递定义域先由实际遗传大小界进入正规秩层。函数值的秩由正则性统一
控制，所以给定初等图及其可数编号都在同一初始模型内。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem pn_initial_row_l {ω β P a X R b S π η : M.Domain}
    (hω : M.IsOmega ω) (above : M.mem ω β) (regular : M.IsRegularCardinal I β)
    (rank : V_d I β P) (hX : M.TransitiveSet X) (hm : Smem_d I a X R) (hn : Smem_d I b P S)
    (embed : Smap_d I ω a b X P π) (countable : M.IsSetInjectionFromTo I η X ω) :
    ∃ ι, Pn_row_d hZF ω a X P π ι := by
  obtain ⟨K, S', model⟩ := pn_regular_model_l hZFC hω above regular rank
  obtain ⟨b', code⟩ := model.source.code
  obtain ⟨rfl, rfl⟩ := smem_unique_l I hZF.1 code hn
  obtain ⟨T, μ, tc, hμ, size⟩ := ZF.hmem_of_subset_l I hZF regular.isLimitOrdinal hX
    (fun _ h => h) above ⟨η, countable⟩
  have hXP := ZF.rk_transitive_bound_l I hZF tc.1 regular.isCardinal hμ size rank X tc.2.1
  obtain ⟨C, hC, fn, hπ⟩ := ZF.v_small_function_l hZF regular above ⟨η, countable⟩ hXP rank embed.1.1
  obtain ⟨U, hU, xu, wu⟩ := ZF.v_joint_bound_l I hZF rank hXP model.source.omega_mem
  have hη : M.mem η P := ZF.v_relation_mem_l I hZF rank regular.isLimitOrdinal hU (fun p hp => by
    obtain ⟨x, hx, i, hi, pair⟩ := (fn0_of_function_l (ZF.modelsKP hZF) countable.1).1 p hp
    exact ⟨x, xu x hx, i, wu i hi, pair⟩)
  obtain ⟨ι, hι, index⟩ := sc_graph_numbering_l hZF hω model.source.transitive code model.source.theory
    model.source.omega_mem hXP hC hη hπ countable (fn0_of_function_l (ZF.modelsKP hZF) fn)
  exact ⟨ι, hX, R, S', b', ω, K, hm, code, model, hπ, hι, embed, index⟩

end YesMetaZFC.SetTheory.LargeCardinal
