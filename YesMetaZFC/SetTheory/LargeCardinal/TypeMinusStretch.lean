import YesMetaZFC.SetTheory.LargeCardinal.WoodinTypes
import YesMetaZFC.Model.SetTheory.Internal.TypeMinusEmbedding

/-! # 前驱类型与同一实际扩展器的伸展交换

原查询域及其前驱类型属于源秩层。限制代码表固定，故前驱随实际初等像搬运；
名字列封闭性保证随后的投影也交换，包含目标中的新常量查询。
两个方向保留同一扩展器、同一超幂和同一坍塌图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 每个实际查询域都满足槽位封闭性；此外不要求两个查询域之间有包含关系。 -/
theorem Et_stretch_d.minus_l {ω θ κ L F X R D t u D₀ v : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X)
    (hD : M.mem D X) (slots : Tt_slots_d ω D) (slots₀ : Tt_slots_d ω D₀)
    (sub : M.MemberSubset t D) (minus : Tm_minus_d I ω D t u)
    (h : Et_stretch_d hZF ω κ L F X R t D₀ v) :
    ∃ w, Tm_minus_d I ω D₀ v w ∧ Et_stretch_d hZF ω κ L F X R u D₀ w := by
  obtain ⟨b, d, N, S, i, t', hm, hn, ultra, htt, cut⟩ := h
  have hi := ultra.elementary_l hZF hm.1 hn.1
  have hN := ultra.transitive_l hZF hn.1
  have trans := ZF.v_transitive_l I hZF hX
  have hu := ZF.v_subset_mem_l I hZF hX hD (fun p hp => ((minus p).mp hp).1)
  obtain ⟨D', _, hDD⟩ := hi.1.1.2.2 D hD
  obtain ⟨u', _, huu⟩ := hi.1.1.2.2 u hu
  have image := (hi.type_minus_l hZF hω hX hθ hωX hN hm hn hDD htt huu).mp minus
  have slots' := hi.type_slots_l hZF hω trans hN hωX hm hn hDD slots
  have sub' := (hi.subset_l hZF hω trans hN hm hn htt hDD).mp sub
  obtain ⟨w, lower, cut'⟩ := tm_minus_project_l hZF hω slots₀ slots' sub' cut image
  exact ⟨w, lower, b, d, N, S, i, u', hm, hn, ultra, huu, cut'⟩

end YesMetaZFC.SetTheory.LargeCardinal
