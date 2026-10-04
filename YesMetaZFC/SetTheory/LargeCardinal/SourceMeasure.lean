import YesMetaZFC.SetTheory.LargeCardinal.DerivedFilter
import YesMetaZFC.SetTheory.Filter.Source
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Model

/-! # 源内部子集与源内部函数上的实际分量

容许子集恰好是 X 中 D 的子集，代表函数也明确限制为 X 的成员。
源中常值图保证代表族非空，商只消费已经证明的共同细化性质。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ed_source_ultrafilter_l (hZF : M.Models ZF) {ω X A Y B j D D' a}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hc : Rd_closed_d X) (hD : M.PairMember I D D' j) (ha : M.mem a D') :
    ∃ P U, FilterZF.Source_d X D P ∧ Ed_filter_d I j a D U ∧ FilterZF.Rel_ultra_d D P U := by
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  obtain ⟨P, hP, hp⟩ := FilterZF.source_field_exists_l (ZF.modelsKP hZF) hc (hj.input_mem_of_pairMember hD)
  obtain ⟨U, hu, hf⟩ := ed_trace_ultrafilter_l I hZF hω h hX hY hp (fun s hs => ((hP s).mp hs).1) hD ha
  refine ⟨P, U, hP, fun s => (hu s).trans ?_, hf⟩
  exact ⟨fun ⟨hs, ht⟩ => ⟨((hP s).mp hs).2, ht⟩,
    fun ⟨hs, t, ht, hat⟩ => ⟨(hP s).mpr ⟨hj.input_mem_of_pairMember ht, hs⟩, t, ht, hat⟩⟩

theorem ed_source_model_l (hZF : M.Models ZF) {ω X A Y B j D D' a}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hc : Rd_closed_d X) (hD : M.PairMember I D D' j) (ha : M.mem a D') : ∃ P U s R G c p C T,
      FilterZF.Source_d X D P ∧ Ed_filter_d I j a D U ∧ FilterZF.Rel_ultra_d D P U ∧
      Smdl_d I s X R ∧ (∀ x y, M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y) ∧
      (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) ∧ Rp_model_d I D X U R c G p C T := by
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, hj⟩ := h; exact hj.1.1
  have hDX := hj.input_mem_of_pairMember hD
  obtain ⟨P, U, hP, hu, hU⟩ := ed_source_ultrafilter_l I hZF hω h hX hY hc hD ha
  obtain ⟨s, R, hs, hR⟩ := smdl_membership_l I hZF ⟨D, hDX⟩
  obtain ⟨f, hfX, hf⟩ := FilterZF.source_function_l (ZF.modelsKP hZF) hc hDX
  obtain ⟨G, c, p, C, T, hG, hm⟩ := rp_family_model_l I hZF hU.base hfX hf R
  exact ⟨P, U, s, R, G, c, p, C, T, hP, hu, hU, hs, hR, hG, hm⟩

end YesMetaZFC.SetTheory.LargeCardinal
