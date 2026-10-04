import YesMetaZFC.Model.SetTheory.Internal.PointwiseTrace
import YesMetaZFC.Model.SetTheory.Internal.PointwiseTruth

/-! # 全坐标代表赋值的源内真值集

内部程序只读取有限支撑，故源内逐点分离集也精确表示全坐标赋值下的
统一满足关系；分量映射可直接对这个实际集合应用测度协调律。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem smap_full_trace_l {ω χ c d X R H S q D E z n F r a}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ)
    (hH : H_d I χ H) (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (hn : Smem_d I d H S)
    (hq : Smap_d I ω c d X H q) (hD : M.mem D X) (hE : M.IsFunctionSpace I E ω X)
    (hz : Sformula_d I ω z n F r) (ha : M.mem a E) (hh : Pe_repr_d I ω D X a) :
    ∃ A, M.mem A X ∧ ∀ v, M.mem v A ↔ M.mem v D ∧
      ∃ f, M.mem f E ∧ Pe_assign_d I ω D X a f v ∧ Satisfies_d I ω c z f := by
  obtain ⟨b, hb, hB⟩ := sbound_exists_l I hZF hω hz.2.1
  have bω := hω.transitive hZF b hb
  obtain ⟨A, hAX, hA⟩ := smap_pe_trace_l hZFC hω hχ hωχ hH hX hm hn hq hD hE hz.2.1 hz.2.2 hb hB ha
    (fun i g hi => hh i g (bω i hi))
  refine ⟨A, hAX, fun v => (hA v).trans (and_congr_right fun hv => ?_)⟩
  apply (pe_sat_full_l I hZF hX hE hz.2.1 hB bω hz.2.2 ha hh hv hm.1.2.1).trans
  exact exists_congr fun f => and_congr_right fun _ => and_congr_right fun _ =>
    (satisfies_decode_l I hZF.1 hm.1 hz hE).symm

end YesMetaZFC.SetTheory.Internal
