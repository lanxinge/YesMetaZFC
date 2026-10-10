import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceProjection
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Relation

/-! # 坐标拉回精确保持代表等价

先在源中构造原代表的相等集，再取容许逆像。测度投影方程由此同时给出
等价保持与反映，供商图构造直接使用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rs_pullback_eq_l (hZF : M.Models ZF) {ω c X R D E P Q U V t f g f' g'}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R)
    (hD : M.mem D X) (hP : Source_d X D P) (hU : Rel_ultra_d D P U) (hV : Rel_ultra_d E Q V)
    (ht : Push_d D E P Q U V t) (hf : Sfun_d X D f) (hg : Sfun_d X D g)
    (hF : Cp0_d E D X t f f') (hG : Cp0_d E D X t g g') : Rp_eq_d X U f g ↔ Rp_eq_d X V f' g' := by
  obtain ⟨A, hAX, ha⟩ := sc_equalizer_l I hZF hω hX hm theory hD hf hg.1
  have hAP := (hP A).mpr ⟨hAX, fun v hv => ((ha v).mp hv).1⟩
  obtain ⟨B, hB, hb, he⟩ := ht.2 A hAP
  have spec v : M.mem v B ↔ M.mem v E ∧ ∃ x, M.mem x X ∧ Rd_entry_d v x f' ∧ Rd_entry_d v x g' := by
    refine (hb v).trans ⟨?_, ?_⟩
    · rintro ⟨hv, w, hw, hvw⟩
      obtain ⟨_, x, hx, hfx, hgx⟩ := (ha w).mp hw
      exact ⟨hv, x, hx, (hF.value_l ht.1 (hf.function_l hX) hvw).mpr hfx,
        (hG.value_l ht.1 (hg.function_l hX) hvw).mpr hgx⟩
    · rintro ⟨hv, x, hx, hfx, hgx⟩
      obtain ⟨w, hw, hvw⟩ := ht.1.2.1 v hv
      exact ⟨hv, w, (ha w).mpr ⟨hw, x, hx, (hF.value_l ht.1 (hf.function_l hX) hvw).mp hfx,
        (hG.value_l ht.1 (hg.function_l hX) hvw).mp hgx⟩, hvw⟩
  exact (rp_eq_member_l hU hAP ha).symm.trans (he.symm.trans (rp_eq_member_l hV hB spec))

end YesMetaZFC.SetTheory.Internal
