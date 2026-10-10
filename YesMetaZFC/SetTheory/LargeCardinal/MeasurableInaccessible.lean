import YesMetaZFC.SetTheory.LargeCardinal.MeasurePower
import YesMetaZFC.SetTheory.LargeCardinal.MeasureRegularity
import YesMetaZFC.SetTheory.Card.SmallEnumeration
import YesMetaZFC.SetTheory.Choice

/-! # 可测基数不可达及武丁基数下方的不可达选择

ZF 中已经得到正则性及小幂集不存在反向单射。对象模型的选择公理提供
幂集的实际序数编号，遂得到强极限性，并接到原武丁测度构造上。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Measurable_d.strong_limit_l (hZFC : M.Models ZFC) {κ : M.Domain}
    (h : Measurable_d I κ) : M.IsStrongLimitCardinal I κ := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨card, _, U, _, _, hU, hn, hc⟩ := h
  refine ⟨card, fun α hα P power => ?_⟩
  have no := ed_power_injection_l I hZF hU hn hc hα power
  obtain ⟨δ, F, hδ, ff, onto⟩ := ZFC.ordinal_enum_l hZFC I P
  obtain ⟨id, ii⟩ := ZF.exists_identityBijection hZF I δ
  have bound := ZF.ordinal_image_bound_l I hZF hδ ⟨id, ii.1⟩ ff onto
  obtain ⟨χ, hχ⟩ := ZF.exists_hartogsNumber hZF I δ
  obtain ⟨ν, g, _, νcard, bij⟩ := ZF.small_enumeration_l I hZF (hχ.isCardinal hZF I)
    ((hχ.2 δ hδ).mpr ⟨id, ii.1⟩) bound
  have lt : M.mem ν κ := by
    rcases νcard.1.trichotomy hZF.1 card.1 (KP.difference_exists_d (ZF.modelsKP hZF))
        (KP.intersection_exists_d (ZF.modelsKP hZF) ν κ) with eq | lt | gt
    · exact (no ⟨g, hZF.1.eq_of_same_members ν κ eq ▸ bij.1⟩).elim
    · exact lt
    · obtain ⟨r, ri⟩ := ZF.exists_inclusionInjection hZF I (νcard.1.transitive κ gt)
      exact (no (ZF.exists_compositionInjection hZF I ri bij.1)).elim
  obtain ⟨r, rb⟩ := ZF.exists_inverseBijection hZF I bij
  obtain ⟨s, si⟩ := ZF.exists_inclusionInjection hZF I (card.1.transitive ν lt)
  exact ⟨ZF.exists_compositionInjection hZF I rb.1 si, fun eq =>
    (eq.symm hZF I).elim fun f hf => no ⟨f, hf.1⟩⟩

/-- 长度由原武丁强嵌入产生的非主完备测度选择，正则和强极限均已实际证明。 -/
theorem woodin_inaccessible_above_l (hZFC : M.Models ZFC) {ω δ α : M.Domain}
    (hω : M.IsOmega ω) (hd : Woodin_d I δ) (hα : M.mem α δ) :
    ∃ κ, M.mem α κ ∧ M.mem κ δ ∧ M.mem ω κ ∧ M.IsRegularCardinal I κ ∧ M.IsStrongLimitCardinal I κ := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨κ, hακ, hκδ, meas⟩ := woodin_measurable_above_l I hZF hd hα
  have hr := meas.regular_l I hZF
  have hs := meas.strong_limit_l I hZFC
  obtain ⟨_, ω₀, _, hω₀, hωκ, _⟩ := meas
  have eq := hZF.1.eq_of_same_members ω₀ ω (fun x => ⟨hω₀.2 ω hω.1 x, hω.2 ω₀ hω₀.1 x⟩)
  exact ⟨κ, hακ, hκδ, eq ▸ hωκ, hr, hs⟩

end YesMetaZFC.SetTheory.LargeCardinal
