import YesMetaZFC.Model.Forcing.CCC.Bounds
import YesMetaZFC.SetTheory.Card.SmallBound
import YesMetaZFC.SetTheory.Card.Properties.Basic

/-! # 小力迫保持较大的基数与正则性

条件集有 μ<κ 的大小界时，其全部反链也有该界。新小集合的地覆盖和内部
κ×κ 计数排除基数塌缩；同一覆盖对共尾序列值域应用，得到正则性保持。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}

theorem size_chain_bound_l (hZF : M.Models ZF) {μ}
    (hB : M.CardinalLessOrEqual (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B μ) :
    Ccc_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) μ B R z := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  intro A hA
  obtain ⟨F, hF⟩ := ZF.exists_inclusionInjection hZF I (show M.MemberSubset A B from fun a ha => (hA.1 a ha).1)
  obtain ⟨G, hG⟩ := hB
  exact ZF.exists_compositionInjection hZF I hF hG

variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) (hU : Generic_d M B R z U)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R z U
local notation "J" => kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)

variable {ω μ κ b : M.Domain} (hω : M.IsOmega ω) (hωκ : M.mem ω κ) (hμκ : M.mem μ κ)
  (hB : M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
    (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) B μ) (hb : U b)
  (e : M.Domain → (extension_l M (ZFC.models_zf_l hZFC) B R z U).Domain) (hi : Function.Injective e)
  (he : ∀ a y, y ∈ e a ↔ ∃ c, M.mem c a ∧ e c = y)
  (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a))
include hω hωκ hμκ hB hb hi he hv

theorem small_cardinal_l (hκ : M.IsCardinal I κ) : (E).IsCardinal J (e κ) := by
  have hE := preserves_zf_l O hZF hU
  refine ⟨image_ordinal_l e hi he hZF.1 (internal_foundation_l O hZF hU) hκ.1, ?_⟩
  intro β hβ hEq
  obtain ⟨α, hα, rfl⟩ := (he κ β).mp hβ
  obtain ⟨ν, hνκ, hν, hμν, hαν⟩ := ZF.common_cardinal_l I hZF hκ.1 hωκ hμκ hα
  obtain ⟨W, hW⟩ := ZF.exists_cartesianProduct hZF I ν ν
  obtain ⟨F, hF⟩ := hEq.symm hE J
  obtain ⟨G, hG⟩ := ccc_injection_bound_l O hZFC hU (size_chain_bound_l hZF hB) hb hμν hαν hW e hi he hv hF.1
  obtain ⟨K, hK⟩ := ZF.cartesianSquare_cardinalLessOrEqual_of_selfMultiplication hZF I
    ⟨hν.1, Structure.Equinumerous.refl hZF I ν⟩ hW
    (ZF.infiniteCardinal_selfMultiplication hZF I hω (ZF.omega_cardinal_l I hZF hω) hν)
  exact hκ.2 ν hνκ (ZF.equinumerous_of_cardinalLessOrEqual hZF I
    (ZF.exists_inclusionInjection hZF I (hκ.1.transitive.memberSubset hνκ))
    (ZF.exists_compositionInjection hZF I hG hK))

/-- 大于条件集大小的不可数正则基数，在任意泛型中仍正则。 -/
theorem small_regular_l (hκ : M.IsRegularCardinal I κ) : (E).IsRegularCardinal J (e κ) := by
  have hE := preserves_zf_l O hZF hU
  have hk := small_cardinal_l O hZFC hU hω hωκ hμκ hB hb e hi he hv hκ.isCardinal
  have hw : (E).IsOmega (e ω) := image_omega_l (hEN := hE.1) e hi he hZF
    (internal_foundation_l O hZF hU) hω (fun T => KP.difference_exists_d (ZF.modelsKP hE) T (e ω))
  have hlim := ZF.infiniteCardinal_isLimitOrdinal hE J hw (ZF.omega_cardinal_l J hE hw)
    ⟨hk, ZF.exists_inclusionInjection hE J (hk.1.transitive.memberSubset ((image_member_l e hi he).mpr hωκ))⟩
  refine ⟨hk, hlim.hasCofinalOrdinalSequence_self hE J, fun δ ⟨F, hF⟩ => ?_⟩
  rcases Structure.IsOrdinal.trichotomy hE.1 hk.1 hF.isIncreasing.1.1.1
      (KP.difference_exists_d (ZF.modelsKP hE)) (KP.intersection_exists_d (ZF.modelsKP hE) (e κ) δ) with hEq | hkδ | hδk
  · exact Or.inl (hE.1.eq_of_same_members _ _ hEq)
  · exact Or.inr hkδ
  · apply False.elim
    obtain ⟨α, hα, rfl⟩ := (he κ δ).mp hδk
    obtain ⟨ν, hνκ, hν, hμν, hαν⟩ := ZF.common_cardinal_l I hZF hκ.isCardinal.1 hωκ hμκ hα
    obtain ⟨W, hW⟩ := ZF.exists_cartesianProduct hZF I ν ν
    obtain ⟨T, hT, hUnion⟩ := hF.isLimit.2.2
    have hf := hF.isSetInjectionFromTo hE J
    have hfT : (E).IsSetBijectionFromTo J F (e α) T := by
      refine ⟨⟨⟨hf.1.1, hf.1.2.1, fun i hi => ?_⟩, hf.2⟩, fun x hx => ?_⟩
      · obtain ⟨x, _, hx⟩ := hf.1.2.2 i hi
        exact ⟨x, (hT x).mpr ⟨i, hx⟩, hx⟩
      · obtain ⟨i, hi⟩ := (hT x).mp hx
        exact ⟨i, hf.1.input_mem_of_pairMember hi, hi⟩
    obtain ⟨G, hG⟩ := ZF.exists_inverseBijection hE J hfT
    obtain ⟨Y, hYκ, hY, hTY⟩ := ccc_set_cover_l O hZFC hU (size_chain_bound_l hZF hB) hb hμν hαν hW e hi he hv
      (show (E).MemberSubset T (e κ) from fun x hx => (hT x).mp hx |>.elim fun i hi => hf.1.output_mem_of_pairMember hi) ⟨G, hG.1⟩
    obtain ⟨L, hL⟩ := hY
    obtain ⟨K, hK⟩ := ZF.cartesianSquare_cardinalLessOrEqual_of_selfMultiplication hZF I
      ⟨hν.1, Structure.Equinumerous.refl hZF I ν⟩ hW
      (ZF.infiniteCardinal_selfMultiplication hZF I hω (ZF.omega_cardinal_l I hZF hω) hν)
    obtain ⟨γ, hγκ, hYγ⟩ := (ZF.small_subset_bounded_l I hZF hκ hYκ hνκ
      (ZF.exists_compositionInjection hZF I hL hK)).exists_bound
    obtain ⟨β, hβ, hγβ⟩ := (hUnion (e γ)).mp ((image_member_l e hi he).mpr hγκ)
    obtain ⟨a, ha, rfl⟩ := (he Y β).mp (hTY β hβ)
    have hγa := (image_member_l e hi he).mp hγβ
    rcases hYγ a ha with heq | haγ
    · exact KP.mem_irrefl_d (ZF.modelsKP hZF) γ (heq ▸ hγa)
    · exact KP.mem_irrefl_d (ZF.modelsKP hZF) γ ((hκ.isCardinal.1.mem hγκ).transitive a haγ γ hγa)

end YesMetaZFC.Model.Forcing.Internal
