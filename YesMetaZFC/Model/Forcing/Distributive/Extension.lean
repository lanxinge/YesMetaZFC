import YesMetaZFC.Model.Forcing.Distributive.NoNewCountable
import YesMetaZFC.SetTheory.Continuum

/-! # ZF 中可数分配扩张的可数性反射与 ω₁ 保持

新可数旧集合具有精确的旧原像，因此直接反射可数性与 Hartogs 数。
同一个规范嵌入同时返回全部结论，不依赖 properness 或选择公理。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R z U
local notation "J" => kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)

theorem distributive_countable_reflect_l {ω b X} (hω : M.IsOmega ω)
    (hD : Distributive_d (M := M) B R z ω) (hb : U b)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y)
    (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a))
    (hc : (E).CardinalLessOrEqual J (e X) (e ω)) : M.CardinalLessOrEqual I X ω := by
  obtain ⟨A, _, hA, ha⟩ := no_new_countable_l O hZF hU hω hD hb e hv he (fun _ h => h) hc
  exact hi ha ▸ hA

theorem distributive_omega_one_l {ω b κ} (hω : M.IsOmega ω)
    (hD : Distributive_d (M := M) B R z ω) (hb : U b)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y)
    (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a)) (hκ : M.IsHartogsNumber I κ ω) :
    (E).IsHartogsNumber J (e κ) (e ω) := by
  have hE := preserves_zf_l O hZF hU
  apply ZF.hartogs_bound_l J hE (image_ordinal_l e hi he hZF.1 (internal_foundation_l O hZF hU) hκ.1)
  · intro α hα
    obtain ⟨a, ha, rfl⟩ := (he κ α).mp hα
    obtain ⟨F, hF⟩ := (hκ.2 a (hκ.1.mem ha)).mp ha
    exact ⟨e F, image_injection_l (hEN := hE.1) (hPN := internal_pair_l O hZF hU) e hi he hF⟩
  · exact fun hc => hκ.not_cardinalLessOrEqual (ZF.modelsKP hZF)
      (distributive_countable_reflect_l O hZF hU hω hD hb e hi he hv hc)

/-- ZF、原实数、旧值序列、可数子集及 ω₁ 保持的一次装配。 -/
theorem distributive_extension_l {ω b} (hω : M.IsOmega ω)
    (hD : Distributive_d (M := M) B R z ω) (hb : U b) :
    (E).Models ZF ∧ ∃ e : M.Domain → (E).Domain,
      (∀ a s, Check_d M b a s → Qval_d M B R z U s (e a)) ∧
      (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧ Function.Injective e ∧ (E).IsOmega (e ω) ∧
      (∀ x, (E).MemberSubset x (e ω) → ∃ a, M.MemberSubset a ω ∧ e a = x) ∧
      (∀ X F, (E).IsSetFunctionFromTo J F (e ω) (e X) →
        ∃ G, M.IsSetFunctionFromTo I G ω X ∧ e G = F) ∧
      (∀ X Y, (E).MemberSubset Y (e X) → (E).CardinalLessOrEqual J Y (e ω) →
        ∃ A, M.MemberSubset A X ∧ M.CardinalLessOrEqual I A ω ∧ e A = Y) ∧
      (∀ X, (E).CardinalLessOrEqual J (e X) (e ω) ↔ M.CardinalLessOrEqual I X ω) ∧
      ∀ κ, M.IsHartogsNumber I κ ω → (E).IsHartogsNumber J (e κ) (e ω) := by
  have hE := preserves_zf_l O hZF hU
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hZF hU hb
  have hw : (E).IsOmega (e ω) := image_omega_l (hEN := hE.1) e hi he hZF (internal_foundation_l O hZF hU) hω
    (fun X => KP.difference_exists_d (ZF.modelsKP hE) X (e ω))
  refine ⟨hE, e, hv, he, hi, hw, (fun x hx => ?_),
    (fun _ _ hF => no_new_functions_l O hZF hU hD hb e hv he hF),
    (fun _ _ hY hy => no_new_countable_l O hZF hU hω hD hb e hv he hY hy),
    (fun _ => ⟨distributive_countable_reflect_l O hZF hU hω hD hb e hi he hv, ?_⟩),
    fun _ hκ => distributive_omega_one_l O hZF hU hω hD hb e hi he hv hκ⟩
  · obtain ⟨a, ha, _, hax⟩ := no_new_countable_l O hZF hU hω hD hb e hv he hx
      (ZF.exists_inclusionInjection hE J hx)
    exact ⟨a, ha, hax⟩
  · rintro ⟨F, hF⟩
    exact ⟨e F, image_injection_l (hEN := hE.1) (hPN := internal_pair_l O hZF hU) e hi he hF⟩

end YesMetaZFC.Model.Forcing.Internal
