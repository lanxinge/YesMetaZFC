import YesMetaZFC.Model.Forcing.Proper.Preservation.Injection
import YesMetaZFC.Model.Forcing.Proper.Preservation.Cofinality
import YesMetaZFC.SetTheory.Continuum

/-! # proper 泛型扩张的可数性反射与 ω₁ 保持

扩张中的实际单射先经真值定理取回一个力迫条件，再反射到地模型。
由此得到全部旧集合的可数性双向对应，地模型 ω 的 Hartogs 序数因而精确保留。
同一个规范嵌入还给出新可数集合的旧覆盖、精确 ω 共尾度保持与旧序数界。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) (hU : Generic_d M B R z U)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R z U
local notation "J" => kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)

theorem proper_countable_reflect_l {ω b X} (hω : M.IsOmega ω) (hPr : Proper_d I ω B R z) (hb : U b)
    (e : M.Domain → (E).Domain) (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a))
    (hc : (E).CardinalLessOrEqual J (e X) (e ω)) : M.CardinalLessOrEqual I X ω := by
  obtain ⟨F, hF⟩ := hc
  obtain ⟨f, hfn, hf⟩ := value_name_l F
  obtain ⟨t, ht, htn, _⟩ := zf_check_l M hZF (hU.proper b hb).1 X
  obtain ⟨w, hw, hwn, _⟩ := zf_check_l M hZF (hU.proper b hb).1 ω
  let ρ := fn_env_l t w f
  let η := fn_env_l (e X) (e ω) F
  have hρ : Env_val_d hZF ρ η := by
    intro s
    cases s with
    | free _ => exact hv ω w hw
    | bound i => exact Fin.cases hf (Fin.cases (hv X t ht) (fun _ => hv ω w hw)) i
  have hsat : Formula.satisfies η inj_body_m :=
    (Formula.satisfies_isInjectionFromTo_iff J (extension_ext_l O hZF hU) η .newest (.bound 1) (.bound 2)).mpr hF
  obtain ⟨p, hp, hforce⟩ := (forcing_truth_l O hZF hU inj_body_m inj_body_closed_l ρ η hρ).mpr hsat
  obtain ⟨r, hr, hrp, hrb⟩ := hU.directed p b hp hb
  have hr' := hU.proper r hr
  have hforce' := (forces_regular_l O hZF inj_body_m ρ (fun s => qval_name_l (hρ s))).1
    p r (hU.proper p hp).1 ⟨hr'.1, hr'.2, hrp⟩ hforce
  exact proper_injection_reflect_l O hZFC hω hPr (hU.proper b hb).1 ⟨hr'.1, hr'.2, hrb⟩ ht hw
    ⟨htn, hwn, hfn, hforce'⟩

/-- 一次构造规范嵌入，所有旧集合同时满足可数性的精确双向对应。 -/
theorem proper_countable_l {ω b} (hω : M.IsOmega ω) (hPr : Proper_d I ω B R z) (hb : U b) :
    ∃ e : M.Domain → (E).Domain,
      (∀ a s, Check_d M b a s → Qval_d M B R z U s (e a)) ∧
      (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧ Function.Injective e ∧
      (∀ X, (E).CardinalLessOrEqual J (e X) (e ω) ↔ M.CardinalLessOrEqual I X ω) ∧
      ∀ X Y, (E).MemberSubset Y (e X) → (E).CardinalLessOrEqual J Y (e ω) →
        ∃ A, M.MemberSubset A X ∧ M.CardinalLessOrEqual I A ω ∧ (E).MemberSubset Y (e A) := by
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hZF hU hb
  refine ⟨e, hv, he, hi, (fun X => ⟨proper_countable_reflect_l O hZFC hU hω hPr hb e hv, ?_⟩),
    fun X Y hY hc => proper_set_cover_l O hZFC hU hω hPr hb e hv hY hc⟩
  rintro ⟨F, hF⟩
  exact ⟨e F, image_injection_l (hEN := extension_ext_l O hZF hU) (hPN := internal_pair_l O hZF hU) e hi he hF⟩

/-- 地模型的第一不可数序数，在每个 proper 泛型扩张中仍恰好是第一不可数序数。 -/
theorem proper_omega_one_l {ω b κ} (hω : M.IsOmega ω) (hPr : Proper_d I ω B R z) (hb : U b)
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
      (proper_countable_reflect_l O hZFC hU hω hPr hb e hv hc)

/-- 规范嵌入、ZFC、ω₁、可数覆盖及可数共尾性保持一次装配。 -/
theorem proper_extension_l {ω b κ} (hω : M.IsOmega ω) (hPr : Proper_d I ω B R z) (hb : U b)
    (hκ : M.IsHartogsNumber I κ ω) : (E).Models ZFC ∧ ∃ e : M.Domain → (E).Domain,
      (∀ a s, Check_d M b a s → Qval_d M B R z U s (e a)) ∧
      (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧ Function.Injective e ∧
      (E).IsOmega (e ω) ∧ (E).IsHartogsNumber J (e κ) (e ω) ∧
      (∀ X, (E).CardinalLessOrEqual J (e X) (e ω) ↔ M.CardinalLessOrEqual I X ω) ∧
      (∀ X Y, (E).MemberSubset Y (e X) → (E).CardinalLessOrEqual J Y (e ω) →
        ∃ A, M.MemberSubset A X ∧ M.CardinalLessOrEqual I A ω ∧ (E).MemberSubset Y (e A)) ∧
      (∀ α, (E).IsCofinality J (e ω) (e α) ↔ M.IsCofinality I ω α) ∧
      ∀ α cf, M.IsCofinality I cf α → M.mem ω cf → ∀ Y, (E).MemberSubset Y (e α) →
        (E).CardinalLessOrEqual J Y (e ω) → ∃ β, M.mem β α ∧ (E).MemberSubset Y (e β) := by
  have hE := preserves_zfc_l O hZFC hU
  obtain ⟨e, hv, he, hi, hc, hcover⟩ := proper_countable_l O hZFC hU hω hPr hb
  have hw : (E).IsOmega (e ω) := image_omega_l (hEN := hE.1) e hi he hZF (internal_foundation_l O hZF hU) hω
    (fun T => KP.difference_exists_d (ZF.modelsKP (ZFC.models_zf_l hE)) T (e ω))
  exact ⟨hE, e, hv, he, hi, hw, proper_omega_one_l O hZFC hU hω hPr hb e hi he hv hκ, hc, hcover,
    fun _ => proper_cf_omega_l O hZFC hU hω hPr hb e hi he hv,
    fun _ _ hcf hωcf _ hY hc => proper_countable_bounded_l O hZFC hU hω hPr hb e he hv hcf hωcf hY hc⟩

end YesMetaZFC.Model.Forcing.Internal
