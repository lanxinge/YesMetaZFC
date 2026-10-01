import YesMetaZFC.Model.Forcing.Closed.NoNewCountable
import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer
import YesMetaZFC.Model.Forcing.Closed.Proper
import YesMetaZFC.Model.Forcing.Proper.Preservation.Countable

/-! # 可数闭泛型扩张的模型性及内部序列反射

同一规范嵌入返回 ZFC、内部 ω、旧序列及可数子集的实际原像。可数闭性构造
真正的 proper club，因而同时取得 ω₁、旧可数性与可数共尾性保持。
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
include O hU

theorem closed_extension_l {ω b} (hω : M.IsOmega ω) (hc : Closed_d I B R z ω) (hb : U b) :
    (E).Models ZFC ∧ ∃ e : M.Domain → (E).Domain,
      (∀ a s, Check_d M b a s → Qval_d M B R z U s (e a)) ∧
      (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧ Function.Injective e ∧ (E).IsOmega (e ω) ∧
      (∀ x, (E).MemberSubset x (e ω) → ∃ a, M.MemberSubset a ω ∧ e a = x) ∧
      (∀ X F, (E).IsSetFunctionFromTo J F (e ω) (e X) →
        ∃ G, M.IsSetFunctionFromTo I G ω X ∧ e G = F) ∧
      (∀ X Y, (E).MemberSubset Y (e X) → (E).CardinalLessOrEqual J Y (e ω) →
        ∃ A, M.MemberSubset A X ∧ M.CardinalLessOrEqual I A ω ∧ e A = Y) ∧
      (∀ X, (E).CardinalLessOrEqual J (e X) (e ω) ↔ M.CardinalLessOrEqual I X ω) ∧
      (∀ κ, M.IsHartogsNumber I κ ω → (E).IsHartogsNumber J (e κ) (e ω)) ∧
      (∀ α, (E).IsCofinality J (e ω) (e α) ↔ M.IsCofinality I ω α) ∧
      ∀ α cf, M.IsCofinality I cf α → M.mem ω cf → ∀ Y, (E).MemberSubset Y (e α) →
        (E).CardinalLessOrEqual J Y (e ω) → ∃ β, M.mem β α ∧ (E).MemberSubset Y (e β) := by
  have hE := preserves_zfc_l O hZFC hU
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hZF hU hb
  have hw : (E).IsOmega (e ω) := image_omega_l (hEN := hE.1) e hi he hZF (internal_foundation_l O hZF hU) hω
    (fun X => KP.difference_exists_d (ZF.modelsKP (ZFC.models_zf_l hE)) X (e ω))
  have hPr := closed_proper_l ⟨O.refl, O.trans⟩ hZFC hω hc
  refine ⟨hE, e, hv, he, hi, hw, (fun x hx => ?_),
    (fun _ _ hF => no_new_functions_l O hZFC hU hω hc hb e hv he hF),
    (fun _ _ hY hy => no_new_countable_l O hZFC hU hω hc hb e hv he hY hy),
    (fun _ => ⟨proper_countable_reflect_l O hZFC hU hω hPr hb e hv, ?_⟩),
    (fun _ hκ => proper_omega_one_l O hZFC hU hω hPr hb e hi he hv hκ),
    (fun _ => proper_cf_omega_l O hZFC hU hω hPr hb e hi he hv),
    fun _ _ hcf hωcf _ hY hy => proper_countable_bounded_l O hZFC hU hω hPr hb e he hv hcf hωcf hY hy⟩
  · obtain ⟨a, ha, _, hax⟩ := no_new_countable_l O hZFC hU hω hc hb e hv he hx
      (ZF.exists_inclusionInjection (ZFC.models_zf_l hE) J hx)
    exact ⟨a, ha, hax⟩
  · rintro ⟨F, hF⟩
    exact ⟨e F, image_injection_l (hEN := hE.1) (hPN := internal_pair_l O hZF hU) e hi he hF⟩

end YesMetaZFC.Model.Forcing.Internal
