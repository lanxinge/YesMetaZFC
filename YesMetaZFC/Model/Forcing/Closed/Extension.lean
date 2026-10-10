import YesMetaZFC.Model.Forcing.Distributive.Extension
import YesMetaZFC.Model.Forcing.Closed.Proper
import YesMetaZFC.Model.Forcing.Proper.Preservation.Countable

/-! # 可数闭泛型扩张的模型性及内部序列反射

同一规范嵌入返回 ZFC、内部 ω、旧序列及可数子集的实际原像。公共分配性层
给出可数性与 ω₁ 保持；实际 proper club 另提供可数共尾性与旧序数界。
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
  have hD := closed_distributive_l O hZF (ZFC.dc_l I hZFC hω) hω hc
  obtain ⟨_, e, hv, he, hi, hw, hr, hf, hy, ht, ho⟩ := distributive_extension_l O hZF hU hω hD hb
  have hPr := closed_proper_l ⟨O.refl, O.trans⟩ hZFC hω hc
  exact ⟨hE, e, hv, he, hi, hw, hr, hf, hy, ht, ho,
    (fun _ => proper_cf_omega_l O hZFC hU hω hPr hb e hi he hv),
    fun _ _ hcf hωcf _ hY hy => proper_countable_bounded_l O hZFC hU hω hPr hb e he hv hcf hωcf hY hy⟩

end YesMetaZFC.Model.Forcing.Internal
