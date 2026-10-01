import YesMetaZFC.Model.Forcing.Proper.Generic.Evaluation
import YesMetaZFC.Model.Forcing.Internal.Extension.ZF
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # N[G] 的内部可数性

地模型的可数名称集合经规范嵌入仍可数，实际求值图满射到 N[G]。按原像的最小
自然数编号构造反向单射，故此处只需 ZF，不把满射的任意截面当成选择函数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R z U
local notation "J" => kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
include O hZF hU

/-- 地集合的任意序数大小界都传到其名称值集合；只需 ZF 的最小原像选择。 -/
theorem ng_cardinal_bound_l {b N κ} {Y : (E).Domain} (hb : U b) (hκ : M.IsOrdinal κ)
    (hN : M.CardinalLessOrEqual I N κ) (hY : ∀ x, x ∈ Y ↔ Ng_mem_d M B R z U N x)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ s, M.mem s a ∧ e s = y)
    (hv : ∀ a t, Check_d M b a t → Qval_d M B R z U t (e a)) :
    (E).CardinalLessOrEqual J Y (e κ) := by
  obtain ⟨S, hS⟩ := ng_source_exists_l M hZF B N
  obtain ⟨F, hF, hs⟩ := ng_surjection_l O hZF hU (hU.proper b hb).1 hS hY e hi he hv
  obtain ⟨G, hG⟩ := ZF.exists_inclusionInjection hZF I (show M.MemberSubset S N from fun s hs => ((hS s).mp hs).1)
  obtain ⟨K, hK⟩ := hN
  obtain ⟨L, hL⟩ := ZF.exists_compositionInjection hZF I hG hK
  exact ZF.ordinal_image_bound_l J (preserves_zf_l O hZF hU)
    (image_ordinal_l e hi he hZF.1 (internal_foundation_l O hZF hU) hκ)
    ⟨e L, image_injection_l (hEN := extension_ext_l O hZF hU) (hPN := internal_pair_l O hZF hU) e hi he hL⟩ hF hs

/-- 给定内部可数 N，直接返回扩张内实际可数的 N[G]，并同时给出内部 ω 的规范像。 -/
theorem ng_countable_l {N ω} (hω : M.IsOmega ω) (hN : M.CardinalLessOrEqual I N ω) :
    ∃ Y w : (E).Domain, (∀ x, x ∈ Y ↔ Ng_mem_d M B R z U N x) ∧
      (E).IsOmega w ∧ (E).CardinalLessOrEqual J Y w := by
  obtain ⟨b, hb⟩ := hU.inhabited
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hZF hU hb
  obtain ⟨Y, hY⟩ := ng_set_l O hZF hU N
  have hE := preserves_zf_l O hZF hU
  have hωE : (E).IsOmega (e ω) := image_omega_l (hEN := hE.1) e hi he hZF
    (internal_foundation_l O hZF hU) hω (fun T => KP.difference_exists_d (ZF.modelsKP hE) T (e ω))
  exact ⟨Y, e ω, hY, hωE, ng_cardinal_bound_l O hZF hU hb (hω.isOrdinal hZF) hN hY e hi he hv⟩

end YesMetaZFC.Model.Forcing.Internal
