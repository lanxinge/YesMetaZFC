import YesMetaZFC.Model.Forcing.Proper.Generic.Countable
import YesMetaZFC.SetTheory.Hereditary

/-! # 遗传小名称的泛型值仍遗传小

名称的地传递闭包经泛型求值仍为传递集合，且含该名称的值。实际求值满射
保持任意地序数大小界，因而不需要预设 κ 的正则性或基数保持。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R z U
local notation "J" => kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)

theorem hmem_value_l {b κ t} {x : (E).Domain} (hb : U b) (hκ : M.IsOrdinal κ)
    (ht : Hmem_d I κ t) (hx : Qval_d M B R z U t x)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ s, M.mem s a ∧ e s = y)
    (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a)) : Hmem_d J (e κ) x := by
  obtain ⟨T, μ, hT, hμ, ht⟩ := ht
  obtain ⟨Y, hY⟩ := ng_set_l O hZF hU T
  exact ZF.hmem_of_transitive_l J (preserves_zf_l O hZF hU)
    (ng_transitive_l O hZF hU hT.1 hY) ((hY x).mpr ⟨t, hT.2.1, hx⟩)
    ((image_member_l e hi he).mpr hμ)
    (ng_cardinal_bound_l O hZF hU hb (hκ.mem hμ) ht hY e hi he hv)

end YesMetaZFC.Model.Forcing.Internal
