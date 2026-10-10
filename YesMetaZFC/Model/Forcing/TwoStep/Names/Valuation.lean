import YesMetaZFC.Model.Forcing.TwoStep.Names.Interpretation
import YesMetaZFC.Model.Forcing.TwoStep.Generic.Recovery

/-! # 二步名称在复合泛型扩张中的实际求值

内部名称先转换，再在两个泛型商中依次解释。求值总且唯一，其成员方程使用
组合滤子接受的原二步条目；此处的输入仍为原名称，商类无关性另须等号传输。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def Curry_val_d (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) (B R z C : M.Domain)
    (U : M.Domain → Prop) (Q D : (extension_l M hZF B R z U).Domain)
    (H : (extension_l M hZF B R z U).Domain → Prop) (x : M.Domain)
    (v : Name_quot_l (extension_l M hZF B R z U) Q D Q H) : Prop :=
  ∃ t a, Curry_d M B C x t ∧ Qval_d M B R z U t a ∧
    Qval_d (extension_l M hZF B R z U) Q D Q H a v

variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
variable {Q D : (extension_l M hZF B R z U).Domain}
  {H : (extension_l M hZF B R z U).Domain → Prop}
local notation "N" => extension_l E (preserves_zf_l O hZF hU) Q D Q H

/-- 转换图唯一、两次商求值唯一，故原名称的复合值唯一。 -/
theorem curry_value_unique_l {x} {v w : Name_quot_l E Q D Q H}
    (hv : Curry_val_d M hZF B R z C U Q D H x v)
    (hw : Curry_val_d M hZF B R z C U Q D H x w) : v = w := by
  obtain ⟨t, a, ht, ha, hv⟩ := hv
  obtain ⟨s, d, hs, hd, hw⟩ := hw
  have he := curry_unique_l M hZF.1 (check_ind_l M hZF) B C x t s ht hs
  subst s
  have he := qval_unique_l ha hd
  subst d
  exact qval_unique_l hv hw

include O hU
/-- 对任意内部二步名称，一次取得双重解释的值及其唯一性。 -/
theorem curry_value_l (h : Two_step_d M B R z b A T W C S) (hA : Qval_d M B R z U A Q)
    {x} (hx : Name_d M C x) : ∃ v : (N).Domain,
      Curry_val_d M hZF B R z C U Q D H x v ∧
      ∀ w, Curry_val_d M hZF B R z C U Q D H x w → w = v := by
  obtain ⟨t, ht, htN, _⟩ := two_step_curry_l M hZF h x
  obtain ⟨a, ha⟩ := name_value_l (R := R) (z := z) (U := U) htN
  obtain ⟨v, hv⟩ := name_value_l (R := D) (z := Q) (U := H)
    (curry_second_name_l O hZF hU h hx ht hA ha)
  have hval : Curry_val_d M hZF B R z C U Q D H x v := ⟨t, a, ht, ha, hv⟩
  exact ⟨v, hval, fun w hw => curry_value_unique_l hZF hw hval⟩

variable (L : Cond_order_d (extension_l M hZF B R z U) Q D Q)
  (hH : Generic_d (extension_l M hZF B R z U) Q D Q H)
include L hH

/-- 两次求值的成员恰由组合滤子接受的原二步条目给出。 -/
theorem curry_value_mem_l (h : Two_step_d M B R z b A T W C S)
    {x} {v w : (N).Domain} (hv : Curry_val_d M hZF B R z C U Q D H x v) :
    w ∈ v ↔ ∃ a c, Entry_d M a c x ∧ Compose_generic_d M B R z C U H c ∧
      Curry_val_d M hZF B R z C U Q D H a w := by
  obtain ⟨t, y, ht, hy, hv⟩ := hv
  constructor
  · intro hw
    obtain ⟨a, q, haq, hq, haw⟩ := (qval_mem_l L (preserves_zf_l O hZF hU) hH hv).mp hw
    obtain ⟨s, c, u, p, d, hsc, hc, hcp, hp, hsu, hua, hdq⟩ :=
      (curry_val_entry_l O hZF hU h ht hy).mp haq
    exact ⟨s, c, hsc, ⟨hc, p, d, q, hcp, hp, hdq, hq⟩, u, a, hsu, hua, haw⟩
  · rintro ⟨s, c, hsc, ⟨hc, p, d, q, hcp, hp, hdq, hq⟩, u, a, hsu, hua, haw⟩
    exact (qval_mem_l L (preserves_zf_l O hZF hU) hH hv).mpr ⟨a, q,
      (curry_val_entry_l O hZF hU h ht hy).mpr ⟨s, c, u, p, d, hsc, hc, hcp, hp, hsu, hua, hdq⟩, hq, haw⟩

/-- 在 Prop 内装配所有二步名称的求值函数，保留精确成员方程；不选择商代表。 -/
theorem two_step_valuation_l (h : Two_step_d M B R z b A T W C S) (hA : Qval_d M B R z U A Q) :
    ∃ e : {x // Name_d M C x} → (N).Domain,
      (∀ x, Curry_val_d M hZF B R z C U Q D H x.1 (e x)) ∧
      ∀ x w, w ∈ e x ↔ ∃ a : {a // Name_d M C a}, ∃ c,
        Entry_d M a.1 c x.1 ∧ Compose_generic_d M B R z C U H c ∧ e a = w := by
  have total (x : {x // Name_d M C x}) : ∃ v : (N).Domain,
      Curry_val_d M hZF B R z C U Q D H x.1 v := by
    obtain ⟨v, hv, _⟩ := curry_value_l O hZF hU h hA x.2
    exact ⟨v, hv⟩
  obtain ⟨e, he⟩ := Classical.axiomOfChoice total
  refine ⟨e, he, fun x w => (curry_value_mem_l O hZF hU L hH h (he x)).trans ?_⟩
  constructor
  · rintro ⟨a, c, hac, hc, ha⟩
    let s : {a // Name_d M C a} := ⟨a, (name_entry_l M x.2 hac).1⟩
    exact ⟨s, c, hac, hc, curry_value_unique_l hZF (he s) ha⟩
  · rintro ⟨a, c, hac, hc, ha⟩
    exact ⟨a.1, c, hac, hc, ha ▸ he a⟩

end YesMetaZFC.Model.Forcing.Internal
