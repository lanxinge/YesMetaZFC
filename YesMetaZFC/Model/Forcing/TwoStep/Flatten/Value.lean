import YesMetaZFC.Model.Forcing.TwoStep.Flatten.Round
import YesMetaZFC.Model.Forcing.TwoStep.Names.Valuation

/-! # 任意第二阶段名称由摊平名称实现

先对首阶段名称作实际摊平，再消费已证明的全部条件等号。第二阶段取任意泛型，
便得到原名称双重值的精确还原；关系规范化只使用条件域内的逐边对应。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain} {U : M.Domain → Prop}

theorem flat_value_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
    (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C) (hb : U b)
    {Q D J : (extension_l M hZF B R z U).Domain} {H : (extension_l M hZF B R z U).Domain → Prop}
    (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T D)
    (hJ : ∀ p q, p ∈ Q → q ∈ Q → (Entry_d (extension_l M hZF B R z U) p q D ↔ Entry_d (extension_l M hZF B R z U) p q J))
    (K : Cond_order_d (extension_l M hZF B R z U) Q J Q) (hH : Generic_d (extension_l M hZF B R z U) Q J Q H)
    {x f} {a : (extension_l M hZF B R z U).Domain} {v}
    (hf : Flat_d M B R z C x f) (hx : Qval_d M B R z U x a)
    (ha : Qval_d (extension_l M hZF B R z U) Q J Q H a v) : Curry_val_d M hZF B R z C U Q J H f v := by
  have hEN := preserves_zf_l O hZF hU
  obtain ⟨t, ht, htN, _⟩ := two_step_curry_l M hZF h f
  obtain ⟨d, htd⟩ := name_value_l (R := R) (z := z) (U := U) htN
  have hd := curry_second_name_l O hZF hU h (flat_name_l M hZF hf) ht hA htd
  obtain ⟨w, hdw⟩ := name_value_l (R := J) (z := Q) (U := H) hd
  obtain ⟨q, hq⟩ := hH.inhabited
  have he := flat_round_l O hZF h L hU hb hA hT hf ht hx htd (qval_name_l ha) q (hH.proper q hq).1
  have he' := (eq_force_order_l hJ hEN (qval_name_l ha) hd).mp he
  have hvw := (qval_eq_l K hEN hH ha hdw).mp ⟨q, hq, he'⟩
  exact ⟨t, d, ht, htd, hvw.symm ▸ hdw⟩

end YesMetaZFC.Model.Forcing.Internal
