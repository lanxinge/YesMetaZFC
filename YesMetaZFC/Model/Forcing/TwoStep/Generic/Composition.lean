import YesMetaZFC.Model.Forcing.TwoStep.Generic.Recovery
import YesMetaZFC.Model.Forcing.TwoStep.Generic.DenseImage

/-! # 两阶段泛型的组合与双向恢复

原地模型泛型和其扩张上的泛型自动组成二步泛型。两阶段投影精确恢复输入，
并与 `two_step_recover_l` 一起给出泛型滤子的双向分解。
组合公式为 V = {(p,s) ∈ C : p ∈ U 且 s[U] ∈ H}；全部名称解释均使用原泛型商。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
include O hZF hU

/-- 一次组合两阶段泛型，并精确恢复首阶段与第二阶段输入。 -/
theorem two_step_compose_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hb : U b) {Q D : (E).Domain} (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T D)
    {H : (E).Domain → Prop} (hH : Generic_d E Q D Q H) :
    Generic_d M C S C (Compose_generic_d M B R z C U H) ∧
      (∀ p, First_generic_d M B R (Compose_generic_d M B R z C U H) p ↔ U p) ∧
      ∀ q, H q ↔ Second_generic_d M hZF B R z U (Compose_generic_d M B R z C U H) Q D q := by
  let V := Compose_generic_d M B R z C U H
  have hV : Generic_d M C S C V := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨hx.1, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) C (he ▸ hx.1)⟩
    · obtain ⟨a, ha⟩ := hH.inhabited
      obtain ⟨x, p, s, hx, hp, hxp, hs⟩ := (two_step_fiber_l O hZF hU h hb hA a).mp (hH.proper a ha).1
      exact ⟨x, hx, p, s, a, hxp, hp, hs, ha⟩
    · rintro x y ⟨hx, p, s, a, hxp, hp, hs, ha⟩ hy hxy
      obtain ⟨q, t, hyq, htW, hqb, htm⟩ := (h.conditions y).mp hy
      obtain ⟨hpq, hst⟩ := (two_step_le_l h hx hy hxp hyq).mp hxy
      have hq := hU.upward p q hp hqb.1 hpq.2.2
      obtain ⟨c, ht⟩ := name_value_l (R := R) (z := z) (U := U) (show Name_d M B t from ⟨W, htW, h.closed⟩)
      have hcQ := (qval_mem_forcing_l O hZF hU ht hA).mp ⟨q, hq, htm⟩
      exact ⟨hy, q, t, c, hyq, hq, ht,
        hH.upward a c ha hcQ ((rel_force_truth_l O hZF hU hs ht hT).mp ⟨p, hp, hst⟩)⟩
    · rintro x y ⟨hx, p, s, a, hxp, hp, hs, ha⟩ ⟨hy, q, t, c, hyq, hq, ht, hc⟩
      obtain ⟨v, hv, hva, hvc⟩ := hH.directed a c ha hc
      obtain ⟨j, r, u, hjr, hr, hu, hjx, hjy⟩ := two_step_common_l O hZF hU h L hA hT
        hx hy hxp hyq hp hq hs ht (hH.proper v hv).1 hva hvc
      exact ⟨j, ⟨hjx.1, r, u, v, hjr, hr, hu, hv⟩, hjx.2.2, hjy.2.2⟩
    · rintro x ⟨hx, p, s, a, hxp, hp, hs, ha⟩ D' hd
      obtain ⟨F, hF⟩ := two_step_image_l O hZF hU h D'
      have hFD := two_step_image_dense_l O hZF hU h L hA hT hF hx hxp hp hs hd
      have hE := preserves_zf_l O hZF hU
      obtain ⟨v, hv, hvF⟩ := hH.meets a ha F (fun t ht => by
        obtain ⟨w, hwQ, hwt, hwF⟩ := hFD t ht.1 ht.2.2
        exact ⟨w, ⟨hwQ, fun he => KP.mem_irrefl_d (ZF.modelsKP hE) Q (he ▸ hwQ), hwt⟩, hwF⟩)
      obtain ⟨y, q, t, hy, hyD, hq, hyq, ht⟩ := (hF v).mp hvF
      exact ⟨y, ⟨hy, q, t, v, hyq, hq, ht, hv⟩, hyD⟩
  refine ⟨hV, ?_, ?_⟩
  · intro q
    constructor
    · rintro ⟨hq, x, p, s, ⟨hx, r, t, a, hxr, hr, _, _⟩, hxp, hpq⟩
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hxp hxr
      exact hU.upward p q hr hq hpq
    · intro hq
      obtain ⟨a, ha⟩ := hH.inhabited
      obtain ⟨x, p, s, hx, hp, hxp, hs⟩ := (two_step_fiber_l O hZF hU h hb hA a).mp (hH.proper a ha).1
      obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp hq
      have hr' := hU.proper r hr
      obtain ⟨y, hyr, hyx⟩ := two_step_lift_l O hZF h L (qval_name_l hT) hx hxp ⟨hr'.1, hr'.2, hrp⟩
      exact ⟨(hU.proper q hq).1, y, r, s, ⟨hyx.1, r, s, a, hyr, hr, hs, ha⟩, hyr, hrq⟩
  · intro q
    constructor
    · intro hq
      have hqQ := (hH.proper q hq).1
      obtain ⟨x, p, s, hx, hp, hxp, hs⟩ := (two_step_fiber_l O hZF hU h hb hA q).mp hqQ
      have hqq := (rel_force_truth_l O hZF hU hs hs hT).mp
        ⟨p, hp, ((two_step_le_l h hx hx hxp hxp).mp (L.refl x hx)).2⟩
      exact ⟨hqQ, x, p, s, q, ⟨hx, p, s, q, hxp, hp, hs, hq⟩, hxp, hs, hqq⟩
    · rintro ⟨hqQ, x, p, s, a, ⟨_, r, t, c, hxr, _, ht, hc⟩, hxp, hs, haq⟩
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hxp hxr
      have he := qval_unique_l ht hs
      exact hH.upward a q (he ▸ hc) hqQ haq

end YesMetaZFC.Model.Forcing.Internal
