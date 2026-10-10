import YesMetaZFC.Model.Forcing.Proper.Elementary.Inverse
import YesMetaZFC.Model.Forcing.Proper.Generic.Member
import YesMetaZFC.Model.Forcing.Proper.Generic.Hull
import YesMetaZFC.Model.Forcing.TwoStep.Generic.DenseImage

/-! # 二步稠密集在 N[G] 中的真实见证

稠密集的第二阶段名称就是其坐标反向图。初等性把该图取到 N，主条件下的
原子成员见证再把 N[G] 中的像点还原为 D∩N 的实际二步条件。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain}

theorem two_step_inverse_name_l (hZF : M.Models ZF) (h : Two_step_d M B R z b A T W C S)
    {D F} (hD : M.MemberSubset D C) (hF : Inv_graph_d M D F) : Name_d M B F := by
  apply (name_unfold_l M (name_ops_l M hZF) B F).mpr
  intro v hv
  obtain ⟨a, p, hvap⟩ := hF.1 v hv
  obtain ⟨x, hx, hxD⟩ := (hF.2 a p).mp ⟨v, hvap, hv⟩
  have hc := (two_step_mem_l h hx).mp (hD x hxD)
  exact ⟨a, p, hvap, hc.2.1.1, W, hc.1, h.closed⟩

theorem two_step_inverse_value_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {U}
    (hU : Generic_d M B R z U) {D F} (hD : M.MemberSubset D C) (hF : Inv_graph_d M D F)
    {Y : (extension_l M hZF B R z U).Domain} (hY : Qval_d M B R z U F Y) :
    ∀ y, y ∈ Y ↔ ∃ x p s, M.mem x C ∧ M.mem x D ∧ U p ∧ KPair_d M x p s ∧ Qval_d M B R z U s y := by
  intro y
  constructor
  · intro hy
    obtain ⟨s, p, hsp, hp, hs⟩ := (qval_mem_l O hZF hU hY).mp hy
    obtain ⟨x, hx, hxD⟩ := (hF.2 s p).mp hsp
    exact ⟨x, p, s, hD x hxD, hxD, hp, hx, hs⟩
  · rintro ⟨x, p, s, _, hxD, hp, hx, hs⟩
    exact (qval_mem_l O hZF hU hY).mpr ⟨s, p, (hF.2 s p).mpr ⟨x, hx, hxD⟩, hp, hs⟩

theorem two_step_image_dense_set_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {U}
    (hU : Generic_d M B R z U) (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C) (hb : U b)
    {Q V Y : (extension_l M hZF B R z U).Domain} (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T V)
    {D} (hD : Dense_set_d M C S C D)
    (hY : ∀ y, y ∈ Y ↔ ∃ x p s, M.mem x C ∧ M.mem x D ∧ U p ∧ KPair_d M x p s ∧ Qval_d M B R z U s y) :
    Dense_set_d (extension_l M hZF B R z U) Q V Q Y := by
  let E := extension_l M hZF B R z U
  have ne {x : E.Domain} (hx : x ∈ Q) : x ≠ Q := fun he => KP.mem_irrefl_d
    (ZF.modelsKP (preserves_zf_l O hZF hU)) Q (he ▸ hx)
  refine ⟨?_, fun y hy _ => ?_⟩
  · intro y hy
    obtain ⟨x, p, s, hx, _, hp, hxp, hs⟩ := (hY y).mp hy
    have hyQ := (two_step_fiber_l O hZF hU h hb hA y).mpr ⟨x, p, s, hx, hp, hxp, hs⟩
    exact ⟨hyQ, ne hyQ⟩
  · obtain ⟨x, p, s, hx, hp, hxp, hs⟩ := (two_step_fiber_l O hZF hU h hb hA y).mp hy
    have hyy := (rel_force_truth_l O hZF hU hs hs hT).mp
      ⟨p, hp, ((two_step_le_l h hx hx hxp hxp).mp (L.refl x hx)).2⟩
    obtain ⟨v, hv, hvy, hvY⟩ := two_step_image_dense_l O hZF hU h L hA hT hY hx hxp hp hs
      (fun r hr => hD.2 r hr.1 hr.2.1) y hy hyy
    exact ⟨v, ⟨hv, ne hv, hvy⟩, hvY⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- N[G] 中的稠密像点，来自 D∩N 的条件且其首坐标仍在原泛型中。 -/
theorem two_step_image_pick_l {ω χ H c J d N K D F q} (O : Cond_order_d M B R z) {U}
    (hU : Generic_d M B R z U) (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ)
    (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hJ : ∀ x y, M.PairMember I x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hS : Ssub_d I c d H J N K) (he : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hz : M.mem z N)
    (hF : Inv_graph_d M D F) (hFN : M.mem F N) (hm : Mstr_d M B R z N q) (hq : U q)
    {Z Y y : (extension_l M hZF B R z U).Domain} (hZ : ∀ x, x ∈ Z ↔ Ng_mem_d M B R z U N x)
    (hY : Qval_d M B R z U F Y) (hyZ : y ∈ Z) (hyY : y ∈ Y) :
    ∃ x p s, M.mem x N ∧ M.mem x D ∧ U p ∧ KPair_d M x p s ∧ Qval_d M B R z U s y := by
  obtain ⟨t, htN, hty⟩ := (hZ y).mp hyZ
  obtain ⟨s, p, hsN, hpN, hsp, hp, hs⟩ := ng_member_pick_l hZFC hω hχ hωχ hH hJ O hU
    hS he hB hR hz htN hFN hm hq hty hY hyY
  obtain ⟨x, hx, hxD⟩ := (hF.2 s p).mp hsp
  exact ⟨x, p, s, selem_kpair_closed_l hZFC hω hχ hωχ hH hJ hS he hpN hsN hx, hxD, hp, hx, hs⟩

end YesMetaZFC.Model.Forcing.Internal
