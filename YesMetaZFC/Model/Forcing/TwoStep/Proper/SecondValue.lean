import YesMetaZFC.Model.Forcing.TwoStep.Proper.Pull
import YesMetaZFC.Model.Forcing.Proper.Generic.Hull

/-! # 二步主条件的第二坐标在 N[G] 中为主条件

将 N[G] 中的稠密集取一个 N 内名称，使用其实际二步判定集。
二步主性给出的共同加强保留首阶段泛型；稠密性排除永不命中的分支。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) (hU : Generic_d M B R z U)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R z U
include O hU

theorem two_step_master_second_value_l {ω χ H c J d N K v q t} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hJ : ∀ x y, M.PairMember I x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H J N K) (hElem : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hz : M.mem z N) (hC : M.mem C N) (hS : M.mem S N)
    (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hvq : KPair_d M v q t) (hm : Mstr_d M C S C N v) (hq : U q)
    {Q V Z a : (E).Domain} (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T V)
    (ht : Qval_d M B R z U t a) (hZ : ∀ x, x ∈ Z ↔ Ng_mem_d M B R z U N x) :
    Mstr_d E Q V Q Z a := by
  have hv := (two_step_mem_l h hvq).mp hm.1
  have hb := hU.upward q b hq h.base hv.2.1.2.2
  have ha := (qval_mem_forcing_l O hZF hU ht hA).mp ⟨q, hq, hv.2.2⟩
  have ne {x : (E).Domain} (hx : x ∈ Q) : x ≠ Q := fun he =>
    KP.mem_irrefl_d (ZF.modelsKP (preserves_zf_l O hZF hU)) Q (he ▸ hx)
  refine ⟨ha, ne ha, fun Y hYN hY r hr => ?_⟩
  obtain ⟨F, hFN, hF⟩ := (hZ Y).mp hYN
  obtain ⟨D, hDN, hD⟩ := selem_step_dec_l hZFC hω hχ hωχ hH hJ hSub hElem
    hB hR hz hC hS hFN h (qval_name_l hF)
  obtain ⟨x, p, s, hx, hp, hxp, hs⟩ := (two_step_fiber_l O hZF hU h hb hA r).mp hr.1
  have hrr := (rel_force_truth_l O hZF hU hs hs hT).mp
    ⟨p, hp, ((two_step_le_l h hx hx hxp hxp).mp (L.refl x hx)).2⟩
  obtain ⟨j, f, u, hjf, hf, hu, _, hjv⟩ := two_step_common_l O hZF hU h L hA hT
    hx hm.1 hxp hvq hp hq hs ht hr.1 hrr hr.2.2
  obtain ⟨y, k, e, w, hyD, hyN, hke, he, hkj, hky⟩ := two_step_master_meet_l O hZF hU h L
    (qval_name_l hT) hm hDN (step_dec_dense_l L (KP.mem_irrefl_d (ZF.modelsKP hZF) C) hD) hjv hjf hf
  have hyC := hD.1 y hyD
  obtain ⟨l, s', hyl, hsW, hlb, _⟩ := (h.conditions y).mp hyC
  have hkl := (two_step_le_l h hkj.1 hyC hke hyl).mp hky
  have hl := hU.upward e l he hlb.1 hkl.1.2.2
  have hit : Step_hits_d M B R z F y := by
    rcases (hD.2 y hyC).mp hyD with hh | hn
    · exact hh
    · obtain ⟨y', hy', hh⟩ := two_step_hits_possible_l O hZF hU h L hyC hyl hl hA hT hF hY
      exact (hn y' hy' hh).elim
  obtain ⟨l', s'', hyl', hmem⟩ := hit
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hyl hyl'
  obtain ⟨a', hs'⟩ := name_value_l (R := R) (z := z) (U := U) (show Name_d M B s' from ⟨W, hsW, h.closed⟩)
  have ha'Y := (qval_mem_forcing_l O hZF hU hs' hF).mp ⟨l, hl, hmem⟩
  have hsN := (selem_kpair_coords_l I hZF hω (ZF.h_transitive_l I hZF hH) hJ hSub hElem hyN hyl).2
  have ha'Z := (hZ a').mpr ⟨s', hsN, hs'⟩
  have hk := (two_step_mem_l h hke).mp hkj.1
  obtain ⟨v', hw⟩ := name_value_l (R := R) (z := z) (U := U) (show Name_d M B w from ⟨W, hk.1, h.closed⟩)
  have hv' := (qval_mem_forcing_l O hZF hU hw hA).mp ⟨e, he, hk.2.2⟩
  have hvr := (rel_force_truth_l O hZF hU hw hu hT).mp
    ⟨e, he, ((two_step_le_l h hkj.1 hjv.1 hke hjf).mp hkj.2.2).2⟩
  have hva' := (rel_force_truth_l O hZF hU hw hs' hT).mp ⟨e, he, hkl.2⟩
  exact ⟨a', ha'Y, ha'Z, v', ⟨hv', ne hv', hvr⟩, hva'⟩

end YesMetaZFC.Model.Forcing.Internal
