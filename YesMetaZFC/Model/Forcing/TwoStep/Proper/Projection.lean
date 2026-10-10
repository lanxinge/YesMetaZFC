import YesMetaZFC.Model.Forcing.Proper.Elementary.FirstPreimage
import YesMetaZFC.Model.Forcing.TwoStep.Generic.Projection
import YesMetaZFC.Model.Forcing.Proper.Master.Basic

/-! # 二步主条件的首阶段投影

提升 N 中的首阶段稠密集，在二步主条件下遇到其 N 内原像，再读取该条件的
第一坐标。共同加强的首坐标给出原偏序中的预稠密见证。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain}

theorem two_step_master_first_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    {ω χ H c J d N K v q t} (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ)
    (hH : H_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) χ H)
    (hJ : ∀ x y, M.PairMember (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) x y J ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) c d H J N K)
    (hElem : Selem_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω c d)
    (hC : M.mem C N) (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hT : Name_d M B T) (hvq : KPair_d M v q t) (hm : Mstr_d M C S C N v) : Mstr_d M B R z N q := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  have hq := ((two_step_mem_l h hvq).mp hm.1).2.1
  refine ⟨hq.1, hq.2.1, fun D hDN hD r hr => ?_⟩
  obtain ⟨F, hFN, hF⟩ := selem_fst_pull_l hZF hω hχ hH hJ hSub hElem hC hDN
  have hFdense : Dense_set_d M C S C F := by
    refine ⟨fun x hx => ⟨hF.1 x hx, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) C (he ▸ hF.1 x hx)⟩,
      fun x hx _ => ?_⟩
    obtain ⟨p, s, hxp, _, hp, _⟩ := (h.conditions x).mp hx
    obtain ⟨a, hap, haD⟩ := hD.2 p hp.1 hp.2.1
    obtain ⟨y, hya, hyx⟩ := two_step_lift_l O hZF h L hT hx hxp hap
    exact ⟨y, hyx, (hF.2 y hyx.1).mpr ⟨a, s, hya, haD⟩⟩
  obtain ⟨w, hwr, hwv⟩ := two_step_lift_l O hZF h L hT hm.1 hvq hr
  obtain ⟨x, hxF, hxN, j, hjw, hjx⟩ := hm.2.2 F hFN hFdense w hwv
  obtain ⟨p, s, hxp, hpD⟩ := (hF.2 x (hF.1 x hxF)).mp hxF
  have hpN := (selem_kpair_coords_l I hZF hω (ZF.h_transitive_l I hZF hH) hJ hSub hElem hxN hxp).1
  obtain ⟨a, u, hja, _, _, _⟩ := (h.conditions j).mp hjw.1
  have har := ((two_step_le_l h hjw.1 hwv.1 hja hwr).mp hjw.2.2).1
  have hap := ((two_step_le_l h hjw.1 (hF.1 x hxF) hja hxp).mp hjx).1
  exact ⟨p, hpD, hpN, a, har, hap.2.2⟩

end YesMetaZFC.Model.Forcing.Internal
