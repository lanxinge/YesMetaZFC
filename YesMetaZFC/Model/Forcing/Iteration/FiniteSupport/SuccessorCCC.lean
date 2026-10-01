import YesMetaZFC.Model.Forcing.TwoStep.CCC.Preservation
import YesMetaZFC.Model.Forcing.Stage.CCC
import YesMetaZFC.Model.Forcing.Iteration.Stage.Basic

/-! # 名称后继的坐标实现保存 CCC -/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

theorem row_next_ccc_l (hZFC : M.Models ZFC) {ω α β B R e A T t D V}
    (hω : M.IsOmega ω) (hs : Row_stage_d M α B R e) (hβ : M.SuccessorOf β α)
    (hc : Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R B)
    (hT : Name_d M B T)
    (hP : Forces_d M B R B (preord_m (.bound 0) (.bound 1)) (ord_env_l M A T) e)
    (hC : Forces_d M B R B (ccc_exists_m (.bound 0) (.bound 1)) (ord_env_l M A T) e)
    (h : Row_next_d M α B R e A T t D V) :
    Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω D V D := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨W, C, S, _, hStep, hRep⟩ := h
  have L := two_step_order_l hs.order hZF hStep hT hP
  obtain ⟨D', V', F, hD', hF, hBij, hGraph, hV', _, hReg, _⟩ := two_step_rows_l hZF hStep L hβ hs.rows
  have hRep' : Row_repr_d M α t C S D' V' := ⟨hD', hGraph, fun p q => (hV' p q).trans
    ⟨fun ⟨c, d, hc, hd, hcd⟩ => ⟨c, d, ((hF c p).mp hc).1, ((hF d q).mp hd).1,
      ((hF c p).mp hc).2, ((hF d q).mp hd).2, hcd⟩,
      fun ⟨c, d, hc, hd, hcp, hdq, hcd⟩ => ⟨c, d, (hF c p).mpr ⟨hc, hcp⟩, (hF d q).mpr ⟨hd, hdq⟩, hcd⟩⟩⟩
  obtain ⟨heD, heV⟩ := row_repr_unique_l M hZF.1 hRep' hRep
  subst D'
  subst V'
  exact reg_surj_ccc_l hZF (two_step_ccc_l hs.order hZFC hω hc hStep hT hP hC) hReg
    (fun q hq _ => (hBij.2 q hq).elim fun p hp => ⟨p, hp.2⟩)

end YesMetaZFC.Model.Forcing.Internal
