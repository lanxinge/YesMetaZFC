import YesMetaZFC.SetTheory.CumulativeRelative
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCoordinates

/-! # 原强嵌入的像历史在已覆盖秩层处取真实值

传输一个源中实际递归历史的全称有界证书，而非假定目标的内部幂集就是
背景幂集。原强性的秩覆盖使指定阶段的全部子集可见，逐层比较消去相对性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ed_hierarchy_l (hZF : M.Models ZF) {ω δ X A Y B j κ k U : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hκ : M.mem κ δ) (hk : Rd_entry_d κ k j) (hU : V_d (kp_pair_l (ZF.modelsKP hZF)) κ U) :
    ∃ H F U' H' F', M.mem H X ∧ M.mem F X ∧ Rd_entry_d U U' j ∧ Rd_entry_d H H' j ∧ Rd_entry_d F F' j ∧
      (∀ t, Vc_d κ U H F t) ∧ (∀ α V, Rd_entry_d α V F → V_d (kp_pair_l (ZF.modelsKP hZF)) α V) ∧
      (∀ t, M.mem t Y → Vc_d k U' H' F' t) ∧
      ∀ ν V, M.mem ν k → V_d (kp_pair_l (ZF.modelsKP hZF)) ν V → M.MemberSubset V Y → Rd_entry_d ν V F' := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := ZF.v_transitive_l I hZF hX
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  obtain ⟨H, F, hHX, hFX, cert, history⟩ := vr_source_l hZF hX hδ hκ hU
  obtain ⟨U', hUY, hjU⟩ := hj.2.2 U (ZF.v_mem_l I hZF hU hX hκ)
  obtain ⟨H', hHY, hjH⟩ := hj.2.2 H hHX
  obtain ⟨F', _, hjF⟩ := hj.2.2 F hFX
  let φ : Formula 1 5 := vc_matrix_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  have tr := spred_forall_delta_l I hZF hω h ht hY φ (by simp -implicitDefEqProofs [φ]) (vc_matrix_delta_l ..)
    ⟨Fin.cases F (Fin.cases H (Fin.cases U (fun _ => κ))), fun _ => κ⟩
    ⟨Fin.cases F' (Fin.cases H' (Fin.cases U' (fun _ => k))), fun _ => k⟩
    (Fin.cases hjF (Fin.cases hjH (Fin.cases hjU (fun _ => hk))))
  simp only [φ, vc_matrix_sat_l (ZF.modelsKP hZF)] at tr
  have target := tr.mp (fun t _ => cert t)
  have fn := (target U' hUY).2.1
  have ko := (target U' hUY).1
  refine ⟨H, F, U', H', F', hHX, hFX, hjU, hjH, hjF, cert, history, target, fun ν V hν hV cover => ?_⟩
  obtain ⟨W, hW, hνW⟩ := fn.2.1 ν hν
  have eq := vr_compare_l hZF hY (hY H' hHY) fn (ko.transitive ν hν) (hY H' hHY W hW) hV cover
    (fun β hβ T hβT t ht => (target t ht).2.2.1 β (ko.transitive ν hν β hβ) T (fn.bound_l hβT).2 hβT)
    (fun t ht => (target t ht).2.2.1 ν hν W hW hνW)
  exact eq ▸ hνW

end YesMetaZFC.SetTheory.LargeCardinal
