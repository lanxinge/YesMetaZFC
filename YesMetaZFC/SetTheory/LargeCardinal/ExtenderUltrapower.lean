import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCollapse

/-! # 相对测度族施加到实际源模型

先构造全部源内部代表的初等定向极限。此构造不需要良基性；跨模型施加
只消费子集一致性，良基性可随后由共同纤维或向良基模型的复制嵌入取得。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_ultrapower_l (hZFC : M.Models ZFC) {ω κ K L X R F : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (hωL : M.MemberSubset ω L) : ∃ J O Z A p T S q c C V,
      Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z A p T S ∧ Di_limit_d A p T S q C V ∧
      Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C V ∧
      Di_elementary_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω O A p T S := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨J, O, Z, A, p, T, S, h⟩ := ep_system_exists_l hZFC source hF coherent hωL
  obtain ⟨z, hz, hzω⟩ := source.omega.1.1
  have hzfn : Fn0_d z L z := ⟨fun r hr => (hz r hr).elim, fun r hr => (hz r hr).elim, fun r hr => (hz r hr).elim⟩
  have hzJ := (h.indices z).mpr ⟨z, hzω, hzfn, fun i j x hi _ => hi.elim fun r hr => (hz r hr.2).elim⟩
  obtain ⟨Q, hZ, models⟩ := h.models
  obtain ⟨d, _, hzd⟩ := hZ.2.1 z hzJ
  obtain ⟨_, _, _, _, _, D, W, _, _, _, _, _, hm⟩ := models z d hzd
  obtain ⟨B, hBD⟩ := hm.code.2.1
  obtain ⟨u, hu⟩ := I.total z B
  have huA := (h.nodes u).mpr ⟨z, B, hu, d, D, W, hzd, hm.code.1, hBD⟩
  obtain ⟨c, q, C, V, limit, model⟩ := di_model_exists_l hZF h.diagram ⟨u, huA⟩
  exact ⟨J, O, Z, A, p, T, S, q, c, C, V, h, limit, model, h.toEp_graph_d.elementary_l hZFC source hF coherent⟩

/-- 同一扩展器图在子集一致的另一源上生成实际完整初等超幂。 -/
theorem ep_apply_l (hZFC : M.Models ZFC) {ω κ K L N X R F : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (owner : Em_source_d ω κ L N F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L N F)
    (agree : Ea_agree_d ω κ N X) (hωL : M.MemberSubset ω L) : ∃ J O Z A p T S q c C V,
      Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z A p T S ∧ Di_limit_d A p T S q C V ∧
      Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C V ∧
      Di_elementary_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω O A p T S :=
  ep_ultrapower_l hZFC source (owner.transfer_l agree) (coherent.transfer_l (ZFC.models_zf_l hZFC) agree) hωL

end YesMetaZFC.SetTheory.LargeCardinal
