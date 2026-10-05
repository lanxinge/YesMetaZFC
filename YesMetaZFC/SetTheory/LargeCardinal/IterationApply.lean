import YesMetaZFC.SetTheory.LargeCardinal.IterationRoot

/-! # 实际扩展器施加接入迭代树的后继构造

一般入口消费已经构造的源内部良基超幂，自动取得常值边、坍塌和新源。
短扩展器入口再以共同纤维自动产生这个超幂；所属判断始终保留模型内语义。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem it_apply_l (hZF : M.Models ZF)
    {ω c₀ α ξ T Q G E k c d X R Y S κ K L F : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q)
    (owner : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (parent : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (localExt : It_local_d ω X κ L F) (agree : Ea_agree_d ω κ X Y)
    (source : Ep_source_d hZF ω κ K Y S) (built : Ep_limit_d hZF ω κ L Y S F) :
    ∃ β U Q' G' E' b j p, It_tree_d hZF ω c₀ β U Q' G' E' ∧ It_extension_d α ξ k T Q G E β U Q' G' E' ∧
      Rd_entry_d α b Q' ∧ It_map_d G' k α j ∧ It_ultra_d hZF ω κ L F d b j ∧
      It_payload_d p κ L F ∧ Rd_entry_d ξ p E' := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨b, j, ultra, ready⟩ := it_ultra_exists_l hZF source parent built
  obtain ⟨N, V, K', code, next⟩ := ready
  obtain ⟨r, hr⟩ := I.total L F
  obtain ⟨p, hp⟩ := I.total κ r
  have payload : It_payload_d p κ L F := ⟨r, hp, hr⟩
  have step : It_active_d hZF ω c d b j p := ⟨κ, L, F, X, R, Y, S, payload, owner, parent, localExt, agree, ultra⟩
  obtain ⟨β, U, Q', G', E', hβ, h', us, qs, gs, es, edge⟩ := it_tree_extend_l hZF tree hα hc hd parent.1 code.1
    (ultra.elementary_l hZF parent.1 code.1) ⟨N, V, K', code, next⟩ (Or.inr step)
  refine ⟨β, U, Q', G', E', b, j, p, h', ⟨hβ, us, fun i a hi => (qs i a).mpr (Or.inl hi), gs,
    fun i a hi => (es i a).mpr (Or.inl hi), fun i a hi => ?_⟩,
    (qs α b).mpr (Or.inr ⟨rfl, rfl⟩), edge, ultra, payload, (es ξ p).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  exact (es i a).trans ⟨fun h => h.elim id (fun h => (hi h.1).elim), Or.inl⟩

/-- 可数共同纤维实际生成所需良基性，调用者无需提供超幂或后继模型。 -/
theorem it_short_apply_l (hZFC : M.Models ZFC)
    {ω c₀ α ξ T Q G E k c d X R Y S κ L F : M.Domain}
    (tree : It_tree_d (ZFC.models_zf_l hZFC) ω c₀ α T Q G E) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q)
    (owner : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (parent : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d Y S)
    (localExt : It_local_d ω X κ L F) (agree : Ea_agree_d ω κ X Y) (hκY : M.mem κ Y)
    (ex : Ex_short_d (ZFC.models_zf_l hZFC) ω κ L F) :
    ∃ β U Q' G' E' b j p, It_tree_d (ZFC.models_zf_l hZFC) ω c₀ β U Q' G' E' ∧ It_extension_d α ξ k T Q G E β U Q' G' E' ∧
      Rd_entry_d α b Q' ∧ It_map_d G' k α j ∧ It_ultra_d (ZFC.models_zf_l hZFC) ω κ L F d b j ∧
      It_payload_d p κ L F ∧ Rd_entry_d ξ p E' := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Y', S', K₀, code, ready⟩ := tree.sources k d hd
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I code.1 parent.1
  obtain ⟨K, source⟩ := ready.rebase_l hZF hκY (ex.critical.1.transitive ω ex.uncountable)
  exact it_apply_l hZF tree hα hc hd owner parent localExt agree source (ex.limit_l hZFC source)

end YesMetaZFC.SetTheory.LargeCardinal
