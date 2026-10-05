import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSuccessor
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLimit

/-! # 后继一致性的自动构造入口

后继证书保留实际源超幂、整个定向极限和传递坍塌，明确把输出模型与
输入扩展器联系起来。短扩展器入口实际生成两侧模型及下一次施加的源证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_successor_d (hZF : M.Models ZF) (ω κ L X R F N S : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ J O Z A p T V q c C W d e,
    Ep_system_d hZF ω κ L X R F J O Z A p T V ∧ Di_limit_d A p T V q C W ∧
    Smdl_d I c C W ∧ Smem_d I d N S ∧ M.TransitiveSet N ∧
    Wc_graph_d C W e ∧ M.IsSetBijectionFromTo I e C N ∧ Smap_d I ω c d C N e

theorem Ex_short_d.successors_l (hZFC : M.Models ZFC) {ω κ L F K K' X R Y R' : M.Domain}
    (ex : Ex_short_d (ZFC.models_zf_l hZFC) ω κ L F)
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (source' : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K' Y R') (agree : Ea_agree_d ω κ X Y) :
    ∃ N S N' S', Ep_successor_d (ZFC.models_zf_l hZFC) ω κ L X R F N S ∧
      Ep_successor_d (ZFC.models_zf_l hZFC) ω κ L Y R' F N' S' ∧
      M.mem L N ∧ M.mem L N' ∧ Ea_agree_d ω L N N' ∧
      ∀ μ, (M.mem μ L ∨ μ = L) → M.MemberSubset ω μ → ∃ K K',
        Ep_source_d (ZFC.models_zf_l hZFC) ω μ K N S ∧ Ep_source_d (ZFC.models_zf_l hZFC) ω μ K' N' S' := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hκ := ex.critical.1.transitive
  have hL := ex.length.transitive
  have hωL : M.MemberSubset ω L := fun x hx => hL κ ex.above x (hκ ω ex.uncountable x hx)
  have family := ex.measures.source_l hZF X
  have coherent := ex.coherent.source_l I X
  obtain ⟨J, O, Z, A, p, T, V, q, c, C, W, h, limit, model, _, _, collapse⟩ := ex.limit_l hZFC source
  obtain ⟨J', O', Z', A', p', T', V', q', c', C', W', h', limit', model', _, _, collapse'⟩ := ex.limit_l hZFC source'
  obtain ⟨_, _, _, N, e, _, d, S, _, _, _, _, hN, wc, bij, code, he, _, _, _, _, _, next⟩ := collapse
  obtain ⟨_, _, _, N', e', _, d', S', _, _, _, _, hN', wc', bij', code', he', _, _, _, _, _, next'⟩ := collapse'
  have range : M.IsRangeOf I N e := fun x => ⟨fun hx => (bij.2 x hx).imp fun E hE => hE.2,
    fun ⟨_, hx⟩ => bij.1.1.output_mem_of_pairMember hx⟩
  have range' : M.IsRangeOf I N' e' := fun x => ⟨fun hx => (bij'.2 x hx).imp fun E hE => hE.2,
    fun ⟨_, hx⟩ => bij'.1.1.output_mem_of_pairMember hx⟩
  obtain ⟨hLN, hLN', common⟩ := ep_successor_agree_l hZFC source source' agree family coherent ex.atoms (ex.normal.source_l X)
    ex.critical.1 ex.length hωL h limit model hN code he range wc h' limit' model' hN' code' he' range' wc'
  refine ⟨N, S, N', S', ⟨J, O, Z, A, p, T, V, q, c, C, W, d, e, h, limit, model, code, hN, wc, bij, he⟩,
    ⟨J', O', Z', A', p', T', V', q', c', C', W', d', e', h', limit', model', code', hN', wc', bij', he'⟩,
    hLN, hLN', common, ?_⟩
  intro μ hμ hωμ
  obtain ⟨K, hk⟩ := next μ (hμ.elim (hN L hLN μ) (fun eq => eq.symm ▸ hLN)) hωμ
  obtain ⟨K', hk'⟩ := next' μ (hμ.elim (hN' L hLN' μ) (fun eq => eq.symm ▸ hLN')) hωμ
  exact ⟨K, K', hk, hk'⟩

end YesMetaZFC.SetTheory.LargeCardinal
