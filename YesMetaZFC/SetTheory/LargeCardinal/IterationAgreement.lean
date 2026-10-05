import YesMetaZFC.SetTheory.LargeCardinal.IterationApply
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSuccessor

/-! # 迭代树后继与所属模型超幂之间的一致性

树前驱与所属模型分别施加同一个扩展器。两张实际超幂边的坍塌目标在
包含支撑端点的全部有限幂子集上一致；自动入口绑定新加入树中的同一个模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem it_ultra_agree_l (hZFC : M.Models ZFC)
    {ω κ L F K K' X R Y S c c' d d' j j' N V N' V' : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (source' : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K' Y S) (agree : Ea_agree_d ω κ X Y)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (atoms : Ea_atoms_d ω κ L F) (normal : En_source_d ω κ L X F)
    (hκ : M.IsOrdinal κ) (hL : M.IsOrdinal L) (hωL : M.MemberSubset ω L)
    (mx : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (my : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c' Y S)
    (nx : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N V)
    (ny : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d' N' V')
    (hN : M.TransitiveSet N) (hN' : M.TransitiveSet N')
    (u : It_ultra_d (ZFC.models_zf_l hZFC) ω κ L F c d j)
    (v : It_ultra_d (ZFC.models_zf_l hZFC) ω κ L F c' d' j') :
    M.mem L N ∧ M.mem L N' ∧ Ea_agree_d ω L N N' := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨X₀, R₀, N₀, V₀, J, O, Z, A, p, T, B, q, b, C, W, _, e,
    mx₀, nx₀, hs, limit, model, wc, bij, he, _, _, _, _⟩ := u
  obtain ⟨Y₀, S₀, N₁, V₁, J', O', Z', A', p', T', B', q', b', C', W', _, e',
    my₀, ny₀, hs', limit', model', wc', bij', he', _, _, _, _⟩ := v
  obtain ⟨eX, eR⟩ := smdl_unique_l I mx₀.1 mx.1
  obtain ⟨eY, eS⟩ := smdl_unique_l I my₀.1 my.1
  obtain ⟨eN, eV⟩ := smdl_unique_l I nx₀.1 nx.1
  obtain ⟨eN', eV'⟩ := smdl_unique_l I ny₀.1 ny.1
  subst X₀ R₀ Y₀ S₀ N₀ V₀ N₁ V₁
  have range : M.IsRangeOf I N e := fun x => ⟨fun hx => (bij.2 x hx).imp fun _ hh => hh.2,
    fun ⟨_, hx⟩ => bij.1.1.output_mem_of_pairMember hx⟩
  have range' : M.IsRangeOf I N' e' := fun x => ⟨fun hx => (bij'.2 x hx).imp fun _ hh => hh.2,
    fun ⟨_, hx⟩ => bij'.1.1.output_mem_of_pairMember hx⟩
  exact ep_successor_agree_l hZFC source source' agree family coherent atoms normal hκ hL hωL
    hs limit model hN nx he range wc hs' limit' model' hN' ny he' range' wc'

theorem it_short_apply_agree_l (hZFC : M.Models ZFC)
    {ω c₀ α ξ T Q G E k c d X R Y S κ L F : M.Domain}
    (tree : It_tree_d (ZFC.models_zf_l hZFC) ω c₀ α T Q G E) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q)
    (owner : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (parent : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d Y S)
    (localExt : It_local_d ω X κ L F) (agree : Ea_agree_d ω κ X Y) (hκY : M.mem κ Y)
    (ex : Ex_short_d (ZFC.models_zf_l hZFC) ω κ L F) :
    ∃ β U Q' G' E' b j b' j' N V N' V', It_tree_d (ZFC.models_zf_l hZFC) ω c₀ β U Q' G' E' ∧
      It_extension_d α ξ k T Q G E β U Q' G' E' ∧ Rd_entry_d α b Q' ∧ It_map_d G' k α j ∧
      It_ultra_d (ZFC.models_zf_l hZFC) ω κ L F d b j ∧ It_ultra_d (ZFC.models_zf_l hZFC) ω κ L F c b' j' ∧
      Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) b N V ∧
      Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) b' N' V' ∧
      Ea_agree_d ω L N N' ∧ ∀ μ, (M.mem μ L ∨ μ = L) → M.MemberSubset ω μ →
        ∃ K K', Ep_source_d (ZFC.models_zf_l hZFC) ω μ K N V ∧ Ep_source_d (ZFC.models_zf_l hZFC) ω μ K' N' V' := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨β, U, Q', G', E', b, j, _, h', extension, hb, edge, ultra, _⟩ :=
    it_short_apply_l hZFC tree hα hc hd owner parent localExt agree hκY ex
  obtain ⟨X₀, R₀, K₀, code, ready⟩ := tree.sources ξ c hc
  obtain ⟨eX, eR⟩ := smdl_unique_l I code.1 owner.1
  subst X₀ R₀
  obtain ⟨_, hκX, _⟩ := localExt
  have hωκ := ex.critical.1.transitive ω ex.uncountable
  obtain ⟨K, source⟩ := ready.rebase_l hZF hκX hωκ
  obtain ⟨b', j', ultra', ready'⟩ := it_ultra_exists_l hZF source owner (ex.limit_l hZFC source)
  obtain ⟨N', V', K', code', next'⟩ := ready'
  obtain ⟨N, V, K₁, code₁, next⟩ := h'.sources α b hb
  obtain ⟨Y₀, S₀, K₂, code₂, ready₂⟩ := tree.sources k d hd
  obtain ⟨eY, eS⟩ := smdl_unique_l I code₂.1 parent.1
  subst Y₀ S₀
  obtain ⟨K₃, source₂⟩ := ready₂.rebase_l hZF hκY hωκ
  obtain ⟨hLN, hLN', common⟩ := it_ultra_agree_l hZFC source₂ source
    (fun n D A hn hD hA => (agree n D A hn hD hA).symm) (ex.measures.source_l hZF Y) (ex.coherent.source_l I Y)
    ex.atoms (ex.normal.source_l Y) ex.critical.1 ex.length
    (fun x hx => ex.length.transitive κ ex.above x (hωκ x hx)) parent owner code₁ code'
    next.transitive next'.transitive ultra ultra'
  refine ⟨β, U, Q', G', E', b, j, b', j', N, V, N', V', h', extension, hb, edge, ultra, ultra', code₁, code', common, ?_⟩
  intro μ hμ hωμ
  obtain ⟨K, hk⟩ := next.rebase_l hZF (hμ.elim (next.transitive L hLN μ) (fun eq => eq.symm ▸ hLN)) hωμ
  obtain ⟨K', hk'⟩ := next'.rebase_l hZF (hμ.elim (next'.transitive L hLN' μ) (fun eq => eq.symm ▸ hLN')) hωμ
  exact ⟨K, K', hk, hk'⟩

end YesMetaZFC.SetTheory.LargeCardinal
