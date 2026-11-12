import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.ActivityRead
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SuccessorApplication

/-! # 实际扩展器施加接入迭代树的后继构造

一般入口把已有实际超幂边和下一步源加入树，保留同一目标及嵌入。
短扩展器入口再以共同纤维自动产生这个超幂；所属判断始终保留模型内语义。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 可数共同纤维实际生成所需良基性，调用者无需提供超幂或后继模型。 -/
theorem it_short_apply_l (hZFC : M.Models ZFC)
    {ω c₀ α ξ T Q G E k c d X R Y S κ L F : M.Domain}
    (tree : It_tree_d (ZFC.models_zf_l hZFC) ω c₀ α T Q G E) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q)
    (owner : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (parent : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d Y S)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (localExt : It_local_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X R κ L F) (agree : Ea_agree_d ω κ X Y) (hκY : M.mem κ Y)
    (ex : Ex_short_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F) :
    ∃ β U Q' G' E' b j p, It_tree_d (ZFC.models_zf_l hZFC) ω c₀ β U Q' G' E' ∧ It_extension_d α ξ k T Q G E β U Q' G' E' ∧
      Rd_entry_d α b Q' ∧ It_map_d G' k α j ∧ It_ultra_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F d b j ∧
      It_payload_d p κ L F ∧ Rd_entry_d ξ p E' := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Y', S', K₀, code, ready⟩ := (tree.sources k d hd).mem_l hZF ⟨Y, S, parent, hY⟩
  obtain ⟨eY, eS⟩ := smdl_unique_l I code.1 parent.1
  subst Y' S'
  obtain ⟨K, source⟩ := ready.rebase_l hκY (ex.critical.1.transitive ω ex.uncountable)
    (sc_ordinal_small_l hZF ready.omega ready.transitive parent ready.theory hκY ex.critical.1)
  obtain ⟨b, j, ultra, next⟩ := it_ultra_exists_l hZF parent (ex.limit_l hZFC source)
  obtain ⟨X', R', _, mx, sx⟩ := (tree.sources ξ c hc).mem_l hZF ⟨X, R, owner, hX⟩
  obtain ⟨eX, eR⟩ := smdl_unique_l I mx.1 owner.1
  subst X' R'
  have family := ex.measures.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) Y
  obtain ⟨p, payload, active⟩ := ultra.active_l hZF (sx.read_source_l hZF) owner sx.theory
    source parent localExt agree family (ex.coherent.source_l I Y)
  obtain ⟨β, U, Q', G', E', built, extension, hb, edge, move, _⟩ :=
    it_apply_l hZF active tree hα hc hd next
  exact ⟨β, U, Q', G', E', b, j, p, built, extension, hb, edge, ultra, payload, move⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 迭代树后继与所属模型超幂之间的一致性

树前驱与所属模型分别施加同一个扩展器。两张实际超幂边的坍塌目标在
包含支撑端点的全部有限幂子集上一致；自动入口绑定新加入树中的同一个模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem it_ultra_agree_l (hZFC : M.Models ZFC)
    {ω κ L F K K' X R Y S c c' d d' j j' N V N' V' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R)
    (source' : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K' Y S) (agree : Ea_agree_d ω κ X Y)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (atoms : Ea_atoms_d ω κ L F) (normal : En_source_d ω κ L X F)
    (hκ : M.IsOrdinal κ) (hL : M.IsOrdinal L)
    (mx : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (my : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c' Y S)
    (nx : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N V)
    (ny : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d' N' V')
    (hN : M.TransitiveSet N) (hN' : M.TransitiveSet N')
    (u : It_ultra_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F c d j)
    (v : It_ultra_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F c' d' j') :
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
  exact ep_successor_agree_l hZFC source source' agree family coherent atoms normal hκ hL
    hs limit model hN nx he range wc hs' limit' model' hN' ny he' range' wc'

theorem it_short_apply_agree_l (hZFC : M.Models ZFC)
    {ω c₀ α ξ T Q G E k c d X R Y S κ L F : M.Domain}
    (tree : It_tree_d (ZFC.models_zf_l hZFC) ω c₀ α T Q G E) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q)
    (owner : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (parent : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d Y S)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (localExt : It_local_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X R κ L F) (agree : Ea_agree_d ω κ X Y) (hκY : M.mem κ Y)
    (ex : Ex_short_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F) :
    ∃ β U Q' G' E' b j b' j' N V N' V', It_tree_d (ZFC.models_zf_l hZFC) ω c₀ β U Q' G' E' ∧
      It_extension_d α ξ k T Q G E β U Q' G' E' ∧ Rd_entry_d α b Q' ∧ It_map_d G' k α j ∧
      It_ultra_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F d b j ∧ It_ultra_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F c b' j' ∧
      Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) b N V ∧
      Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) b' N' V' ∧
      Ea_agree_d ω L N N' ∧ ∀ μ, (M.mem μ L ∨ μ = L) → M.MemberSubset ω μ →
        ∃ K K', Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω μ K N V ∧ Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω μ K' N' V' := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨β, U, Q', G', E', b, j, _, h', extension, hb, edge, ultra, _⟩ :=
    it_short_apply_l hZFC tree hα hc hd owner parent hX hY localExt agree hκY ex
  obtain ⟨X₀, R₀, K₀, code, ready⟩ := (tree.sources ξ c hc).mem_l hZF ⟨X, R, owner, hX⟩
  obtain ⟨eX, eR⟩ := smdl_unique_l I code.1 owner.1
  subst X₀ R₀
  obtain ⟨_, hκX, _⟩ := localExt
  have hωκ := ex.critical.1.transitive ω ex.uncountable
  obtain ⟨K, source⟩ := ready.rebase_l hκX hωκ
    (sc_ordinal_small_l hZF ready.omega ready.transitive owner ready.theory hκX ex.critical.1)
  obtain ⟨b', j', ultra', ready'⟩ := it_ultra_exists_l hZF owner (ex.limit_l hZFC source)
  obtain ⟨N', V', K', code', next'⟩ := ready'.mem_l hZF (ultra'.target_mem_l hZF)
  obtain ⟨N, V, K₁, code₁, next⟩ := (h'.sources α b hb).mem_l hZF (ultra.target_mem_l hZF)
  obtain ⟨Y₀, S₀, K₂, code₂, ready₂⟩ := (tree.sources k d hd).mem_l hZF ⟨Y, S, parent, hY⟩
  obtain ⟨eY, eS⟩ := smdl_unique_l I code₂.1 parent.1
  subst Y₀ S₀
  obtain ⟨K₃, source₂⟩ := ready₂.rebase_l hκY hωκ
    (sc_ordinal_small_l hZF ready₂.omega ready₂.transitive parent ready₂.theory hκY ex.critical.1)
  obtain ⟨hLN, hLN', common⟩ := it_ultra_agree_l hZFC source₂ source
    (fun n D A hn hD hA => (agree n D A hn hD hA).symm) (ex.measures.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) Y) (ex.coherent.source_l I Y)
    ex.atoms (ex.normal.source_l Y) ex.critical.1 ex.length
    parent owner code₁ code'
    next.transitive next'.transitive ultra ultra'
  refine ⟨β, U, Q', G', E', b, j, b', j', N, V, N', V', h', extension, hb, edge, ultra, ultra', code₁, code', common, ?_⟩
  intro μ hμ hωμ
  have ho := hμ.elim ex.length.mem (fun eq => eq.symm ▸ ex.length)
  have hm := hμ.elim (next.transitive L hLN μ) (fun eq => eq.symm ▸ hLN)
  have hm' := hμ.elim (next'.transitive L hLN' μ) (fun eq => eq.symm ▸ hLN')
  obtain ⟨K, hk⟩ := next.rebase_l hm hωμ (sc_ordinal_small_l hZF next.omega next.transitive code₁ next.theory hm ho)
  obtain ⟨K', hk'⟩ := next'.rebase_l hm' hωμ (sc_ordinal_small_l hZF next'.omega next'.transitive code' next'.theory hm' ho)
  exact ⟨K, K', hk, hk'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 真正分叉的三结点迭代树

先用 pad 建立 0→1，再把结点 1 所属的扩展器施加到结点 0，建立 0→2。
两个后继在树序中不可比较；第二条边保留实际超幂与操作图证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem it_fork_l (hZFC : M.Models ZFC) {ω κ K L F X R c : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R)
    (code : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (localExt : It_local_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X R κ L F) (ex : Ex_short_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F) :
    ∃ z a b α T Q G E d j p, (∀ x, ¬ M.mem x z) ∧ M.SuccessorOf a z ∧ M.SuccessorOf b a ∧ M.SuccessorOf α b ∧
      It_tree_d (ZFC.models_zf_l hZFC) ω c α T Q G E ∧ Rd_entry_d z a T ∧ Rd_entry_d z b T ∧
      ¬ Rd_entry_d a b T ∧ ¬ Rd_entry_d b a T ∧ Rd_entry_d b d Q ∧ It_map_d G z b j ∧
      It_ultra_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F c d j ∧ It_payload_d p κ L F ∧ Rd_entry_d a p E := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨K₀, ready⟩ := source.rebase_l source.omega_mem (fun _ h => h) (source.cardinal_small.mono_mem_l (kp_pair_l (ZF.modelsKP hZF)) code source.omega_mem source.below)
  obtain ⟨z, a, T₀, Q₀, G₀, hz, ha, root⟩ := it_root_l hZF (it_source_mem_l hZF code ready)
  obtain ⟨b, T₁, Q₁, G₁, E₁, c₁, j₁, hb, tree, pad, hc₁, hca, edge₁, _, _⟩ := it_pad_l hZF root ha
  have eq := root.diagram.model_function.2 z c₁ c hc₁ (root.root z hz)
  subst c₁
  have hcz := pad.2.2.1 z c (root.root z hz)
  obtain ⟨α, T, Q, G, E, d, j, p, result, extension, hd, edge, ultra, payload, record⟩ :=
    it_short_apply_l hZFC tree hb hca hcz code code source.transitive source.transitive localExt (fun _ _ _ _ _ _ => Iff.rfl) source.cardinal_mem ex
  have za := (extension.2.1 z a).mpr (Or.inl (tree.diagram.map_bound_l hZF edge₁))
  have zb := result.diagram.map_bound_l hZF edge
  have no : ¬ M.mem b b := fun h => tree.diagram.order.ordinal.wellOrder.linear.irrefl b h h
  have ab : ¬ Rd_entry_d a b T := by
    intro h
    rcases (extension.2.1 a b).mp h with h | ⟨_, eq | h⟩
    · exact no (tree.diagram.order.bound a b h).2
    · exact no (eq ▸ hb.predecessor_mem)
    · rcases tree.diagram.order.forward a z h with eq | haz
      · exact hz z (eq ▸ ha.predecessor_mem)
      · exact hz a haz
  have ba : ¬ Rd_entry_d b a T := by
    intro h
    rcases result.diagram.order.forward b a h with eq | hba
    · exact no (eq.symm ▸ hb.predecessor_mem)
    · exact no (tree.diagram.order.ordinal.transitive a hb.predecessor_mem b hba)
  exact ⟨z, a, b, α, T, Q, G, E, d, j, p, hz, ha, hb, extension.1, result, za, zb, ab, ba, hd, edge, ultra, payload, record⟩

end YesMetaZFC.SetTheory.LargeCardinal
