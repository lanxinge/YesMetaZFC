import YesMetaZFC.SetTheory.LargeCardinal.IterationApply

/-! # 真正分叉的三结点迭代树

先用 pad 建立 0→1，再把结点 1 所属的扩展器施加到结点 0，建立 0→2。
两个后继在树序中不可比较；第二条边保留实际超幂与操作图证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem it_fork_l (hZFC : M.Models ZFC) {ω κ K L F X R c : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (code : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (localExt : It_local_d ω X κ L F) (ex : Ex_short_d (ZFC.models_zf_l hZFC) ω κ L F) :
    ∃ z a b α T Q G E d j p, (∀ x, ¬ M.mem x z) ∧ M.SuccessorOf a z ∧ M.SuccessorOf b a ∧ M.SuccessorOf α b ∧
      It_tree_d (ZFC.models_zf_l hZFC) ω c α T Q G E ∧ Rd_entry_d z a T ∧ Rd_entry_d z b T ∧
      ¬ Rd_entry_d a b T ∧ ¬ Rd_entry_d b a T ∧ Rd_entry_d b d Q ∧ It_map_d G z b j ∧
      It_ultra_d (ZFC.models_zf_l hZFC) ω κ L F c d j ∧ It_payload_d p κ L F ∧ Rd_entry_d a p E := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨K₀, ready⟩ := source.rebase_l hZF source.omega_mem (fun _ h => h) (source.cardinal_small.mono_l source.below)
  obtain ⟨z, a, T₀, Q₀, G₀, hz, ha, root⟩ := it_root_l hZF ⟨X, R, K₀, code, ready⟩
  obtain ⟨b, T₁, Q₁, G₁, E₁, c₁, j₁, hb, tree, pad, hc₁, hca, edge₁, _, _⟩ := it_pad_l hZF root ha
  have eq := root.diagram.model_function.2 z c₁ c hc₁ (root.root z hz)
  subst c₁
  have hcz := pad.2.2.1 z c (root.root z hz)
  obtain ⟨α, T, Q, G, E, d, j, p, result, extension, hd, edge, ultra, payload, record⟩ :=
    it_short_apply_l hZFC tree hb hca hcz code code localExt (fun _ _ _ _ _ _ => Iff.rfl) source.cardinal_mem ex
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
