import YesMetaZFC.SetTheory.LargeCardinal.IterationBranchExtend
import YesMetaZFC.SetTheory.LargeCardinal.IterationLinearOrder

/-! # 任意非空内部序数长度的 padding 树

常模型、恒等嵌入和空操作逐项实际编码。这给出极限扩张所需源、共尾枝、
相容实现的无限实例族；极限扩张仍统一调用一般直接极限及坍塌构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_padding_l {ω c α : M.Domain} (ready : It_source_d hZF ω c)
    (ho : M.IsOrdinal α) (ne : ∃ i, M.mem i α) :
    ∃ T Q G E X R P, It_tree_d hZF ω c α T Q G E ∧ Smem_d I c X R ∧
      It_cone_d hZF ω α Q G c X R P ∧
      (∀ i j, Rd_entry_d i j T ↔ M.mem i α ∧ M.mem j α ∧ (i = j ∨ M.mem i j)) := by
  obtain ⟨X, R, K, code, source⟩ := ready
  obtain ⟨T, order, ts, pred⟩ := it_linear_order_l (ZF.modelsKP hZF) ho
  obtain ⟨C, hc⟩ := KP.exists_singleton (ZF.modelsKP hZF) c
  obtain ⟨Q, qf, qs⟩ := ZF.exists_constantFunction hZF I (source := α) ((hc c).mpr rfl)
  obtain ⟨e, he, es⟩ := smap_identity_l I hZF (c := c) (X := X) source.omega
  obtain ⟨D, hd⟩ := KP.exists_singleton (ZF.modelsKP hZF) e
  obtain ⟨G, gf, gs⟩ := ZF.exists_constantFunction hZF I (source := T) ((hd e).mpr rfl)
  obtain ⟨P, pf, ps⟩ := ZF.exists_constantFunction hZF I (source := α) ((hd e).mpr rfl)
  have maps i j f : It_map_d G i j f ↔ Rd_entry_d i j T ∧ f = e := by
    constructor
    · rintro ⟨r, hr, hrf⟩
      obtain ⟨hrT, eq⟩ := (gs r f).mp hrf
      exact ⟨⟨r, hr, hrT⟩, eq⟩
    · rintro ⟨⟨r, hr, hrT⟩, rfl⟩
      exact ⟨r, hr, (gs r _).mpr ⟨hrT, rfl⟩⟩
  have typed i b Y S (hb : Rd_entry_d i b Q) (my : Smdl_d I b Y S) : b = c ∧ Y = X := by
    have eq := ((qs i b).mp hb).2
    exact ⟨eq, (smdl_unique_l I (eq ▸ my) code.1).1⟩
  have ident f (hf : f = e) x y (hxy : Rd_entry_d x y f) : x = y := ((es x y).mp (hf ▸ hxy)).2
  have elem i f b Y S (hf : f = e) (hb : Rd_entry_d i b Q) (my : Smdl_d I b Y S) : Smap_d I ω b c Y X f := by
    obtain ⟨rfl, rfl⟩ := typed i b Y S hb my
    exact hf.symm ▸ he
  have diagram : It_diagram_d hZF ω α T Q G := by
    refine ⟨order, qf.1, qf.2.1,
      fun i b hb => ((qs i b).mp hb).2.symm ▸ ⟨X, R, code.1⟩, gf.1, gf.2.1, ?_,
      fun i f hf => ident f ((maps i i f).mp hf).2, ?_⟩
    · intro i j f b Y S d Z V hf hb hd my mz
      obtain ⟨rfl, rfl⟩ := typed j d Z V hd mz
      exact elem i f b Y S ((maps i j f).mp hf).2 hb my
    · intro i j k f g v hf hg hv x y z hxy hyz
      have eq := ((maps j k g).mp hg).2.trans ((maps i k v).mp hv).2.symm
      exact eq ▸ (ident f ((maps i j f).mp hf).2 x y hxy).symm ▸ hyz
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  let φ : UnarySchema 1 := { body := Formula.existsMem (.bound 1) (Formula.isSuccessor .newest (.bound 1)) }
  obtain ⟨J, js⟩ := ZF.separation_exists_d hZF φ ⟨fun _ => α, fun _ => α⟩ α
  have indices i : M.mem i J ↔ ∃ j, M.mem j α ∧ M.SuccessorOf j i := by
    have sat : φ.denote ⟨fun _ => α, fun _ => α⟩ i ↔ ∃ j, M.mem j α ∧ M.SuccessorOf j i := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_isSuccessor_iff]; rfl
    exact (js i).trans ((and_congr_right fun _ => sat).trans ⟨And.right,
      fun ⟨j, hj, hs⟩ => ⟨ho.transitive j hj i hs.predecessor_mem, j, hj, hs⟩⟩)
  obtain ⟨Z, hZ⟩ := KP.exists_singleton (ZF.modelsKP hZF) z
  obtain ⟨E, ef, es'⟩ := ZF.exists_constantFunction hZF I (source := J) ((hZ z).mpr rfl)
  have tree : It_tree_d hZF ω c α T Q G E := by
    refine ⟨source.omega, diagram,
      fun o hzero => (qs o c).mpr ⟨ho.empty_mem_of_nonempty (ZF.modelsKP hZF) ne hzero, rfl⟩,
      fun i b hb => ((qs i b).mp hb).2.symm ▸ (show It_source_d hZF ω c from ⟨X, R, K, code, source⟩), ef.1,
      fun i => (ef.2.1 i).symm.trans (indices i), ?_, ?_⟩
    · intro i j hj hs
      have hi := ho.transitive j hj i hs.predecessor_mem
      exact ⟨i, c, c, c, e, z, pred i j hj hs, (qs i c).mpr ⟨hi, rfl⟩, (qs i c).mpr ⟨hi, rfl⟩,
        (qs j c).mpr ⟨hj, rfl⟩, (maps i j e).mpr ⟨(ts i j).mpr ⟨hi, hj, Or.inr hs.predecessor_mem⟩, rfl⟩,
        (es' i z).mpr ⟨(indices i).mpr ⟨j, hj, hs⟩, rfl⟩, Or.inl ⟨hz, rfl, rfl, ident e rfl⟩⟩
    · intro δ hδ hl b Y S hb hp y hy
      have eq := ((qs δ b).mp hb).2
      subst b
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp code.1.1
      obtain ⟨i, hi⟩ := hl.2.1
      have hiα := ho.transitive δ hδ i hi
      have hiδ := (ts i δ).mpr ⟨hiα, hδ, Or.inr hi⟩
      exact ⟨i, hi, hiδ, e, (maps i δ e).mpr ⟨hiδ, rfl⟩, y, (es y y).mpr ⟨hy, rfl⟩⟩
  have cone : It_cone_d hZF ω α Q G c X R P := by
    refine ⟨⟨code.1, pf.1, pf.2.1,
      fun i f b Y S hf => elem i f b Y S ((ps i f).mp hf).2, ?_⟩, ?_⟩
    · intro i j f u v hf hu hv x y z hxy hyz
      have eq := ((ps j v).mp hv).2.trans ((ps i u).mp hu).2.symm
      exact eq ▸ (ident f ((maps i j f).mp hf).2 x y hxy).symm ▸ hyz
    · intro x hx
      obtain ⟨i, hi⟩ := ne
      exact ⟨i, e, x, (ps i e).mpr ⟨hi, rfl⟩, (es x x).mpr ⟨hx, rfl⟩⟩
  exact ⟨T, Q, G, E, X, R, P, tree, code, cone, ts⟩

/-- 任意极限长度的实际树、共尾良基枝与极限添枝，统一经过一般商与坍塌。 -/
theorem it_padding_limit_l {ω c α : M.Domain} (ready : It_source_d hZF ω c) (hl : M.IsLimitOrdinal α) :
    ∃ T Q G E β U Q' G', It_tree_d hZF ω c α T Q G E ∧ It_wf_branch_d hZF ω α T Q G α ∧
      It_limit_extension_d hZF ω c α T Q G E α β U Q' G' := by
  obtain ⟨T, Q, G, E, X, R, P, tree, code, cone, ts⟩ := it_padding_l hZF ready hl.1 hl.2.1
  have b : It_branch_d α T α := ⟨fun _ hx => hx, fun i j hi hj => by
    rcases hl.1.wellOrder.linear.compare i hi j hj with eq | hij | hji
    · exact Or.inl ((ts i j).mpr ⟨hi, hj, Or.inl (hZF.1.eq_of_same_members i j eq)⟩)
    · exact Or.inl ((ts i j).mpr ⟨hi, hj, Or.inr hij⟩)
    · exact Or.inr ((ts j i).mpr ⟨hj, hi, Or.inr hji⟩),
    fun i j hij _ => ((ts i j).mp hij).1, fun i hi => ⟨i, hi, Or.inl rfl⟩⟩
  have wf : Wf_rel_d X R := fun Y _ ne => by
    obtain ⟨x, hx, minimal⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) ne
    exact ⟨x, hx, fun y hy hr => minimal y hy ((code.2 y x).mp hr).2.2⟩
  have built := it_realized_branch_l hZF tree.omega tree.diagram b hl.2.1 (cone.toIt_embedding_d.realizer_l hZF tree.omega) wf
  obtain ⟨β, U, Q', G', ext⟩ := it_wf_branch_extend_l hZF tree hl built
  exact ⟨T, Q, G, E, β, U, Q', G', tree, built, ext⟩

/-- 同一实例同时满足可数共尾枝选择的延伸条件，起点可指定为任意旧结点。 -/
theorem it_padding_pruned_l {ω c α F a : M.Domain} (ready : It_source_d hZF ω c)
    (cf : M.IsCofinalOrdinalSequence I F ω α) (ha : M.mem a α) :
    ∃ T Q G E B β U Q' G', It_tree_d hZF ω c α T Q G E ∧ M.mem a B ∧
      It_wf_branch_d hZF ω α T Q G B ∧ It_limit_extension_d hZF ω c α T Q G E B β U Q' G' := by
  obtain ⟨T, Q, G, E, X, R, P, tree, code, cone, ts⟩ := it_padding_l hZF ready cf.1.1 cf.1.2.1
  have pruned i k (hi : M.mem i α) (hk : M.mem k α) : ∃ j, M.mem j α ∧ Rd_entry_d i j T ∧ (k = j ∨ M.mem k j) := by
    rcases cf.1.1.wellOrder.linear.compare i hi k hk with eq | hik | hki
    · exact ⟨k, hk, (ts i k).mpr ⟨hi, hk, Or.inl (hZF.1.eq_of_same_members i k eq)⟩, Or.inl rfl⟩
    · exact ⟨k, hk, (ts i k).mpr ⟨hi, hk, Or.inr hik⟩, Or.inl rfl⟩
    · exact ⟨i, hi, tree.diagram.order.refl i hi, Or.inr hki⟩
  have wf : Wf_rel_d X R := fun Y _ ne => by
    obtain ⟨x, hx, minimal⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) ne
    exact ⟨x, hx, fun y hy hr => minimal y hy ((code.2 y x).mp hr).2.2⟩
  obtain ⟨B, β, U, Q', G', built, haB, ext⟩ := it_pruned_extend_l hZF tree cf ha pruned (cone.toIt_embedding_d.realizer_l hZF tree.omega) wf
  exact ⟨T, Q, G, E, B, β, U, Q', G', tree, haB, built, ext⟩

end YesMetaZFC.SetTheory.LargeCardinal
