import YesMetaZFC.SetTheory.LargeCardinal.IterationRealizer
import YesMetaZFC.SetTheory.LargeCardinal.IterationLimitExtend
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Isomorphism

/-! # 从良基共尾树枝自动完成极限扩张

输出保留同一个带标号系统，坍塌后的新结点仍带有它的实际直接极限证书。
非可数共尾度与相容良基实现两种入口直接构造证书，再调用同一添枝定理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure It_limit_extension_d (hZF : M.Models ZF) (ω c₀ α T Q G E B β U Q' G' : M.Domain) : Prop where
  successor : M.SuccessorOf β α
  tree : It_tree_d hZF ω c₀ β U Q' G' E
  order : ∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B)
  old_maps : ∀ i j f, M.mem j α → (It_map_d G' i j f ↔ It_map_d G i j f)
  limit : ∃ L A p H R r d N W P,
    (∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) ∧
    It_system_d B L Q G A p H R ∧ Di_limit_d A p H R r N W ∧
    Smem_d (kp_pair_l (ZF.modelsKP hZF)) d N W ∧ It_cone_d hZF ω B Q G d N W P ∧
    (∀ i c, Rd_entry_d i c Q' ↔ Rd_entry_d i c Q ∨ i = α ∧ c = d) ∧
    ∀ i f, M.mem i α → (It_map_d G' i α f ↔ Rd_entry_d i f P)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_wf_branch_extend_l {ω c₀ α T Q G E B : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (hl : M.IsLimitOrdinal α) (built : It_wf_branch_d hZF ω α T Q G B) :
    ∃ β U Q' G', It_limit_extension_d hZF ω c₀ α T Q G E B β U Q' G' := by
  obtain ⟨b, L, A, p, H, R, q, c, C, V, ls, s, elem, limit, model, wf⟩ := built
  obtain ⟨k, hk⟩ := hl.2.1
  obtain ⟨i, hi, _⟩ := b.cofinal k hk
  obtain ⟨a, X, S, ha, _⟩ := tree.diagram.model_l hZF (b.subset i hi)
  obtain ⟨X, S, K, mx, source⟩ := tree.sources i a ha
  obtain ⟨d, N, W, P, e, r, cone, ready, target, _, _, bij, he, hr, rs, _⟩ :=
    it_limit_model_l hZF tree.diagram b.subset s elem limit model wf hi ha mx source
  have next_limit := di_limit_iso_l (ZF.modelsKP hZF) limit bij hr rs target.1.2.2
    (fun _ _ _ _ hx hy => he.relation_l I hZF tree.omega model target.1 hx hy)
  obtain ⟨β, U, Q', G', hβ, next, us, qs, old, tips⟩ := it_tree_limit_l hZF tree hl b cone ready
  exact ⟨β, U, Q', G', hβ, next, us, old, L, A, p, H, R, r, d, N, W, P, ls, s, next_limit, target, cone, qs, tips⟩

theorem it_sigma_extend_l {ω c₀ α κ T Q G E B : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (b : It_branch_d α T B)
    (hκ : M.IsCofinality I κ α) (hωκ : M.mem ω κ) (dc : Dc_d I ω) :
    ∃ β U Q' G', It_limit_extension_d hZF ω c₀ α T Q G E B β U Q' G' := by
  have models i c (hc : Rd_entry_d i c Q) : ∃ X R, Smem_d I c X R := by
    obtain ⟨X, R, _, code, _⟩ := tree.sources i c hc
    exact ⟨X, R, code⟩
  exact it_wf_branch_extend_l hZF tree (hκ.hasCofinalSequence.elim fun _ hf => hf.isLimitOrdinal)
    (it_sigma_branch_l hZF tree.omega tree.diagram b hκ hωκ dc models)

theorem it_pruned_extend_l {ω c₀ α T Q G E F a Y V P : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (cf : M.IsCofinalOrdinalSequence I F ω α) (ha : M.mem a α)
    (pruned : ∀ i k, M.mem i α → M.mem k α → ∃ j, M.mem j α ∧ Rd_entry_d i j T ∧ (k = j ∨ M.mem k j))
    (realizer : It_realizer_d hZF α Q G Y V P) (wf : Wf_rel_d Y V) :
    ∃ B β U Q' G', It_wf_branch_d hZF ω α T Q G B ∧ M.mem a B ∧
      It_limit_extension_d hZF ω c₀ α T Q G E B β U Q' G' := by
  obtain ⟨B, b, haB⟩ := it_pruned_wf_branch_l hZF tree.omega tree.diagram cf ha pruned realizer wf
  obtain ⟨β, U, Q', G', ext⟩ := it_wf_branch_extend_l hZF tree cf.isLimitOrdinal b
  exact ⟨B, β, U, Q', G', b, haB, ext⟩

end YesMetaZFC.SetTheory.LargeCardinal
