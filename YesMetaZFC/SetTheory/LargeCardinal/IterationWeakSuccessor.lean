import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakAppend
import YesMetaZFC.SetTheory.LargeCardinal.IterationEmbeddingLaws
import YesMetaZFC.SetTheory.LargeCardinal.IterationNiceReturn

/-! # 弱迭代后继步由原 nice 树的返回定理自动产生

选择同一棵 ω 树的共尾枝和实际极限，再把根腿接到原线性列。
新模型可数，返回因子满足原根复合式，故全部旧返回三角形继续交换。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Wi_state_d.successor_l {ω α ξ T Q G a A S P θ c T₀ Q₀ G₀ E₀ L₀ : M.Domain}
    (h : Wi_state_d hZF ω α T Q G a A S P) (rank : V_d I θ A) (ma : Smem_d I a A S)
    (hα : M.SuccessorOf α ξ) (hc : Rd_entry_d ξ c Q) (nice : It_nice_d hZF ω c ω T₀ Q₀ G₀ E₀ L₀) :
    ∃ β U Q' G' P' B d N W H σ j, Wi_state_d hZF ω β U Q' G' a A S P' ∧
      Wi_extension_d α Q G P β Q' G' P' ∧ Rd_entry_d α d Q' ∧ Rd_entry_d α σ P' ∧
      It_branch_d ω T₀ B ∧ Wi_limit_d hZF ω B Q₀ G₀ d N W H ∧
      It_map_d G' ξ α j ∧ ∀ o, (∀ x, ¬ M.mem x o) → Rd_entry_d o j H := by
  have hw := nice.tree.omega
  obtain ⟨o, ho, _⟩ := hw.1.1
  obtain ⟨X, R, K, mx, _⟩ := h.sources ξ c hc
  obtain ⟨π, hπ⟩ := (h.returns.domain ξ).mp hα.predecessor_mem
  have embed := h.returns.elementary ξ π c X R hπ hc mx.1
  obtain ⟨B, L, D, p, F, V, r, d, N, W, H, σ, branch, system, limit, mn, cone, ready, hs, projects, j, hj, square⟩ :=
    it_pnice_return_l hZFC nice.toIt_pnice_d mx (h.count ξ c X R hc mx.1.1) ho rank ma embed
  have count := cone.countable_l hZFC hw nice.tree.diagram branch.subset
    (ZF.exists_inclusionInjection hZF I branch.subset) (it_countable_l hZF nice.tree mx.1 (h.count ξ c X R hc mx.1.1))
  have jj := cone.elementary o j c X R hj (nice.tree.root o ho) mx.1
  obtain ⟨β, U, Q', G', e, hβ, diagram, us, qs, gs, edge⟩ :=
    it_diagram_extend_l hZF hw h.diagram hα hc mx.1 mn.1 jj
  have no := KP.mem_irrefl_d (ZF.modelsKP hZF) α
  have old i k f (hk : M.mem k α) : It_map_d G' i k f ↔ It_map_d G i k f := (gs i k f).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hk)).elim), Or.inl⟩
  have tip i (hi : M.mem i α) : Rd_entry_d i α U := by
    apply (us i α).mpr
    refine Or.inr ⟨rfl, Or.inr ?_⟩
    rcases (hα i).mp hi with hi | eq
    · exact h.linear i ξ hα.predecessor_mem hi
    · exact (hZF.1.eq_of_same_members i ξ eq).symm ▸ h.diagram.order.refl ξ hα.predecessor_mem
  have squares i f k (hf : Rd_entry_d i f P) (hk : It_map_d G' i α k) : It_comp_d k σ f := by
    rcases (gs i α k).mp hk with hk | ⟨_, ⟨eq, _⟩ | ⟨g, hg, comp⟩⟩
    · exact (no (h.diagram.order.bound i α (h.diagram.map_bound_l hZF hk)).2).elim
    · exact (no (eq ▸ (h.returns.domain i).mpr ⟨f, hf⟩)).elim
    · exact comp.assoc_l square (h.returns.comp_l hZF h.diagram (fun _ h => h) hg hf hπ)
  obtain ⟨P', state, ps⟩ := h.append_l hZF hβ diagram (fun i k hik => (us i k).mpr (Or.inl hik))
    tip qs old mn ready count hs squares
  refine ⟨β, U, Q', G', P', B, d, N, W, H, σ, j, state,
    ⟨hβ, fun i d hd => (qs i d).mpr (Or.inl hd), old, fun i f hf => (ps i f).mpr (Or.inl hf)⟩,
    (qs α d).mpr (Or.inr ⟨rfl, rfl⟩), (ps α σ).mpr (Or.inr ⟨rfl, rfl⟩),
    branch, ⟨L, D, p, F, V, r, system, limit, mn, cone, projects⟩, edge, ?_⟩
  intro o' ho'
  exact (hZF.1.eq_of_same_members o o' (fun x => iff_of_false (ho x) (ho' x))) ▸ hj

end YesMetaZFC.SetTheory.LargeCardinal
