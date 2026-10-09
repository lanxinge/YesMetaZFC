import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakAppend
import YesMetaZFC.SetTheory.LargeCardinal.IterationLimitDiagram

/-! # 弱迭代在可数极限处的完整延长

旧返回列证明原直接极限良基，并产生与全部旧腿交换的同一返回因子。
可数性和完整源由实际极限构造保持，随后追加原规范腿及新返回值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Wi_state_d.limit_l {ω α T Q G a A S P : M.Domain}
    (h : Wi_state_d hZF ω α T Q G a A S P) (ma : Smem_d I a A S)
    (limit : M.IsLimitOrdinal α) (count : M.CardinalLessOrEqual I α ω) :
    ∃ β U Q' G' P' c N W H σ, Wi_state_d hZF ω β U Q' G' a A S P' ∧
      Wi_extension_d α Q G P β Q' G' P' ∧ Rd_entry_d α c Q' ∧ Rd_entry_d α σ P' ∧
      Wi_limit_d hZF ω α Q G c N W H ∧ Smap_d I ω c a N A σ ∧
      (∀ i j, M.mem i α → (It_map_d G' i α j ↔ Rd_entry_d i j H)) ∧
      ∀ i f j, Rd_entry_d i f P → Rd_entry_d i j H → It_comp_d j σ f := by
  obtain ⟨o, ho⟩ := limit.2.1
  obtain ⟨c₀, hc₀⟩ := (h.diagram.model_domain o).mp ho
  have ready := h.sources o c₀ hc₀
  have ready₀ := ready
  obtain ⟨_, _, _, _, source⟩ := ready₀
  have hw := source.omega
  obtain ⟨L, D, p, F, R, r, c, N, W, H, σ, s, lim, mn, cone, ready, cn, hs, projects, squares⟩ :=
    it_countable_limit_l hZFC hw h.diagram (h.branch_l hZF) ho hc₀ ready ma h.returns count h.count
  obtain ⟨β, U, Q', G', e, hβ, diagram, us, qs, gs⟩ :=
    it_limit_diagram_l hZF hw h.diagram limit (h.branch_l hZF) cone
  have no := KP.mem_irrefl_d (ZF.modelsKP hZF) α
  have old i j f (hj : M.mem j α) : It_map_d G' i j f ↔ It_map_d G i j f := (gs i j f).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hj)).elim), Or.inl⟩
  have square i f j (hf : Rd_entry_d i f P) (hj : It_map_d G' i α j) : It_comp_d j σ f := by
    rcases (gs i α j).mp hj with hj | ⟨_, ⟨eq, _⟩ | hj⟩
    · exact (no (h.diagram.order.bound i α (h.diagram.map_bound_l hZF hj)).2).elim
    · exact (no (eq ▸ (h.returns.domain i).mpr ⟨f, hf⟩)).elim
    · exact squares i f j hf hj
  obtain ⟨P', state, ps⟩ := h.append_l hZF hβ diagram (fun i j hij => (us i j).mpr (Or.inl hij))
    (fun i hi => (us i α).mpr (Or.inr ⟨rfl, Or.inr hi⟩)) qs old mn ready cn hs square
  refine ⟨β, U, Q', G', P', c, N, W, H, σ, state,
    ⟨hβ, fun i d hd => (qs i d).mpr (Or.inl hd), old, fun i f hf => (ps i f).mpr (Or.inl hf)⟩,
    (qs α c).mpr (Or.inr ⟨rfl, rfl⟩), (ps α σ).mpr (Or.inr ⟨rfl, rfl⟩),
    ⟨L, D, p, F, R, r, s, lim, mn, cone, projects⟩, hs, ?_, squares⟩
  intro i j hi
  exact (gs i α j).trans ⟨fun hh => hh.elim
    (fun hh => (no (h.diagram.order.bound i α (h.diagram.map_bound_l hZF hh)).2).elim)
    (fun hh => hh.2.elim (fun hh => (no (hh.1 ▸ hi)).elim) id), fun hh => Or.inr ⟨rfl, Or.inr hh⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
