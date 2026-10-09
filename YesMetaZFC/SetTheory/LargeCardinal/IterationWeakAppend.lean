import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakState

/-! # 线性模型列的返回因子随实际新结点延长 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Wi_state_d.branch_l {ω α T Q G a A S P : M.Domain} (h : Wi_state_d hZF ω α T Q G a A S P) :
    It_branch_d α T α := by
  refine ⟨fun _ hi => hi, ?_, fun i j hij _ => (h.diagram.order.bound i j hij).1, fun i hi => ⟨i, hi, Or.inl rfl⟩⟩
  intro i j hi hj
  rcases (h.diagram.order.ordinal.mem hi).trichotomy hZF.1 (h.diagram.order.ordinal.mem hj)
    (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) i j) with eq | lt | gt
  · exact Or.inl ((hZF.1.eq_of_same_members i j eq) ▸ h.diagram.order.refl i hi)
  · exact Or.inl (h.linear i j hj lt)
  · exact Or.inr (h.linear j i hi gt)

/-- 旧返回列只追加新因子；所有旧值和所有交换三角形都保留。 -/
theorem Wi_state_d.append_l {ω α T Q G a A S P β U Q' G' c N W σ : M.Domain}
    (h : Wi_state_d hZF ω α T Q G a A S P) (hβ : M.SuccessorOf β α)
    (diagram : It_diagram_d hZF ω β U Q' G')
    (order : ∀ i j, Rd_entry_d i j T → Rd_entry_d i j U)
    (tip : ∀ i, M.mem i α → Rd_entry_d i α U)
    (qs : ∀ i d, Rd_entry_d i d Q' ↔ Rd_entry_d i d Q ∨ i = α ∧ d = c)
    (gs : ∀ i j f, M.mem j α → (It_map_d G' i j f ↔ It_map_d G i j f))
    (mn : Smem_d I c N W) (source : It_source_d hZF ω c) (count : M.CardinalLessOrEqual I N ω)
    (hs : Smap_d I ω c a N A σ)
    (squares : ∀ i f j, Rd_entry_d i f P → It_map_d G' i α j → It_comp_d j σ f) :
    ∃ P', Wi_state_d hZF ω β U Q' G' a A S P' ∧
      ∀ i f, Rd_entry_d i f P' ↔ Rd_entry_d i f P ∨ i = α ∧ f = σ := by
  have no := KP.mem_irrefl_d (ZF.modelsKP hZF) α
  obtain ⟨P', pf, ps⟩ := Structure.IsSequenceOfLength.exists_append (value := σ) (ZF.modelsKP hZF) I
    ⟨h.diagram.order.ordinal, h.returns.function, h.returns.domain⟩ diagram.order.ordinal hβ
  have old i f (hi : M.mem i α) : Rd_entry_d i f P' ↔ Rd_entry_d i f P := (ps i f).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hi)).elim), Or.inl⟩
  have qold i d (hi : M.mem i α) : Rd_entry_d i d Q' ↔ Rd_entry_d i d Q := (qs i d).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hi)).elim), Or.inl⟩
  refine ⟨P', ⟨diagram, ?_, ?_, ?_, ⟨h.returns.model, pf.2.1, pf.2.2, ?_, ?_⟩⟩, ps⟩
  · intro i j hj hij
    rcases (hβ j).mp hj with hj | eq
    · exact order i j (h.linear i j hj hij)
    · have eq := hZF.1.eq_of_same_members j α eq
      subst j
      exact tip i hij
  · intro i d hd
    exact ((qs i d).mp hd).elim (h.sources i d) (fun hh => hh.2.symm ▸ source)
  · intro i d X R hd pair
    rcases (qs i d).mp hd with hd | ⟨_, rfl⟩
    · exact h.count i d X R hd pair
    · obtain ⟨eq, _⟩ := kpair_injective_l M pair mn.1.1
      exact eq.symm ▸ count
  · intro i f d X R hf hd mx
    rcases (ps i f).mp hf with hf | ⟨ei, ef⟩
    · exact h.returns.elementary i f d X R hf ((qold i d ((h.returns.domain i).mpr ⟨f, hf⟩)).mp hd) mx
    · subst i f
      have eq : d = c := ((qs α d).mp hd).elim
        (fun hd => (no ((h.diagram.model_domain α).mpr ⟨d, hd⟩)).elim) And.right
      subst d
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I mx mn.1
      exact hs
  · intro i j f u v edge hu hv x y z hxy hyz
    rcases (ps j v).mp hv with hv | ⟨ej, ev⟩
    · have edge := (gs i j f ((h.returns.domain j).mpr ⟨v, hv⟩)).mp edge
      have hi := (h.diagram.order.bound i j (h.diagram.map_bound_l hZF edge)).1
      exact h.returns.commute i j f u v edge ((old i u hi).mp hu) hv x y z hxy hyz
    · subst j v
      rcases (ps i u).mp hu with hu | ⟨ei, eu⟩
      · exact ((squares i u f hu edge).2 x z).mpr ⟨y, hxy, hyz⟩
      · subst i u
        exact (diagram.identity α f edge x y hxy).symm ▸ hyz

end YesMetaZFC.SetTheory.LargeCardinal
