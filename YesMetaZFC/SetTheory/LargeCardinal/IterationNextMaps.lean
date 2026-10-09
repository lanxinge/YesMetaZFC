import YesMetaZFC.SetTheory.LargeCardinal.IterationDiagram

/-! # 后继结点的整列嵌入由替代实际收集

旧箭头保持原值；新对角线取恒等图；每条到新结点的祖先箭头是原箭头
与指定后继边的复合。三种情形互斥，复合图唯一，故不需要选择代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_next_d (α k G e t i j f : M.Domain) : Prop := It_map_d G i j f ∨
  j = α ∧ ((i = α ∧ f = e) ∨ ∃ g, It_map_d G i k g ∧ It_comp_d g t f)
def it_next_m {d} (α k G e t i j f : Term d) : Formula 1 d := .disj (it_map_m G i j f)
  (.conj (Formula.extensionalEq j α) (.disj (.conj (Formula.extensionalEq i α) (Formula.extensionalEq f e))
    (.existsE (.conj (it_map_m G.weaken i.weaken k.weaken .newest) (it_comp_m .newest t.weaken f.weaken)))))
derive_free_closed it_next_m

theorem it_next_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (α k G e t i j f : Term d) :
    Formula.satisfies ρ (it_next_m α k G e t i j f) ↔
      It_next_d (α.eval ρ) (k.eval ρ) (G.eval ρ) (e.eval ρ) (t.eval ρ) (i.eval ρ) (j.eval ρ) (f.eval ρ) := by
  simp only [it_next_m, It_next_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, Formula.satisfies_exists_iff,
    it_map_sat_l hKP.1, it_comp_sat_l hKP.1, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_next_unique_l {ω α T Q G k e t i j f g : M.Domain} (h : It_diagram_d hZF ω α T Q G)
    (hf : It_next_d α k G e t i j f) (hg : It_next_d α k G e t i j g) : f = g := by
  have no : ¬ M.mem α α := fun ha => h.order.ordinal.wellOrder.linear.irrefl α ha ha
  have left {l f} (hf : It_map_d G α l f) : False := no (h.order.bound α l (h.map_bound_l hZF hf)).1
  have right {l f} (hf : It_map_d G l α f) : False := no (h.order.bound l α (h.map_bound_l hZF hf)).2
  rcases hf with hf | ⟨rfl, ⟨rfl, rfl⟩ | ⟨f₀, hf₀, cf⟩⟩
  · rcases hg with hg | ⟨rfl, _⟩
    · exact h.map_unique_l hZF hf hg
    · exact (right hf).elim
  · rcases hg with hg | ⟨_, ⟨_, eq⟩ | ⟨g₀, hg₀, _⟩⟩
    · exact (right hg).elim
    · exact eq.symm
    · exact (left hg₀).elim
  · rcases hg with hg | ⟨_, ⟨rfl, _⟩ | ⟨g₀, hg₀, cg⟩⟩
    · exact (right hg).elim
    · exact (left hf₀).elim
    · exact cf.unique_l hZF.1 ((h.map_unique_l hZF hg₀ hf₀) ▸ cg)

theorem it_next_maps_l {ω α T Q G k c X R d Y e t U : M.Domain}
    (h : It_diagram_d hZF ω α T Q G) (hc : Rd_entry_d k c Q) (mx : Smdl_d I c X R)
    (ht : Smap_d I ω c d X Y t)
    (u : ∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ Rd_entry_d i k T))
    (rel : M.IsSetRelation I U) : ∃ H, M.IsSetFunction I H ∧ M.IsDomainOf I U H ∧
      ∀ i j f, It_map_d H i j f ↔ It_next_d α k G e t i j f := by
  let ρ : Env M 5 := ⟨Fin.cases α (Fin.cases k (Fin.cases G (Fin.cases e (fun _ => t)))), fun _ => α⟩
  let φ : BinarySchema 5 := {
    body := .existsE (.existsE (.conj (kpair_m (.bound 3) (.bound 1) .newest)
      (it_next_m (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 1) .newest (.bound 2)))) }
  have sat r f : φ.denote ρ r f ↔ ∃ i j, KPair_d M r i j ∧ It_next_d α k G e t i j f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, it_next_sat_l (ZF.modelsKP hZF)]; rfl
  have total r (hr : M.mem r U) : ∃ f, φ.denote ρ r f := by
    obtain ⟨i, j, hp⟩ := rel r hr
    rcases (u i j).mp ⟨r, hp, hr⟩ with hij | ⟨rfl, rfl | hik⟩
    · obtain ⟨f, hf⟩ := h.map_l hZF hij
      exact ⟨f, (sat r f).mpr ⟨i, j, hp, Or.inl hf⟩⟩
    · exact ⟨e, (sat r e).mpr ⟨_, _, hp, Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩⟩
    · obtain ⟨f, hf⟩ := h.map_l hZF hik
      obtain ⟨b, Z, V, hb, mb⟩ := h.model_l hZF (h.order.bound i k hik).1
      obtain ⟨g, _, comp⟩ := it_comp_elementary_l hZF (h.elementary i k f b Z V c X R hf hb hc mb mx) ht
      exact ⟨g, (sat r g).mpr ⟨i, _, hp, Or.inr ⟨rfl, Or.inr ⟨f, hf, comp⟩⟩⟩⟩
  have unique r f g (hf : φ.denote ρ r f) (hg : φ.denote ρ r g) : f = g := by
    obtain ⟨i, j, hr, hf⟩ := (sat r f).mp hf
    obtain ⟨i', j', hr', hg⟩ := (sat r g).mp hg
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hr hr'
    exact it_next_unique_l hZF h hf hg
  obtain ⟨B, bs⟩ := ZF.exists_functionalImage hZF φ ρ U total unique
  obtain ⟨H, hh, hs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total (fun r _ => unique r)
    (fun r f hr hf => (bs f).mpr ⟨r, hr, hf⟩)
  refine ⟨H, hh.1, hh.2.1, fun i j f => ⟨?_, ?_⟩⟩
  · rintro ⟨r, hr, hrf⟩
    obtain ⟨i', j', hr', hf⟩ := (sat r f).mp ((hs r f).mp hrf).2
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hr hr'
    exact hf
  · intro hf
    obtain ⟨r, hr⟩ := (I).total i j
    have hij : Rd_entry_d i j U := by
      apply (u i j).mpr
      rcases hf with hf | ⟨rfl, ⟨rfl, _⟩ | ⟨g, hg, _⟩⟩
      · exact Or.inl (h.map_bound_l hZF hf)
      · exact Or.inr ⟨rfl, Or.inl rfl⟩
      · exact Or.inr ⟨rfl, Or.inr (h.map_bound_l hZF hg)⟩
    obtain ⟨s, hs', hsU⟩ := hij
    have hrU := (kpair_unique_l M hZF.1 hs' hr) ▸ hsU
    exact ⟨r, hr, (hs r f).mpr ⟨hrU, (sat r f).mpr ⟨i, j, hr, hf⟩⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
