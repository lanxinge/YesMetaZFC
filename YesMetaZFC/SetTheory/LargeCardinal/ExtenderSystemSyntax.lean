import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLaws

/-! # 全部源分量的带标号并及其实际过渡关系 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_at_d (Z a B : M.Domain) : Prop := ∃ c C S, Rd_entry_d a c Z ∧ KPair_d M c C S ∧ M.mem B C
def ep_at_m {d} (Z a B : Term d) : Formula 1 d := .existsE (.existsE (.existsE
  (.conj (rd_entry_m a.weaken.weaken.weaken (.bound 2) Z.weaken.weaken.weaken)
    (.conj (kpair_m (.bound 2) (.bound 1) .newest) (.mem B.weaken.weaken.weaken (.bound 1))))))
derive_free_closed ep_at_m
theorem ep_at_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Z a B : Term d) :
    Formula.satisfies ρ (ep_at_m Z a B) ↔ Ep_at_d (Z.eval ρ) (a.eval ρ) (B.eval ρ) := by
  simp only [ep_at_m, Ep_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, kpair_sat_l M hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

def Ep_rel_d (Z a B D : M.Domain) : Prop := ∃ c C S, Rd_entry_d a c Z ∧ KPair_d M c C S ∧ Rd_entry_d B D S
def ep_rel_m {d} (Z a B D : Term d) : Formula 1 d := .existsE (.existsE (.existsE
  (.conj (rd_entry_m a.weaken.weaken.weaken (.bound 2) Z.weaken.weaken.weaken)
    (.conj (kpair_m (.bound 2) (.bound 1) .newest) (rd_entry_m B.weaken.weaken.weaken D.weaken.weaken.weaken .newest)))))
derive_free_closed ep_rel_m
theorem ep_rel_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Z a B D : Term d) :
    Formula.satisfies ρ (ep_rel_m Z a B D) ↔ Ep_rel_d (Z.eval ρ) (a.eval ρ) (B.eval ρ) (D.eval ρ) := by
  simp only [ep_rel_m, Ep_rel_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, kpair_sat_l M hE, Definitional.Term.eval_weaken]; rfl

theorem ep_at_read_l {J Q Z a c C S B : M.Domain} (hz : Fn0_d J Q Z)
    (hac : Rd_entry_d a c Z) (hc : KPair_d M c C S) : Ep_at_d Z a B ↔ M.mem B C := by
  refine ⟨fun ⟨d, D, T, had, hd, hB⟩ => ?_, fun hB => ⟨c, C, S, hac, hc, hB⟩⟩
  have e := hz.2.2 a (hz.bound_l hac).1 d (hz.bound_l had).2 c (hz.bound_l hac).2 had hac
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M (e ▸ hd) hc
  exact hB

theorem ep_rel_read_l {J Q Z a c C S B D : M.Domain} (hz : Fn0_d J Q Z)
    (hac : Rd_entry_d a c Z) (hc : KPair_d M c C S) : Ep_rel_d Z a B D ↔ Rd_entry_d B D S := by
  refine ⟨fun ⟨d, E, T, had, hd, hBD⟩ => ?_, fun hBD => ⟨c, C, S, hac, hc, hBD⟩⟩
  have e := hz.2.2 a (hz.bound_l hac).1 d (hz.bound_l had).2 c (hz.bound_l hac).2 had hac
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M (e ▸ hd) hc
  exact hBD

theorem ep_at_model_l (hZF : M.Models ZF) {ω κ L X R F Z a B : M.Domain}
    (models : ∀ a c, Rd_entry_d a c Z → Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F a c)
    (hB : Ep_at_d Z a B) : ∃ c C S, Rd_entry_d a c Z ∧
      Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F a c ∧
      Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C S ∧ M.mem B C := by
  obtain ⟨c, C, S, hac, hc, hB⟩ := hB
  have hm := models a c hac
  obtain ⟨_, _, _, _, _, C', S', _, _, _, _, _, hp⟩ := hm
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hc hp.code.1
  exact ⟨c, C, S, hac, models a c hac, hp.code, hB⟩

structure Ep_graph_d (hZF : M.Models ZF) (ω κ L X R F J O Z A p T S : M.Domain) : Prop where
  order : Di_order_d J O
  order_spec : ∀ a b, Rd_entry_d a b O ↔ M.mem a J ∧ M.mem b J ∧ ∃ q, Ei_map_d ω L a b q
  projection : Fn0_d A J p
  indices : ∀ a, M.mem a J ↔ Ei_d ω L a
  models : ∃ Q, Fn0_d J Q Z ∧ ∀ a c, Rd_entry_d a c Z → Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F a c
  nodes : ∀ u, M.mem u A ↔ ∃ a B, KPair_d M u a B ∧ Ep_at_d Z a B
  index : ∀ u a B, KPair_d M u a B → (Rd_entry_d u a p ↔ M.mem u A)
  arrows : ∀ u v, Rd_entry_d u v T ↔ M.mem u A ∧ M.mem v A ∧
    ∃ a b B C, KPair_d M u a B ∧ KPair_d M v b C ∧ Ep_arrow_d ω κ L X a b B C
  relations : ∀ u v, Rd_entry_d u v S ↔ M.mem u A ∧ M.mem v A ∧
    ∃ a B C, KPair_d M u a B ∧ KPair_d M v a C ∧ Ep_rel_d Z a B C

def Ep_lift_d (ω κ L X a b B C : M.Domain) : Prop := ∀ f, M.mem f B → ∃ m n q g,
  M.mem m ω ∧ M.mem n ω ∧ Fn0_d m n q ∧ Fn0_d n L b ∧ Cp0_d m n L q b a ∧
    M.mem g C ∧ Ep_pull_d κ X m n q f g

structure Ep_system_d (hZF : M.Models ZF) (ω κ L X R F J O Z A p T S : M.Domain) : Prop
    extends Ep_graph_d hZF ω κ L X R F J O Z A p T S where
  diagram : Di_system_d J O A p T S
  representatives : ∀ u v a b B C, KPair_d M u a B → KPair_d M v b C → Rd_entry_d u v T →
    Ep_lift_d ω κ L X a b B C

variable {hZF : M.Models ZF} {ω κ L X R F J O Z A p T S : M.Domain}

theorem Ep_graph_d.at_l (h : Ep_graph_d hZF ω κ L X R F J O Z A p T S)
    {u a B} (hu : M.mem u A) (hc : KPair_d M u a B) : Ep_at_d Z a B := by
  obtain ⟨b, C, hc', hb⟩ := (h.nodes u).mp hu
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hc hc'
  exact hb

theorem Ep_graph_d.label_l (h : Ep_graph_d hZF ω κ L X R F J O Z A p T S)
    {u a} (hua : Rd_entry_d u a p) : ∃ B, KPair_d M u a B ∧ Ep_at_d Z a B := by
  obtain ⟨b, B, hu, hat⟩ := (h.nodes u).mp (h.projection.bound_l hua).1
  have hub := (h.index u b B hu).mpr (h.projection.bound_l hua).1
  have e := h.projection.2.2 u (h.projection.bound_l hua).1 b (h.projection.bound_l hub).2
    a (h.projection.bound_l hua).2 hub hua
  exact ⟨B, e ▸ hu, e ▸ hat⟩

theorem Ep_graph_d.arrow_l (h : Ep_graph_d hZF ω κ L X R F J O Z A p T S)
    {u v a b B C} (hu : KPair_d M u a B) (hv : KPair_d M v b C) :
    Rd_entry_d u v T ↔ M.mem u A ∧ M.mem v A ∧ Ep_arrow_d ω κ L X a b B C := by
  refine (h.arrows u v).trans ⟨?_, fun ⟨huA, hvA, hab⟩ => ⟨huA, hvA, a, b, B, C, hu, hv, hab⟩⟩
  rintro ⟨huA, hvA, a', b', B', C', hu', hv', hab⟩
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hu hu'
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hv hv'
  exact ⟨huA, hvA, hab⟩

theorem Ep_graph_d.relation_l (h : Ep_graph_d hZF ω κ L X R F J O Z A p T S)
    {u v a B C} (hu : KPair_d M u a B) (hv : KPair_d M v a C) :
    Rd_entry_d u v S ↔ M.mem u A ∧ M.mem v A ∧ Ep_rel_d Z a B C := by
  refine (h.relations u v).trans ⟨?_, fun ⟨huA, hvA, hab⟩ => ⟨huA, hvA, a, B, C, hu, hv, hab⟩⟩
  rintro ⟨huA, hvA, a', B', C', hu', hv', hab⟩
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hu hu'
  obtain ⟨_, rfl⟩ := kpair_injective_l M hv hv'
  exact ⟨huA, hvA, hab⟩

end YesMetaZFC.SetTheory.LargeCardinal
