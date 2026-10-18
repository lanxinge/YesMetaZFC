import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRepresentative
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Factor

/-! # 源包含诱导实际超幂的关系嵌入

同一支撑、同一代表在两个商中读取；函数值域的包含保持等价核及隶属关系。
不要求小源初等包含于大源。该构造用于辨认严格秩段超幂的实际像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_inclusion_l {ω κ L X R Y S F c d
    J O Z A p T V q C W J' O' Z' A' p' T' V' q' C' W' : M.Domain}
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (inside : M.MemberSubset X Y)
    (family : Em_source_d ω κ L X F) (family' : Em_source_d ω κ L Y F)
    (h : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (h' : Ep_system_d I ω κ L Y S F J' O' Z' A' p' T' V') (limit' : Di_limit_d A' p' T' V' q' C' W') :
    ∃ g, M.IsSetInjectionFromTo I g C C' ∧
      (∀ E H E' H', Rd_entry_d E E' g → Rd_entry_d H H' g → (Rd_entry_d E H W ↔ Rd_entry_d E' H' W')) ∧
      ∀ a f E E', Ep_repr_d q a f E → (Rd_entry_d E E' g ↔ Ep_repr_d q' a f E') := by
  have lift u a B f (hu : M.mem u A) (pair : KPair_d M u a B) (hf : M.mem f B) :
      ∃ E, M.mem E C' ∧ Ep_repr_d q' a f E := by
    obtain ⟨H, _, huH⟩ := limit.projection.2.1 u hu
    have old : Ep_repr_d q a f H := ⟨u, B, pair, hf, huH⟩
    obtain ⟨hfX, n, hno, ha, D, hd, fn⟩ := old.source_l hZF family h limit
    exact ep_repr_exists_l hZF family' h' limit' ((h'.indices a).mpr ((h.indices a).mp (old.index_l hZF h limit)))
      ha hd (inside f hfX) (fn.mono_target_l inside)
  have atoms a f g E H E' H' U (haU : Rd_entry_d a U F)
      (fe : Ep_repr_d q a f E) (gh : Ep_repr_d q a g H)
      (fe' : Ep_repr_d q' a f E') (gh' : Ep_repr_d q' a g H') :
      (E = H ↔ E' = H') ∧ (Rd_entry_d E H W ↔ Rd_entry_d E' H' W') := by
    obtain ⟨_, _, _, _, D, _, ff⟩ := fe.source_l hZF family h limit
    obtain ⟨_, _, _, _, D', _, gf⟩ := gh.source_l hZF family h limit
    have eq : Rp_eq_d X U f g ↔ Rp_eq_d Y U f g := by
      constructor <;> rintro ⟨B, hB, eq⟩ <;> refine ⟨B, hB, fun s hs => ?_⟩
      · obtain ⟨x, hx, hf, hg⟩ := eq s hs
        exact ⟨x, inside x hx, hf, hg⟩
      · obtain ⟨x, _, hf, hg⟩ := eq s hs
        exact ⟨x, (ff.bound_l hf).2, hf, hg⟩
    have rel : Rp_rel_d I X U R f g ↔ Rp_rel_d I Y U S f g := by
      constructor <;> rintro ⟨B, hB, rel⟩ <;> refine ⟨B, hB, fun s hs => ?_⟩
      · obtain ⟨x, hx, y, hy, hf, hg, hxy⟩ := rel s hs
        exact ⟨x, inside x hx, y, inside y hy, hf, hg,
          (hn.2 x y).mpr ⟨inside x hx, inside y hy, ((hm.2 x y).mp hxy).2.2⟩⟩
      · obtain ⟨x, _, y, _, hf, hg, hxy⟩ := rel s hs
        exact ⟨x, (ff.bound_l hf).2, y, (gf.bound_l hg).2, hf, hg,
          (hm.2 x y).mpr ⟨(ff.bound_l hf).2, (gf.bound_l hg).2, ((hn.2 x y).mp hxy).2.2⟩⟩
    have left := ep_repr_atoms_l hZF family h limit haU fe gh
    have right := ep_repr_atoms_l hZF family' h' limit' haU fe' gh'
    exact ⟨left.1.trans (eq.trans right.1.symm), left.2.trans (rel.trans right.2.symm)⟩
  let ρ : Env M 1 := ⟨fun _ => q', fun _ => q'⟩
  let φ : BinarySchema 1 := { body := .existsE (.existsE (.existsE
    (.conj (kpair_m (.bound 4) (.bound 2) (.bound 1))
      (.conj (.mem .newest (.bound 1)) (ep_repr_m (.bound 5) (.bound 2) .newest (.bound 3)))))) }
  have sat u E : φ.denote ρ u E ↔ ∃ a B f, KPair_d M u a B ∧ M.mem f B ∧ Ep_repr_d q' a f E := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, Formula.satisfies_mem_iff, ep_repr_sat_l hZF.1]; rfl
  have unique u (hu : M.mem u A) E H (he : φ.denote ρ u E) (hh : φ.denote ρ u H) : E = H := by
    obtain ⟨a, B, f, pair, hf, fe⟩ := (sat u E).mp he
    obtain ⟨a', B', g, pair', hg, gh⟩ := (sat u H).mp hh
    obtain ⟨ea, eb⟩ := kpair_injective_l M pair' pair
    subst a' B'
    obtain ⟨E₀, _, huE⟩ := limit.projection.2.1 u hu
    have fv : Ep_repr_d q a f E₀ := ⟨u, B, pair, hf, huE⟩
    obtain ⟨_, n, hno, ha, _⟩ := fv.source_l hZF family h limit
    obtain ⟨U, haU⟩ := family.total n a hno ha
    exact (atoms a f g E₀ E₀ E H U haU fv ⟨u, B, pair, hg, huE⟩ fe gh).1.mp rfl
  obtain ⟨t, ht, ts⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := A) (target := C')
    (fun u hu => by
      obtain ⟨a, B, pair, hat⟩ := (h.nodes u).mp hu
      have models := h.components
      obtain ⟨_, _, _, _, comp, model, hb⟩ := ep_at_model_l hZF models hat
      obtain ⟨_, _, _, ⟨f, hf⟩, _⟩ := ep_representatives_l I hZF.1 family comp model hb
      obtain ⟨E, _, he⟩ := lift u a B f hu pair hf
      exact ⟨E, (sat u E).mpr ⟨a, B, f, pair, hf, he⟩⟩)
    unique (fun u E _ he => by
      obtain ⟨_, _, _, _, _, v, _, _, _, hv⟩ := (sat u E).mp he
      exact (limit'.projection.bound_l hv).2)
  have spec u E := (ts u E).trans (and_congr_right fun _ => sat u E)
  have any u a B f E (pair : KPair_d M u a B) (hf : M.mem f B) (huE : Rd_entry_d u E t) : Ep_repr_d q' a f E := by
    obtain ⟨H, _, fh⟩ := lift u a B f (ht.input_mem_of_pairMember huE) pair hf
    have hH := (ts u H).mpr ⟨ht.input_mem_of_pairMember huE, (sat u H).mpr ⟨a, B, f, pair, hf, fh⟩⟩
    exact ht.1.2 u H E hH huE ▸ fh
  have comm u v E H (edge : Rd_entry_d u v T) (huE : Rd_entry_d u E t) (hvH : Rd_entry_d v H t) : E = H := by
    obtain ⟨_, a, B, f, pair, hf, fe⟩ := (spec u E).mp huE
    obtain ⟨b, D, pair', _⟩ := (h.nodes v).mp (ht.input_mem_of_pairMember hvH)
    obtain ⟨m, n, r, g, hm, hn, hr, hb, hra, hg, pull⟩ := h.representatives u v a b B D pair pair' edge f hf
    exact ep_repr_pull_l hZF h' limit' hm hn hr hb hra (pull.mono_l inside) fe (any v b D g H pair' hg hvH)
  have fiber u v a E H (hua : Rd_entry_d u a p) (hva : Rd_entry_d v a p)
      (huE : Rd_entry_d u E t) (hvH : Rd_entry_d v H t) :
      (u = v ↔ E = H) ∧ (Rd_entry_d u v V ↔ Rd_entry_d E H W') := by
    obtain ⟨B, pair, _⟩ := h.toEp_graph_d.label_l hua
    obtain ⟨D, pair', _⟩ := h.toEp_graph_d.label_l hva
    obtain ⟨_, a₀, B₀, f, pair₀, hf, fe⟩ := (spec u E).mp huE
    obtain ⟨ea, eb⟩ := kpair_injective_l M pair₀ pair
    subst a₀ B₀
    obtain ⟨_, a₁, D₀, g, pair₁, hg, gh⟩ := (spec v H).mp hvH
    obtain ⟨ea, ed⟩ := kpair_injective_l M pair₁ pair'
    subst a₁ D₀
    obtain ⟨E₀, _, hu₀⟩ := limit.projection.2.1 u (ht.input_mem_of_pairMember huE)
    obtain ⟨H₀, _, hv₀⟩ := limit.projection.2.1 v (ht.input_mem_of_pairMember hvH)
    have fv : Ep_repr_d q a f E₀ := ⟨u, B, pair, hf, hu₀⟩
    obtain ⟨_, n, hno, ha, _⟩ := fv.source_l hZF family h limit
    obtain ⟨U, haU⟩ := family.total n a hno ha
    have compare := atoms a f g E₀ H₀ E H U haU fv ⟨v, D, pair', hg, hv₀⟩ fe gh
    exact ⟨((limit.kernel u v E₀ H₀ hu₀ hv₀).trans (h.diagram.eq_at_l hua hva)).symm.trans compare.1,
      ((limit.relation u v E₀ H₀ hu₀ hv₀).trans (h.diagram.rel_at_l hua hva
        (h.diagram.identity u (ht.input_mem_of_pairMember huE)) (h.diagram.identity v (ht.input_mem_of_pairMember hvH)))).symm.trans compare.2⟩
  obtain ⟨g, hg, gs, rel, _⟩ := di_factor_embedding_l hZF h.diagram limit
    (fn0_of_function_l (ZF.modelsKP hZF) ht) comm fiber
  refine ⟨g, hg, rel, fun a f E E' old => ?_⟩
  obtain ⟨u, B, pair, hf, huE⟩ := old
  constructor
  · intro hEE
    obtain ⟨H, _, huH⟩ := ht.2.2 u (limit.projection.bound_l huE).1
    exact hg.1.1.2 E H E' (gs u E H huE huH) hEE ▸ any u a B f H pair hf huH
  · intro value
    exact gs u E E' huE ((spec u E').mpr ⟨(limit.projection.bound_l huE).1, a, B, f, pair, hf, value⟩)

end YesMetaZFC.SetTheory.LargeCardinal
