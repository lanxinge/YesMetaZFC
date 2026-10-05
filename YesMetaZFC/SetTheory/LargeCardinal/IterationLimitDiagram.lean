import YesMetaZFC.SetTheory.LargeCardinal.IterationLimitMaps

/-! # 极限添枝后的完整初等图与交换律 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_limit_diagram_l {ω α T Q G B d N W P : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d hZF ω α T Q G) (hl : M.IsLimitOrdinal α)
    (b : It_branch_d α T B) (cone : It_cone_d hZF ω B Q G d N W P) :
    ∃ β U Q' G' e, M.SuccessorOf β α ∧ It_diagram_d hZF ω β U Q' G' ∧
      (∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B)) ∧
      (∀ i c, Rd_entry_d i c Q' ↔ Rd_entry_d i c Q ∨ i = α ∧ c = d) ∧
      ∀ i j f, It_map_d G' i j f ↔ It_finish_d α G P e i j f := by
  have no : ¬ M.mem α α := fun ha => h.order.ordinal.wellOrder.linear.irrefl α ha ha
  obtain ⟨β, U, hβ, order, us⟩ := it_limit_order_l (ZF.modelsKP hZF) h.order hl b
  obtain ⟨Q', qf, qs⟩ := Structure.IsSequenceOfLength.exists_append (value := d) (ZF.modelsKP hZF) I
    ⟨h.order.ordinal, h.model_function, h.model_domain⟩ order.ordinal hβ
  have qold i c (hi : M.mem i α) : Rd_entry_d i c Q' ↔ Rd_entry_d i c Q := (qs i c).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hi)).elim), Or.inl⟩
  have qtip c : Rd_entry_d α c Q' ↔ c = d := (qs α c).trans
    ⟨fun hh => hh.elim (fun hh => (no ((h.model_domain α).mpr ⟨c, hh⟩)).elim) And.right,
      fun hh => Or.inr ⟨rfl, hh⟩⟩
  obtain ⟨e, he, es⟩ := smap_identity_l I hZF (c := d) (X := N) hω
  obtain ⟨G', gf, gd, gs⟩ := it_finish_maps_l hZF h b.subset cone (e := e) us order.relation
  have gold i j f (hj : M.mem j α) : It_map_d G' i j f ↔ It_map_d G i j f := (gs i j f).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hj)).elim), Or.inl⟩
  have typed i j f c X R c' Y S (hf : It_map_d G' i j f) (hc : Rd_entry_d i c Q') (hc' : Rd_entry_d j c' Q')
      (mx : Smdl_d I c X R) (my : Smdl_d I c' Y S) : Smap_d I ω c c' X Y f := by
    rcases (gs i j f).mp hf with hf | ⟨rfl, ⟨rfl, rfl⟩ | hf⟩
    · have hij := h.order.bound i j (h.map_bound_l hZF hf)
      exact h.elementary i j f c X R c' Y S hf ((qold i c hij.1).mp hc) ((qold j c' hij.2).mp hc') mx my
    · have eq := (qtip c).mp hc
      have eq' := (qtip c').mp hc'
      subst c c'
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I mx cone.model
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I my cone.model
      exact he
    · have eq := (qtip c').mp hc'
      subst c'
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I my cone.model
      exact cone.elementary i f c X R hf ((qold i c (b.subset i ((cone.domain i).mpr ⟨f, hf⟩))).mp hc) mx
  have ident i f (hf : It_map_d G' i i f) x y (hxy : Rd_entry_d x y f) : x = y := by
    rcases (gs i i f).mp hf with hf | ⟨rfl, ⟨_, rfl⟩ | hf⟩
    · exact h.identity i f hf x y hxy
    · exact ((es x y).mp hxy).2
    · exact (no (b.subset _ ((cone.domain _).mpr ⟨f, hf⟩))).elim
  have commute i j k f g v (hf : It_map_d G' i j f) (hg : It_map_d G' j k g) (hv : It_map_d G' i k v)
      x y z (hxy : Rd_entry_d x y f) (hyz : Rd_entry_d y z g) : Rd_entry_d x z v := by
    rcases (gs j k g).mp hg with hg | ⟨rfl, ⟨rfl, rfl⟩ | hg⟩
    · obtain ⟨hj, hk⟩ := h.order.bound j k (h.map_bound_l hZF hg)
      exact h.comp i j k f g v ((gold i j f hj).mp hf) hg ((gold i k v hk).mp hv) x y z hxy hyz
    · have eq := it_finish_unique_l hZF h b.subset cone ((gs i _ f).mp hf) ((gs i _ v).mp hv)
      exact eq ▸ ((es y z).mp hyz).2 ▸ hxy
    · have hf₀ := (gold i j f (b.subset j ((cone.domain j).mpr ⟨g, hg⟩))).mp hf
      rcases (gs i _ v).mp hv with hv | ⟨_, ⟨rfl, _⟩ | hv⟩
      · exact (no (h.order.bound i _ (h.map_bound_l hZF hv)).2).elim
      · exact (no (h.order.bound _ j (h.map_bound_l hZF hf₀)).1).elim
      · exact cone.commute i j f v g hf₀ hv hg x y z hxy hyz
  exact ⟨β, U, Q', G', e, hβ, ⟨order, qf.2.1, qf.2.2, fun i c hc => by
      rcases (qs i c).mp hc with hc | ⟨_, rfl⟩
      · exact h.models i c hc
      · exact ⟨N, W, cone.model⟩,
    gf, gd, typed, ident, commute⟩, us, qs, gs⟩

end YesMetaZFC.SetTheory.LargeCardinal
