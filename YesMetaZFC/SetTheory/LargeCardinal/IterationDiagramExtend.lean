import YesMetaZFC.SetTheory.LargeCardinal.IterationNextMaps

/-! # 添枝后完整初等图的交换律

新增模型和全部新增箭头一起构造。旧三角形沿用原交换律；经过新结点的
三角形展开成一次末边复合，逐值计算即得交换，不添加交换律假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_diagram_extend_l {ω α ξ T Q G k c X R d Y S t : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d hZF ω α T Q G) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d k c Q) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (ht : Smap_d I ω c d X Y t) :
    ∃ β U Q' G' e, M.SuccessorOf β α ∧ It_diagram_d hZF ω β U Q' G' ∧
      (∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ Rd_entry_d i k T)) ∧
      (∀ i b, Rd_entry_d i b Q' ↔ Rd_entry_d i b Q ∨ i = α ∧ b = d) ∧
      (∀ i j f, It_map_d G' i j f ↔ It_next_d α k G e t i j f) ∧ It_map_d G' k α t := by
  have hk := (h.model_domain k).mpr ⟨c, hc⟩
  have no : ¬ M.mem α α := fun ha => h.order.ordinal.wellOrder.linear.irrefl α ha ha
  obtain ⟨β, U, hβ, order, us⟩ := it_order_extend_l (ZF.modelsKP hZF) h.order hα hk
  obtain ⟨Q', hQ', qs⟩ := Structure.IsSequenceOfLength.exists_append (value := d) (ZF.modelsKP hZF) I
    ⟨h.order.ordinal, h.model_function, h.model_domain⟩ order.ordinal hβ
  have qold i b (hi : M.mem i α) : Rd_entry_d i b Q' ↔ Rd_entry_d i b Q := (qs i b).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hi)).elim), Or.inl⟩
  have qtip b : Rd_entry_d α b Q' ↔ b = d := (qs α b).trans
    ⟨fun hh => hh.elim (fun hh => (no ((h.model_domain α).mpr ⟨b, hh⟩)).elim) And.right,
      fun hh => Or.inr ⟨rfl, hh⟩⟩
  obtain ⟨e, he, es⟩ := smap_identity_l I hZF (c := d) (X := Y) hω
  obtain ⟨G', gfun, gdom, gs⟩ := it_next_maps_l hZF h hc mx ht (e := e) us order.relation
  have gold i j f (hj : M.mem j α) : It_map_d G' i j f ↔ It_map_d G i j f := (gs i j f).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hj)).elim), Or.inl⟩
  have gtip i f : It_map_d G' i α f ↔ (i = α ∧ f = e) ∨ ∃ g, It_map_d G i k g ∧ It_comp_d g t f :=
    (gs i α f).trans ⟨fun hh => hh.elim (fun hh => (no (h.order.bound i α (h.map_bound_l hZF hh)).2).elim) And.right,
      fun hh => Or.inr ⟨rfl, hh⟩⟩
  have typed i j f b Z V b' Z' V' (hf : It_map_d G' i j f) (hb : Rd_entry_d i b Q') (hb' : Rd_entry_d j b' Q')
      (mb : Smdl_d I b Z V) (mb' : Smdl_d I b' Z' V') : Smap_d I ω b b' Z Z' f := by
    rcases (gs i j f).mp hf with hf | ⟨rfl, ⟨rfl, rfl⟩ | ⟨g, hg, comp⟩⟩
    · have hij := h.order.bound i j (h.map_bound_l hZF hf)
      exact h.elementary i j f b Z V b' Z' V' hf ((qold i b hij.1).mp hb) ((qold j b' hij.2).mp hb') mb mb'
    · have eb := (qtip b).mp hb
      have eb' := (qtip b').mp hb'
      subst b b'
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I mb my
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I mb' my
      exact he
    · have eb' := (qtip b').mp hb'
      subst b'
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I mb' my
      have gi := h.elementary i k g b Z V c X R hg
        ((qold i b (h.order.bound i k (h.map_bound_l hZF hg)).1).mp hb) hc mb mx
      obtain ⟨f', hf', spec⟩ := it_comp_elementary_l hZF gi ht
      exact spec.unique_l hZF.1 comp ▸ hf'
  have ident i f (hf : It_map_d G' i i f) x y (hxy : Rd_entry_d x y f) : x = y := by
    rcases (gs i i f).mp hf with hf | ⟨rfl, ⟨_, rfl⟩ | ⟨g, hg, _⟩⟩
    · exact h.identity i f hf x y hxy
    · exact ((es x y).mp hxy).2
    · exact (no (h.order.bound _ k (h.map_bound_l hZF hg)).1).elim
  have commute i j l f g v (hf : It_map_d G' i j f) (hg : It_map_d G' j l g) (hv : It_map_d G' i l v)
      x y z (hxy : Rd_entry_d x y f) (hyz : Rd_entry_d y z g) : Rd_entry_d x z v := by
    rcases (gs j l g).mp hg with hg₀ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨g₀, hg₀, cg⟩⟩
    · obtain ⟨hj, hl⟩ := h.order.bound j l (h.map_bound_l hZF hg₀)
      exact h.comp i j l f g v ((gold i j f hj).mp hf) hg₀ ((gold i l v hl).mp hv) x y z hxy hyz
    · have eq := it_next_unique_l hZF h ((gs i _ f).mp hf) ((gs i _ v).mp hv)
      exact eq ▸ ((es y z).mp hyz).2 ▸ hxy
    · have hf₀ := (gold i j f (h.order.bound j k (h.map_bound_l hZF hg₀)).1).mp hf
      rcases (gtip i v).mp hv with ⟨rfl, _⟩ | ⟨v₀, hv₀, cv⟩
      · exact (no (h.order.bound _ j (h.map_bound_l hZF hf₀)).1).elim
      · obtain ⟨w, hyw, hwz⟩ := (cg.2 y z).mp hyz
        exact (cv.2 x z).mpr ⟨w, h.comp i j k f g₀ v₀ hf₀ hg₀ hv₀ x y w hxy hyw, hwz⟩
  have diagram : It_diagram_d hZF ω β U Q' G' := ⟨order, hQ'.2.1, hQ'.2.2, fun i b hb => by
      rcases (qs i b).mp hb with hb | ⟨rfl, rfl⟩
      · exact h.models i b hb
      · exact ⟨Y, S, my⟩,
    gfun, gdom, typed, ident, commute⟩
  obtain ⟨f, hf⟩ := h.map_l hZF (h.order.refl k hk)
  have ff := h.elementary k k f c X R c X R hf hc hc mx mx
  have idcomp : It_comp_d f t t := ⟨ht.1.1.1.1, fun x y => ⟨fun hxy => by
    obtain ⟨z, _, hxz⟩ := ff.1.1.2.2 x (ht.1.1.input_mem_of_pairMember hxy)
    exact ⟨x, (h.identity k f hf x z hxz).symm ▸ hxz, hxy⟩,
    fun ⟨z, hxz, hzy⟩ => (h.identity k f hf x z hxz).symm ▸ hzy⟩⟩
  exact ⟨β, U, Q', G', e, hβ, diagram, us, qs, gs,
    (gtip k t).mpr (Or.inr ⟨f, hf, idcomp⟩)⟩

end YesMetaZFC.SetTheory.LargeCardinal
