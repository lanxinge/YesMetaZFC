import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRawAssembly

/-! # 全部原关系支撑的实际初等极限

规范分量图、既有坐标过渡和标签同构共同给出一个实际定向系统。
原源的常值图经空支撑分量进入极限，并返回同一原始模型的复合初等图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_ultrapower_l {ω c X R c' Y S q B H N κ K L F R₀ Γ γ k : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q) (hBH : Rd_entry_d B H q)
    (trans : M.TransitiveSet B) (small : Sc_small_d X B)
    (closed : ∀ a b, M.mem a B → M.mem b X → M.MemberSubset b a → M.mem b B)
    (owner : Ep_source_d hZF ω κ K N R₀) (hΓ : M.mem Γ N) (rank : Vr_d N γ Γ)
    (hγ : M.IsLimitOrdinal γ) (hκ : M.mem κ Γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (family : Em_source_d ω κ L N F) (coherent : Ec_source_d I ω κ L N F) (above : M.MemberSubset ω L) :
    ∃ J O Z A p T V r o C W i q', Er_system_d I ω κ L Y S F k J O Z A p T V ∧
      Di_limit_d A p T V r C W ∧ Smdl_d I o C W ∧ Di_elementary_d I ω O A p T V ∧
      Smap_d I ω c' o Y C i ∧ Smap_d I ω c o X C q' ∧
      (∀ x z, Rd_entry_d x z q' ↔ M.mem x X ∧ ∃ y, Rd_entry_d x y q ∧ Rd_entry_d y z i) ∧
      ∃ a D, (∀ z, ¬ M.mem z a) ∧ Ep_space_d κ a D ∧
        ∀ x E, Rd_entry_d x E i → ∃ B f u, Fn0_d D Y f ∧ M.mem f B ∧ Rs_const_d D x f ∧
          KPair_d M u a B ∧ Rd_entry_d u E r := by
  obtain ⟨J, O, indices, order, os⟩ := ei_order_l hZF hω above
  obtain ⟨Z, Q, hz, components⟩ := er_components_l hZF hω hX mx theory collection model hq hBH trans small closed
    owner hΓ rank hγ hκ fk image pred family (fun a ha => (indices a).mp ha)
  obtain ⟨A, p, T, V, graph⟩ := eg_graphs_l hZF (κ := κ) (X := Y) order os indices hz
  have maps {a b o₀ o₁ m n r : M.Domain} := er_component_map_l hZFC hω hX mx theory collection model hq hBH trans small closed
    owner hΓ rank hγ fk image pred family coherent (a := a) (b := b) (o₀ := o₀) (o₁ := o₁) (m := m) (n := n) (r := r)
  have transition : Eg_transition_d I ω κ L Y O Z := by
    intro a b hab
    obtain ⟨ha, hb, t, m, n, hm, hn, ft, fb, fta⟩ := (os a b).mp hab
    obtain ⟨c₀, _, hac⟩ := hz.2.1 a ha
    obtain ⟨c₁, _, hbd⟩ := hz.2.1 b hb
    obtain ⟨_, _, _, inj⟩ := (indices b).mp hb
    obtain ⟨j, C₀, T₀, C₁, T₁, mc₀, mc₁, embed, spec, lift, _⟩ :=
      maps hm hn ft fb inj fta (components a c₀ hac) (components b c₁ hbd)
    exact ⟨j, c₀, C₀, T₀, c₁, C₁, T₁, hac, hbd, mc₀, mc₁, embed, spec, lift⟩
  have reps a B (hat : Ep_at_d Z a B) : ∃ n, M.mem n ω ∧ Fn0_d n L a ∧
      (∃ f, M.mem f B) ∧ ∀ f, M.mem f B → Ep_fun_d κ Y n f := by
    obtain ⟨o, C, W, hao, pair, hB⟩ := hat
    obtain ⟨n, D, U, _, _, G, s, C', W', hn, fa, space, haU, _, _, functions, quotient⟩ := components a o hao
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair quotient.code.1
    have measure := (family.at_l hZF.1 haU fa space).base
    obtain ⟨f, hfp⟩ := (quotient.map.range B).mp hB
    exact ⟨n, hn, fa, ⟨f, quotient.map.representative_l I measure hfp⟩, fun g hg =>
      ⟨D, space, ((functions g).mp (quotient.map.projection.input_mem_of_pairMember
        (quotient.map.member_l I hZF.1 measure hB hg))).1⟩⟩
  obtain ⟨diagram, lifts⟩ := graph.system_l hZF hω reps transition
  have elementary := graph.elementary_l hZF hω transition
  obtain ⟨a, empty, haω⟩ := hω.1.1
  have fa : Fn0_d a L a := ⟨fun x hx => (empty x hx).elim, fun x hx => (empty x hx).elim, fun x hx => (empty x hx).elim⟩
  have inj i j x (h : Rd_entry_d i x a) (_ : Rd_entry_d j x a) : i = j := h.elim fun z hz => (empty z hz.2).elim
  have haJ := (indices a).mpr ⟨a, haω, fa, inj⟩
  obtain ⟨o₀, _, hao⟩ := hz.2.1 a haJ
  have aa : Fn0_d a a a := ⟨fun x hx => (empty x hx).elim, fun x hx => (empty x hx).elim, fun x hx => (empty x hx).elim⟩
  obtain ⟨_, C₀, T₀, _, _, mc₀, _, _, _, _, i₀, D, space, hi₀, const⟩ :=
    maps haω haω aa fa inj ⟨fa, fun x hx => (empty x hx).elim⟩ (components a o₀ hao) (components a o₀ hao)
  obtain ⟨B₀, hB₀⟩ := mc₀.2.1
  obtain ⟨u, pair⟩ := (I).total a B₀
  have hu := (graph.nodes u).mpr ⟨a, B₀, pair, o₀, C₀, T₀, hao, mc₀.1, hB₀⟩
  obtain ⟨o, r, C, W, limit, mc⟩ := di_model_exists_l hZF diagram ⟨u, hu⟩
  obtain ⟨v, hv, values⟩ := ep_stage_embedding_l hZF hω graph diagram limit elementary mc hao mc₀
  obtain ⟨i, hi, square⟩ := smap_comp_l I hZF hi₀ hv
  obtain ⟨q', hq', composition⟩ := smap_comp_l I hZF hq hi
  refine ⟨J, O, Z, A, p, T, V, r, o, C, W, i, q', ⟨graph, components, diagram, lifts⟩,
    limit, mc, elementary, hi, hq', composition, a, D, empty, space, fun x E hxE => ?_⟩
  obtain ⟨_, B₁, hxB, hBE⟩ := (square x E).mp hxE
  obtain ⟨_, _, f, ff, hf, fc⟩ := (const x B₁).mp hxB
  obtain ⟨_, u, pair, huE⟩ := (values B₁ E).mp hBE
  exact ⟨B₁, f, u, ff, hf, fc, pair, huE⟩

end YesMetaZFC.SetTheory.LargeCardinal
