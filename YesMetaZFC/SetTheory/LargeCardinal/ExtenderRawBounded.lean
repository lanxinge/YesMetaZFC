import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRawLimit

/-! # 原关系定向极限的完整有界代表覆盖

任意新成员与原常值先移到共同支撑，再在同一原子测度下规范化。
共同低层回收所得内部函数码，最终得到所属源中的实际有界函数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_system_d.bounded_l {ω c X R c' Y S q B H N κ L F Γ γ k J O Z A p T V r C W
    A₀ b D₀ a₀ f₀ H₀ E : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (hBH : Rd_entry_d B H q)
    (closed : ∀ a b, M.mem a B → M.mem b X → M.MemberSubset b a → M.mem b B)
    (hN : M.TransitiveSet N) (algebra : Sc_algebra_d N) (hΓ : M.mem Γ N)
    (rank : Vr_d N γ Γ) (hγ : M.IsLimitOrdinal γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (family : Em_source_d ω κ L N F) (system : Er_system_d I ω κ L Y S F k J O Z A p T V)
    (limit : Di_limit_d A p T V r C W) (hAb : Rd_entry_d A₀ b k)
    (ff₀ : Fn0_d D₀ Y f₀) (constant : Rs_const_d D₀ b f₀) (fv : Ep_repr_d r a₀ f₀ H₀)
    (edge : Rd_entry_d E H₀ W) :
    ∃ n a D f g, M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧
      M.mem f N ∧ Fn0_d D A₀ f ∧ Cp0_d D Γ Y f k g ∧ Ep_repr_d r a g E := by
  obtain ⟨u, huE⟩ := (limit.range E).mp (limit.bounded E H₀ edge).1
  obtain ⟨v, B₀, pv, hfB₀, hvH⟩ := fv
  obtain ⟨a, w, z, hwa, hza, huw, hvz, hwz⟩ := (limit.relation u v E H₀ huE hvH).mp edge
  obtain ⟨P, pw, atP⟩ := system.toEg_graph_d.label_l hwa
  obtain ⟨Q, pz, atQ⟩ := system.toEg_graph_d.label_l hza
  obtain ⟨o, C₁, W₁, hao, component, mc, hPC⟩ := system.model_l hZF atP
  obtain ⟨_, hz⟩ := system.codes
  have hQC := (ep_at_read_l hz hao mc.1).mp atQ
  have rel := (ep_rel_read_l hz hao mc.1).mp ((system.toEg_graph_d.relation_l pw pz).mp hwz).2.2
  obtain ⟨n, D, U, d, t, G, s, C₂, W₂, hn, fa, space, haU, hDd, ht, functions, quotient⟩ := component
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I quotient.code mc
  have measure := family.at_l hZF.1 haU fa space
  -- 原常值沿同一实际支撑箭头拉回，仍是新分量中的处处常值。
  obtain ⟨m, n', t₀, f', _, _, ft₀, fa', fta₀, hfQ, pull⟩ :=
    system.representatives v z a₀ a B₀ Q pv pz hvz f₀ hfB₀
  have eq := fa'.domain_eq_l hZF.1 fa
  subst n'
  obtain ⟨D', space₀, ff⟩ := pull.1
  have eq := ff.domain_eq_l hZF.1 ff₀
  subst D'
  have fc : Rs_const_d D b f' := by
    intro s hs
    obtain ⟨v, comp⟩ := cp0_exists_l (ZF.modelsKP hZF) ft₀ ((space s).mp hs)
    exact (pull.2.2 s v ((space s).mp hs) comp b).mpr (constant v ((space₀ v).mpr comp.1))
  have fp := quotient.map.member_l I hZF.1 measure.base hQC hfQ
  have low := rank.transitive_l hZF hN hΓ
  have ft := fn0_of_function_l (ZF.modelsKP hZF) (ht.isSetFunctionFromTo fk.1 (low D (fk.1.input_mem_of_pairMember hDd)))
  have domain s x (hsx : Rd_entry_d s x t) := (pred D d hDd x).mpr
    ⟨s, ((ht.2 s x).mp hsx).1, ((ht.2 s x).mp hsx).2⟩
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω mx.1 model (rf_ext_mem_l I hZF.1 hX mx)
  let d' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨d, fk.1.output_mem_of_pairMember hDd⟩
  let b' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨b, fk.1.output_mem_of_pairMember hAb⟩
  have codes := (rc_family_native_l I model.2.1 (ext.native_l I model.2.1) d' ft).mp functions
  obtain ⟨g, hg, gp, bound⟩ := rc_bounded_representative_l hZF hω hX mx theory model hq d' ft domain
    measure.base measure.proper codes quotient ⟨b'.property, f', quotient.map.projection.input_mem_of_pairMember fp, fc, fp⟩ rel
  obtain ⟨f, hf, fn, comp⟩ := (hq.bounded_functions_raw_l hZF hω hX mx model hBH closed hN algebra hΓ rank hγ
    fk image pred d' b' hDd hAb ht codes g).mp ⟨hg, bound⟩
  obtain ⟨E', _, hwE⟩ := limit.projection.2.1 w (system.projection.bound_l hwa).1
  have eq := limit.commute_l system.diagram huw huE hwE
  exact ⟨n, a, D, f, g, hn, (system.projection.bound_l hwa).2, fa, space, hf, fn, comp,
    w, P, pw, quotient.map.representative_l I measure.base gp, eq.symm ▸ hwE⟩

theorem Er_system_d.bound_mem_l {ω κ L N Y S F k J O Z A p T V r C W D₀ b a₀ f₀ H₀ a g E : M.Domain}
    (family : Em_source_d ω κ L N F) (system : Er_system_d I ω κ L Y S F k J O Z A p T V)
    (limit : Di_limit_d A p T V r C W) (hb : M.mem b Y)
    (ff₀ : Fn0_d D₀ Y f₀) (constant : Rs_const_d D₀ b f₀) (fv : Ep_repr_d r a₀ f₀ H₀)
    (bound : ∀ s y, Rd_entry_d s y g → Rd_entry_d y b S) (gv : Ep_repr_d r a g E) : Rd_entry_d E H₀ W := by
  obtain ⟨u, B, pu, hgB, huE⟩ := gv
  obtain ⟨v, B₀, pv, hfB₀, hvH⟩ := fv
  obtain ⟨c, w, z, hwc, hzc, huw, hvz⟩ := system.diagram.common_l (limit.projection.bound_l huE).1 (limit.projection.bound_l hvH).1
  obtain ⟨P, pw, atP⟩ := system.toEg_graph_d.label_l hwc
  obtain ⟨Q, pz, atQ⟩ := system.toEg_graph_d.label_l hzc
  obtain ⟨o, C₁, W₁, hco, component, mc, hPC⟩ := system.model_l hZF atP
  obtain ⟨_, hz⟩ := system.codes
  have hQC := (ep_at_read_l hz hco mc.1).mp atQ
  obtain ⟨n, D, U, _, _, G, s, C₂, W₂, _, fc, space, hcU, _, _, _, quotient⟩ := component
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I quotient.code mc
  have measure := (family.at_l hZF.1 hcU fc space).base
  obtain ⟨m, n', t, g', _, _, ft, fc', _, hgP, pg⟩ := system.representatives u w a c B P pu pw huw g hgB
  have eq := fc'.domain_eq_l hZF.1 fc
  subst n'
  obtain ⟨l, n', t₀, f', _, _, ft₀, fc', _, hfQ, pf⟩ := system.representatives v z a₀ c B₀ Q pv pz hvz f₀ hfB₀
  have eq := fc'.domain_eq_l hZF.1 fc
  subst n'
  obtain ⟨D', ds₀, ff⟩ := pf.1
  have eq := ff.domain_eq_l hZF.1 ff₀
  subst D'
  have gp := quotient.map.member_l I hZF.1 measure hPC hgP
  have fp := quotient.map.member_l I hZF.1 measure hQC hfQ
  have fg := quotient.map.functions g' (quotient.map.projection.input_mem_of_pairMember gp)
  have relation := (quotient.relation g' f' P Q gp fp).mpr ⟨D, measure.top, fun s hs => by
    have sf := (space s).mp hs
    obtain ⟨v, tv⟩ := cp0_exists_l (ZF.modelsKP hZF) ft sf
    obtain ⟨v₀, tv₀⟩ := cp0_exists_l (ZF.modelsKP hZF) ft₀ sf
    obtain ⟨y, hy, hsy⟩ := fg.2.1 s hs
    exact ⟨y, hy, b, hb, hsy, (pf.2.2 s v₀ sf tv₀ b).mpr (constant v₀ ((ds₀ v₀).mpr tv₀.1)),
      bound v y ((pg.2.2 s v sf tv y).mp hsy)⟩⟩
  exact (limit.relation u v E H₀ huE hvH).mpr ⟨c, w, z, hwc, hzc, huw, hvz,
    (system.toEg_graph_d.relation_l pw pz).mpr ⟨(system.projection.bound_l hwc).1,
      (system.projection.bound_l hzc).1, (ep_rel_read_l hz hco mc.1).mpr relation⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
