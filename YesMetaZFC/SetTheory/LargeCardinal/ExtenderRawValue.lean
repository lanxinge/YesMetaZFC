import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRawBounded

/-! # 共同有界代表在原关系极限中的实际求值

所属源的函数先与低层实现复合，再读取同一规范商与极限投影。
同支撑原子方程始终使用原测度。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_repr_atoms_l {ω κ L N Y S F k J O Z A p T V r C W a f g E H U : M.Domain}
    (family : Em_source_d ω κ L N F) (h : Er_system_d I ω κ L Y S F k J O Z A p T V)
    (limit : Di_limit_d A p T V r C W) (haU : Rd_entry_d a U F)
    (he : Ep_repr_d r a f E) (hh : Ep_repr_d r a g H) :
    (E = H ↔ Rp_eq_d Y U f g) ∧ (Rd_entry_d E H W ↔ Rp_rel_d I Y U S f g) := by
  obtain ⟨u, B, hu, hf, huE⟩ := he
  obtain ⟨v, D, hv, hg, hvH⟩ := hh
  have huA := (limit.projection.bound_l huE).1
  have hvA := (limit.projection.bound_l hvH).1
  have hua := (h.index u a B hu).mpr huA
  have hva := (h.index v a D hv).mpr hvA
  obtain ⟨_, hz⟩ := h.codes
  obtain ⟨o, Q, R, hao, component, model, hBQ⟩ := h.model_l hZF (h.toEg_graph_d.at_l huA hu)
  have hDQ := (ep_at_read_l hz hao model.1).mp (h.toEg_graph_d.at_l hvA hv)
  obtain ⟨n, Q₀, U₀, _, _, G, s, Q', R', _, fa, space, haU₀, _, _, _, md⟩ := component
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I md.code model
  have eq := family.function a U₀ U haU₀ haU
  subst U₀
  have measure := (family.at_l hZF.1 haU fa space).base
  have fp := md.map.member_l I hZF.1 measure hBQ hf
  have gp := md.map.member_l I hZF.1 measure hDQ hg
  have same : u = v ↔ B = D := ⟨fun eq => (kpair_injective_l M (eq ▸ hu) hv).2,
    fun eq => kpair_unique_l M hZF.1 (eq ▸ hu) hv⟩
  refine ⟨(limit.kernel u v E H huE hvH).trans ((h.diagram.eq_at_l hua hva).trans
    (same.trans (rp_kernel_l I hZF.1 measure md.map fp gp))), ?_⟩
  exact (limit.relation u v E H huE hvH).trans
    ((h.diagram.rel_at_l hua hva (h.diagram.identity u huA) (h.diagram.identity v hvA)).trans
      ((h.toEg_graph_d.relation_l hu hv).trans
        ((and_congr_right fun _ => and_congr_right fun _ => ep_rel_read_l hz hao model.1).trans
          ((and_iff_right huA).trans ((and_iff_right hvA).trans (md.relation f g B D fp gp))))))

theorem Er_system_d.bounded_value_l {ω c X R c' Y S q H N κ L F Γ γ k J O Z A p T V r C W
    A₀ b n a D f : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (closed : Rr_closed_d I Y S H)
    (hN : M.TransitiveSet N) (algebra : Sc_algebra_d N) (hΓ : M.mem Γ N)
    (rank : Vr_d N γ Γ) (hγ : M.IsLimitOrdinal γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (family : Em_source_d ω κ L N F) (system : Er_system_d I ω κ L Y S F k J O Z A p T V)
    (limit : Di_limit_d A p T V r C W) (hAb : Rd_entry_d A₀ b k)
    (ha : M.mem a J) (fa : Fn0_d n L a) (space : Ep_space_d κ n D) (hf : M.mem f N) (ff : Fn0_d D A₀ f) :
    ∃ g E, Cp0_d D Γ Y f k g ∧ Ep_repr_d r a g E := by
  obtain ⟨_, hz⟩ := system.codes
  obtain ⟨o, _, hao⟩ := hz.2.1 a ha
  obtain ⟨n', D', U, d, t, G, s, C₁, W₁, _, fa', space', haU, hDd, ht, functions, quotient⟩ := system.components a o hao
  have eq := fa'.domain_eq_l hZF.1 fa
  subst n'
  have eq := hZF.1.eq_of_same_members D' D (fun s => (space' s).trans (space s).symm)
  subst D'
  have low := rank.transitive_l hZF hN hΓ
  have ft := fn0_of_function_l (ZF.modelsKP hZF) (ht.isSetFunctionFromTo fk.1 (low D (fk.1.input_mem_of_pairMember hDd)))
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω mx.1 model (rf_ext_mem_l I hZF.1 hX mx)
  let d' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨d, fk.1.output_mem_of_pairMember hDd⟩
  let b' : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨b, fk.1.output_mem_of_pairMember hAb⟩
  have codes := (rc_family_native_l I model.2.1 (ext.native_l I model.2.1) d' ft).mp functions
  obtain ⟨g, comp⟩ := cp0_exists_l (ZF.modelsKP hZF) (ff.mono_target_l (low A₀ (fk.1.input_mem_of_pairMember hAb)))
    (fn0_of_function_l (ZF.modelsKP hZF) fk.1)
  have hg := ((rr_bounded_functions_l hZF model.2.1 ext closed hN algebra hΓ rank hγ
    fk image pred d' b' hDd hAb ht codes g).mpr ⟨f, hf, ff, comp⟩).1
  obtain ⟨B₁, hB₁, gp⟩ := quotient.map.projection.2.2 g hg
  obtain ⟨u, pair⟩ := (I).total a B₁
  obtain ⟨E, _, huE⟩ := limit.projection.2.1 u ((system.nodes u).mpr ⟨a, B₁, pair, o, C₁, W₁, hao, quotient.code.1, hB₁⟩)
  exact ⟨g, E, comp, u, B₁, pair, quotient.map.representative_l I (family.at_l hZF.1 haU fa space).base gp, huE⟩

theorem Er_system_d.reindex_l {ω κ L Y S F k J O Z A p T V r C W m n a b t f E : M.Domain}
    (system : Er_system_d I ω κ L Y S F k J O Z A p T V) (limit : Di_limit_d A p T V r C W)
    (hm : M.mem m ω) (hn : M.mem n ω) (ft : Fn0_d m n t) (hb : M.mem b J)
    (fb : Fn0_d n L b) (fta : Cp0_d m n L t b a) (value : Ep_repr_d r a f E) :
    ∃ g, Ep_pull_d κ Y m n t f g ∧ Ep_repr_d r b g E := by
  obtain ⟨u, B, pu, hf, huE⟩ := value
  have hua := (system.index u a B pu).mpr (limit.projection.bound_l huE).1
  have ab := (system.order_spec a b).mpr ⟨(system.projection.bound_l hua).2, hb, t, m, n, hm, hn, ft, fb, fta⟩
  obtain ⟨v, hvb, huv⟩ := system.diagram.total u a b hua ab
  obtain ⟨P, pv, _⟩ := system.toEg_graph_d.label_l hvb
  obtain ⟨m', n', t', g, _, _, ft', fb', fta', hg, pull⟩ := system.representatives u v a b B P pu pv huv f hf
  have eq := fb'.domain_eq_l hZF.1 fb
  subst n'
  have eq := fta'.1.domain_eq_l hZF.1 fta.1
  subst m'
  obtain ⟨_, _, _, inj⟩ := (system.indices b).mp hb
  have eq := ec_factor_unique_l hZF.1 inj ft' ft fta' fta
  subst t'
  obtain ⟨E', _, hvE⟩ := limit.projection.2.1 v (system.projection.bound_l hvb).1
  exact ⟨g, pull, v, P, pv, hg, (limit.commute_l system.diagram huv huE hvE).symm ▸ hvE⟩

/-- 不同支撑的同一处处常值在原关系极限中有同一个值。 -/
theorem Er_system_d.constant_l {ω κ L N Y S F k J O Z A p T V r C W D E x a b f g H P : M.Domain}
    (family : Em_source_d ω κ L N F) (system : Er_system_d I ω κ L Y S F k J O Z A p T V)
    (limit : Di_limit_d A p T V r C W) (ff : Fn0_d D Y f) (fg : Fn0_d E Y g)
    (fc : Rs_const_d D x f) (gc : Rs_const_d E x g) (fv : Ep_repr_d r a f H) (gv : Ep_repr_d r b g P) : H = P := by
  obtain ⟨u, B, pu, hf, huH⟩ := fv
  obtain ⟨v, B', pv, hg, hvP⟩ := gv
  obtain ⟨c, w, z, hwc, hzc, huw, hvz⟩ := system.diagram.common_l (limit.projection.bound_l huH).1 (limit.projection.bound_l hvP).1
  obtain ⟨Q, pw, atQ⟩ := system.toEg_graph_d.label_l hwc
  obtain ⟨Q', pz, atQ'⟩ := system.toEg_graph_d.label_l hzc
  obtain ⟨o, C₀, W₀, hco, component, mc, hQC⟩ := system.model_l hZF atQ
  obtain ⟨_, hz⟩ := system.codes
  have hQ'C := (ep_at_read_l hz hco mc.1).mp atQ'
  obtain ⟨n, D₀, U, _, _, G, s, C₁, W₁, _, fn, space, hcU, _, _, _, quotient⟩ := component
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I quotient.code mc
  have measure := (family.at_l hZF.1 hcU fn space).base
  have lift {D a B u f} (ff : Fn0_d D Y f) (fc : Rs_const_d D x f)
      (pu : KPair_d M u a B) (hf : M.mem f B) {Q w} (pw : KPair_d M w c Q) (huw : Rd_entry_d u w T) :
      ∃ g, M.mem g Q ∧ Rs_const_d D₀ x g := by
    obtain ⟨m, n', t, g, _, _, ft, fn', _, hg, pull⟩ := system.representatives u w a c B Q pu pw huw f hf
    have eq := fn'.domain_eq_l hZF.1 fn
    subst n'
    obtain ⟨D', ds, ff'⟩ := pull.1
    have eq := ff'.domain_eq_l hZF.1 ff
    subst D'
    refine ⟨g, hg, fun v hv => ?_⟩
    obtain ⟨t₀, comp⟩ := cp0_exists_l (ZF.modelsKP hZF) ft ((space v).mp hv)
    exact (pull.2.2 v t₀ ((space v).mp hv) comp x).mpr (fc t₀ ((ds t₀).mpr comp.1))
  obtain ⟨f', hf', fc'⟩ := lift ff fc pu hf pw huw
  obtain ⟨g', hg', gc'⟩ := lift fg gc pv hg pz hvz
  have sf := quotient.map.member_l I hZF.1 measure hQC hf'
  have sg := quotient.map.member_l I hZF.1 measure hQ'C hg'
  have fnf := quotient.map.functions f' (quotient.map.projection.input_mem_of_pairMember sf)
  have eq := (rp_kernel_l I hZF.1 measure quotient.map sf sg).mpr
    ⟨D₀, measure.top, fun s hs => ⟨x, (fnf.bound_l (fc' s hs)).2, fc' s hs, gc' s hs⟩⟩
  have wz := kpair_unique_l M hZF.1 pw (eq.symm ▸ pz)
  exact (limit.kernel u v H P huH hvP).mpr ⟨w, huw, wz.symm ▸ hvz⟩

end YesMetaZFC.SetTheory.LargeCardinal
