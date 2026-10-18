import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRawValue

/-! # 所属源有界关系与新极限关系的精确对应

两边使用同一个共同支撑和同一真实测度。值域只经已有低层实现搬运，
成员关系由完整前驱方程反映，不假设新极限良基。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_edge_iff_l {ω κ K L N R₀ Y S F Γ k J O Z A p T V r C W B U₀ R'
    m n a b D Q f g f' g' E H : M.Domain}
    (owner : Ep_source_d hZF ω κ K N R₀) (family : Em_source_d ω κ L N F)
    (system : Er_system_d I ω κ L Y S F k J O Z A p T V) (limit : Di_limit_d A p T V r C W)
    (fk : M.IsSetInjectionFromTo I k Γ Y) (sub : M.MemberSubset B Γ)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (membership : Rd_fun_d .mem B B B R') (measures : ∀ a U, Rd_entry_d a U F → M.mem U U₀)
    (hm : M.mem m ω) (hn : M.mem n ω) (fa : Fn0_d m L a) (fb : Fn0_d n L b)
    (space : Ep_space_d κ m D) (space' : Ep_space_d κ n Q) (ff : Fn0_d D B f) (gg : Fn0_d Q B g)
    (cf : Cp0_d D Γ Y f k f') (cg : Cp0_d Q Γ Y g k g')
    (fv : Ep_repr_d r a f' E) (gv : Ep_repr_d r b g' H) :
    Eb_edge_d ω κ L B J K U₀ R' F a f b g ↔ Rd_entry_d E H W := by
  have key := fn0_of_function_l (ZF.modelsKP hZF) fk.1
  have member x y x' y' (hx : M.mem x B) (hy : M.mem y B) (hxx : Rd_entry_d x x' k) (hyy : Rd_entry_d y y' k) :
      Rd_entry_d x y R' ↔ Rd_entry_d x' y' S :=
    (rt_mem_graph_l (ZF.modelsKP hZF) membership x y).trans
      ((and_iff_right hx).trans ((and_iff_right hy).trans
        ⟨fun h => (pred y y' hyy x').mpr ⟨x, h, hxx⟩, fun h => by
          obtain ⟨z, hz, hzx⟩ := (pred y y' hyy x').mp h
          exact fk.2 z x x' hzx hxx ▸ hz⟩))
  constructor
  · rintro ⟨c, hcJ, U, _, hcU, P, hPU, m', _, n', _, l, hl, s, _, t, _, fs, ft, fc, fsa, ftb, point⟩
    have eq := fsa.1.domain_eq_l hZF.1 fa
    subst m'
    have eq := ftb.1.domain_eq_l hZF.1 fb
    subst n'
    obtain ⟨f'', pf, fv'⟩ := system.reindex_l hZF limit hm hl fs hcJ fc fsa fv
    obtain ⟨g'', pg, gv'⟩ := system.reindex_l hZF limit hn hl ft hcJ fc ftb gv
    obtain ⟨D₁, _, ds⟩ := owner.space_l hZF hl
    have measure := (family.at_l hZF.1 hcU fc ds).base
    apply (er_repr_atoms_l hZF family system limit hcU fv' gv').2.mpr
    refine ⟨P, hPU, fun v hv => ?_⟩
    obtain ⟨s₀, _, t₀, _, x, hx, y, hy, sv, tv, sx, ty, xy⟩ := point v hv
    obtain ⟨x', hx', hxx⟩ := fk.1.2.2 x (sub x hx)
    obtain ⟨y', hy', hyy⟩ := fk.1.2.2 y (sub y hy)
    have vf := (ds v).mp (measure.bounds P hPU v hv)
    exact ⟨x', hx', y', hy', (pf.2.2 v s₀ vf sv x').mpr ((cf.value_l (ff.mono_target_l sub) key sx).mpr hxx),
      (pg.2.2 v t₀ vf tv y').mpr ((cg.value_l (gg.mono_target_l sub) key ty).mpr hyy),
      (member x y x' y' hx hy hxx hyy).mp xy⟩
  · intro edge
    obtain ⟨u, P₀, pu, hfP, huE⟩ := fv
    obtain ⟨v, P₁, pv, hgP, hvH⟩ := gv
    obtain ⟨c, w, z, hwc, hzc, huw, hvz, hwz⟩ := (limit.relation u v E H huE hvH).mp edge
    obtain ⟨P, pw, atP⟩ := system.toEg_graph_d.label_l hwc
    obtain ⟨Q₁, pz, atQ⟩ := system.toEg_graph_d.label_l hzc
    obtain ⟨m', l, s, f'', _, hl, fs, fc, fsa, hfP', pf⟩ := system.representatives u w a c P₀ P pu pw huw f' hfP
    obtain ⟨n', l', t, g'', _, _, ft, fc', ftb, hgQ', pg⟩ := system.representatives v z b c P₁ Q₁ pv pz hvz g' hgP
    have eq := fsa.1.domain_eq_l hZF.1 fa
    subst m'
    have eq := ftb.1.domain_eq_l hZF.1 fb
    subst n'
    have eq := fc'.domain_eq_l hZF.1 fc
    subst l'
    obtain ⟨o, C₁, W₁, hco, component, model, hPC⟩ := system.model_l hZF atP
    obtain ⟨_, hz⟩ := system.codes
    have hQC := (ep_at_read_l hz hco model.1).mp atQ
    have relation := (ep_rel_read_l hz hco model.1).mp ((system.toEg_graph_d.relation_l pw pz).mp hwz).2.2
    obtain ⟨l', D₁, U, _, _, G, q₀, C₂, W₂, _, fc', ds, hcU, _, _, _, quotient⟩ := component
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I quotient.code model
    have eq := fc'.domain_eq_l hZF.1 fc
    subst l'
    have measure := (family.at_l hZF.1 hcU fc ds).base
    obtain ⟨P', hPU, point⟩ := (quotient.relation f'' g'' P Q₁
      (quotient.map.member_l I hZF.1 measure hPC hfP') (quotient.map.member_l I hZF.1 measure hQC hgQ')).mp relation
    have sk := (owner.finite s).mpr ⟨m, hm, fn0_function_l (ZF.modelsKP hZF)
      (fs.mono_target_l fun x hx => owner.below x (owner.omega.transitive hZF l hl x hx))⟩
    have tk := (owner.finite t).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF)
      (ft.mono_target_l fun x hx => owner.below x (owner.omega.transitive hZF l hl x hx))⟩
    refine ⟨c, (system.projection.bound_l hwc).2, U, measures c U hcU, hcU, P', hPU,
      m, hm, n, hn, l, hl, s, sk, t, tk, fs, ft, fc, fsa, ftb, fun v hv => ?_⟩
    have vf := (ds v).mp (measure.bounds P' hPU v hv)
    obtain ⟨s₀, sv⟩ := cp0_exists_l (ZF.modelsKP hZF) fs vf
    obtain ⟨t₀, tv⟩ := cp0_exists_l (ZF.modelsKP hZF) ft vf
    obtain ⟨x, hx, sx⟩ := ff.2.1 s₀ ((space s₀).mpr sv.1)
    obtain ⟨y, hy, ty⟩ := gg.2.1 t₀ ((space' t₀).mpr tv.1)
    obtain ⟨x', _, y', _, vx, vy, xy⟩ := point v hv
    have hxx := (cf.value_l (ff.mono_target_l sub) key sx).mp ((pf.2.2 v s₀ vf sv x').mp vx)
    have hyy := (cg.value_l (gg.mono_target_l sub) key ty).mp ((pg.2.2 v t₀ vf tv y').mp vy)
    exact ⟨s₀, (owner.finite s₀).mpr ⟨m, hm, fn0_function_l (ZF.modelsKP hZF) sv.1⟩,
      t₀, (owner.finite t₀).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) tv.1⟩,
      x, hx, y, hy, sv, tv, sx, ty, (member x y x' y' hx hy hxx hyy).mpr xy⟩

end YesMetaZFC.SetTheory.LargeCardinal
