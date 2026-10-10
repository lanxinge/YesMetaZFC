import YesMetaZFC.SetTheory.LargeCardinal.ExtenderValueBound

/-! # 有界集合代表在两次施加后给出同一个集合

先搬运代表和界公式，再把任意有限列加入共同支撑。其投影在两侧均
坍塌为原列，同一测度判定相同的成员关系，最后用外延性识别集合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_set_transfer_l (hZFC : M.Models ZFC)
    {ω κ K K' L X R Y R' F J O Z A p T V q c C W d N S e
      J' O' Z' A' p' T' V' q' c' C' W' d' N' S' e' n m D E a f u i μ B : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (source' : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K' Y R')
    (agree : Ea_agree_d ω κ X Y) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (hN : M.TransitiveSet N) (target : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (fixed : ∀ α H, Ep_seed_d κ L q α H → Rd_entry_d H α e)
    (h' : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L Y R' F J' O' Z' A' p' T' V')
    (limit' : Di_limit_d A' p' T' V' q' C' W')
    (model' : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c' C' W')
    (hN' : M.TransitiveSet N') (target' : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d' N' S')
    (he' : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c' d' C' N' e')
    (fixed' : ∀ α H, Ep_seed_d κ L q' α H → Rd_entry_d H α e')
    (hL : M.TransitiveSet L) (hωL : M.MemberSubset ω L)
    (haJ : M.mem a J) (hn : M.mem n ω) (hm : M.mem m ω) (ha : Fn0_d n L a)
    (hD : Ep_space_d κ n D) (hE : Ep_space_d κ m E)
    (hfX : M.mem f X) (hf : Fn0_d D X f) (fb : ∀ s x, Rd_entry_d s x f → M.MemberSubset x E)
    (fv : Ep_value_d q e a f B) (huX : M.mem u X) (hu : Ep_coord_d κ D i u) (hiμ : Rd_entry_d i μ a)
    (bound : ∀ t, M.mem t B → Fn0_d m μ t) : M.mem B N' := by
  let hZF := ZFC.models_zf_l hZFC
  have family' := family.transfer_l agree
  have coherent' := coherent.transfer_l hZF agree
  have haJ' := (h'.indices a).mpr ((h.indices a).mp haJ)
  have hfY := agree.set_function_l hZF source source' hn hm hD hE hfX hf fb
  have hf' := hf.retarget_l (fun s x hx => (rd_entry_transitive_l source'.transitive hfY hx).2)
  obtain ⟨H', hHC', fh'⟩ := ep_repr_exists_l hZF family' h' limit' haJ' ha hD hfY hf'
  obtain ⟨B', hBN', hHB'⟩ := he'.1.1.2.2 H' hHC'
  have fv' : Ep_value_d q' e' a f B' := ⟨H', fh', hHB'⟩
  obtain ⟨U, haU⟩ := family.total n a hn ha
  have huY := agree.function_l hZF source source' hn hD huX hu.1
  obtain ⟨H, _, uh⟩ := ep_repr_exists_l hZF family h limit haJ ha hD huX
    (hu.1.mono_target_l (source.transitive κ source.cardinal_mem))
  obtain ⟨H₁, _, uh'⟩ := ep_repr_exists_l hZF family' h' limit' haJ' ha hD huY
    (hu.1.mono_target_l (source'.transitive κ source'.cardinal_mem))
  have uv : Ep_value_d q e a u μ := ⟨H, uh, fixed μ H ⟨n, a, i, D, u, ha, hiμ, hD, hu, uh⟩⟩
  have uv' : Ep_value_d q' e' a u μ := ⟨H₁, uh', fixed' μ H₁ ⟨n, a, i, D, u, ha, hiμ, hD, hu, uh'⟩⟩
  obtain ⟨b, code⟩ := source.code
  obtain ⟨v, _, _, _, hv, vs⟩ := sc_constant_l hZF source.omega source.transitive code source.theory
    (source.space_mem_l hZF hn hD) (source.transitive ω source.omega_mem m hm)
  have hvκ := hv.retarget_l (fun s x hsx => ((vs s x).mp hsx).2.symm ▸ source.below m hm)
  have vc : Rs_const_d D m v := fun s hs => (vs s m).mpr ⟨hs, rfl⟩
  have vv := ep_value_natural_l hZFC source family coherent h limit model hN target he haJ ha hD hm
    (hvκ.mono_target_l (source.transitive κ source.cardinal_mem)) vc
  have vv' := ep_value_natural_l hZFC source' family' coherent' h' limit' model' hN' target' he' haJ' ha hD hm
    (hvκ.mono_target_l (source'.transitive κ source'.cardinal_mem)) vc
  have bounds := ep_value_agree_l hZFC source source' agree family coherent h limit model hN target he
    h' limit' model' hN' target' he' haJ haJ' hn ha hD haU (k := 3)
    (ep_subspace_m (.bound 2) (.bound 1) (.bound 0)) (by simp -implicitDefEqProofs) (ep_subspace_delta_l ..)
    (Fin.cases f (Fin.cases u (fun _ => v)))
    ⟨Fin.cases B (Fin.cases μ (fun _ => m)), fun _ => m⟩ ⟨Fin.cases B' (Fin.cases μ (fun _ => m)), fun _ => m⟩
    (Fin.cases fv (Fin.cases uv (fun _ => vv))) (Fin.cases fv' (Fin.cases uv' (fun _ => vv')))
  have bound' := (ep_subspace_sat_l hZF.1 ..).mp (bounds.mp ((ep_subspace_sat_l hZF.1 ..).mpr bound))
  -- 把待测有限列并入支撑；同一投影在两侧都代表该列自身。
  have members t (ht : Fn0_d m μ t) : M.mem t B ↔ M.mem t B' := by
    obtain ⟨l, a₁, r, s, hl, ha₁, hr, hra, hs, hst⟩ := ec_join_l hZF source.omega hωL hn hm ha
      (ht.mono_target_l (hL μ (ha.bound_l hiμ).2))
    have ha₁f := fn0_of_function_l (ZF.modelsKP hZF) ha₁.1
    have ha₁J := (h.indices a₁).mpr ⟨l, hl, ha₁f, ha₁.2⟩
    have ha₁J' := (h'.indices a₁).mpr ⟨l, hl, ha₁f, ha₁.2⟩
    obtain ⟨D₁, _, hD₁⟩ := source.space_l hZF hl
    obtain ⟨H, fh, hHB⟩ := fv
    obtain ⟨g, hgX, hg, pull, gh⟩ := ep_repr_reindex_l hZF source family h limit hn hl hr ha₁J ha₁f hra hD hD₁ hfX hf fh
    obtain ⟨g', hgY, hg', pull', gh'⟩ := ep_repr_reindex_l hZF source' family' h' limit' hn hl hr ha₁J' ha₁f hra hD hD₁ hfY hf' fh'
    have eg := ep_pull_unique_l (ZF.modelsKP hZF) hr pull' pull
    subst g'
    obtain ⟨k, hkX, hk, ks⟩ := source.projection_l hZF hm hl hs hE hD₁
    obtain ⟨k', hkY, hk', ks'⟩ := source'.projection_l hZF hm hl hs hE hD₁
    have ek : k' = k := hk'.ext_l hZF.1 hk fun x hx => by
      obtain ⟨y, _, hxy⟩ := hk'.2.1 x hx
      exact ⟨y, hxy, (ks x y).mpr ((ks' x y).mp hxy)⟩
    subst k'
    have kv := ep_tuple_value_l hZFC source family coherent h limit model hN target he fixed ha₁J hl hm ha₁f hs hst
      hD₁ hE hkX hk (fun x y hxy => ((ks x y).mp hxy).2)
    have kv' := ep_tuple_value_l hZFC source' family' coherent' h' limit' model' hN' target' he' fixed' ha₁J' hl hm ha₁f hs hst
      hD₁ hE hkY hk (fun x y hxy => ((ks x y).mp hxy).2)
    obtain ⟨U₁, ha₁U⟩ := family.total l a₁ hl ha₁f
    simpa only [Formula.satisfies_mem_iff] using! ep_value_agree_l hZFC source source' agree family coherent h limit model hN target he
      h' limit' model' hN' target' he' ha₁J ha₁J' hl ha₁f hD₁ ha₁U (k := 2)
      (.mem (.bound 0) (.bound 1)) (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]) (.mem _ _)
      (Fin.cases k (fun _ => g)) ⟨Fin.cases t (fun _ => B), fun _ => B⟩ ⟨Fin.cases t (fun _ => B'), fun _ => B'⟩
      (Fin.cases kv (fun _ => ⟨H, gh, hHB⟩)) (Fin.cases kv' (fun _ => ⟨H', gh', hHB'⟩))
  have equal := hZF.1.eq_of_same_members B' B fun t =>
    ⟨fun ht => (members t (bound' t ht)).mpr ht, fun ht => (members t (bound t ht)).mp ht⟩
  exact equal ▸ hBN'

end YesMetaZFC.SetTheory.LargeCardinal
