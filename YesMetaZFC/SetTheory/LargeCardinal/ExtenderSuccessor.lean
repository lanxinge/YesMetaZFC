import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSetTransfer
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSupportBound

/-! # 同一扩展器的两次施加保持支撑以下的子集一致性

每个后继子集先取实际代表，以常值 κ 的像统一界住整个支撑，再正规化。
目标内的有限列空间分离出原集合的迹，因而同一证明也适用于支撑端点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 先证一个方向：原后继中的有界有限列集合属于另一后继。 -/
theorem ep_successor_mem_l (hZFC : M.Models ZFC)
    {ω κ K K' L X R Y R' F J O Z A p T V q c C W d N S e
      J' O' Z' A' p' T' V' q' c' C' W' d' N' S' e' m μ B : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (source' : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K' Y R')
    (agree : Ea_agree_d ω κ X Y) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (hN : M.TransitiveSet N) (target : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (range : M.IsRangeOf (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) N e)
    (fixed : ∀ α H, Ep_seed_d κ L q α H → Rd_entry_d H α e)
    (h' : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L Y R' F J' O' Z' A' p' T' V')
    (limit' : Di_limit_d A' p' T' V' q' C' W')
    (model' : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c' C' W')
    (hN' : M.TransitiveSet N') (target' : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d' N' S')
    (he' : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c' d' C' N' e')
    (fixed' : ∀ α H, Ep_seed_d κ L q' α H → Rd_entry_d H α e')
    (hωL : M.MemberSubset ω L) (hm : M.mem m ω) (hμL : M.MemberSubset μ L) (hμN' : M.mem μ N')
    (hB : M.mem B N) (bound : ∀ t, M.mem t B → Fn0_d m μ t) : M.mem B N' := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨H, hHB⟩ := (range B).mp hB
  obtain ⟨n, a, D, f, hn, haJ, ha, hD, hfX, hf, fh⟩ :=
    ep_repr_surjective_l hZF family h limit (he.1.1.input_mem_of_pairMember hHB)
  obtain ⟨b, j, code, hj, constants⟩ := ep_value_constants_l hZFC source family coherent h limit model he haJ ha hD
  obtain ⟨ν, _, hκν⟩ := hj.1.1.2.2 κ source.cardinal_mem
  obtain ⟨u, huX, hu, uc, uv⟩ := constants κ ν hκν
  have cover := ep_value_support_l hZF source family h limit model target he fixed haJ hn ha hD huX hu uc uv
  obtain ⟨E, _, hE⟩ := source.space_l hZF hm
  obtain ⟨g, hgX, hg, gb, gv⟩ := ep_value_bound_l hZFC source family coherent h limit model hN target he
    haJ hn hm ha hD hE hfX hf ⟨H, fh, hHB⟩ hu
    (fun s x hsx => by
      have eq := (fn0_function_l (ZF.modelsKP hZF) hu).1.2 s x κ hsx (uc s (hu.bound_l hsx).1)
      exact eq ▸ (fun _ hx => hx)) uv (fun t ht => (bound t ht).mono_target_l (fun α hα => cover α (hμL α hα)))
  obtain ⟨B', hBN', trace⟩ := ep_set_trace_l hZFC source source' agree family coherent h limit model hN target he fixed
    h' limit' model' hN' target' he' fixed' hωL haJ hn hm ha hD hE hgX hg gb gv
  -- 目标的有限 μ 列空间是实际内部集合；在其中取迹，允许 μ=L。
  have haJ' := (h'.indices a).mpr ((h.indices a).mp haJ)
  obtain ⟨b', j', code', hj', _⟩ := ep_value_constants_l hZFC source' (family.transfer_l agree)
    (coherent.transfer_l hZF agree) h' limit' model' he' haJ' ha hD
  have hωN' := hj'.1.1.output_mem_of_pairMember (hj'.omega_l I hZF source.omega source'.transitive hN'
    code' target' source'.omega_mem)
  have theory := source'.theory.map_l I hZF source.omega source'.transitive hN' code' target' hj'
  have seq := (sc_sequences_iff_l hZF source.omega source'.transitive hN' code' target' hj' source'.omega_mem source'.theory theory).mp source'.sequences
  obtain ⟨Q, hQN', hQ⟩ := seq.space μ hμN'
  let ρ : Env M 3 := ⟨Fin.cases m (Fin.cases μ (fun _ => B')), fun _ => m⟩
  let φ : UnarySchema 3 := { body := .conj (fn0_m (.bound 1) (.bound 2) .newest) (.mem .newest (.bound 3)) }
  have sat t : φ.denote ρ t ↔ Fn0_d m μ t ∧ M.mem t B' := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_conj_iff, fn0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  obtain ⟨B₀, hB₀, spec⟩ := sc_separate_source_l I hZF source.omega hN' target' theory φ
    (.conj (fn0_delta_l ..) (.mem _ _)) ρ (Fin.cases (hN' ω hωN' m hm) (Fin.cases hμN' (fun _ => hBN'))) hQN'
  have eq : B₀ = B := hZF.1.eq_of_same_members B₀ B (fun t => by
    rw [spec t, sat t]
    exact ⟨fun ⟨_, ht, htB⟩ => (trace t (ht.mono_target_l hμL)).mpr htB,
      fun ht => ⟨(hQ t).mpr ⟨m, hm, fn0_function_l (ZF.modelsKP hZF) (bound t ht)⟩,
        bound t ht, (trace t ((bound t ht).mono_target_l hμL)).mp ht⟩⟩)
  exact eq ▸ hB₀

/-- 序数支撑的端点属于两侧后继，两者在全部有限 L 幂子集上一致。 -/
theorem ep_successor_agree_l (hZFC : M.Models ZFC)
    {ω κ K K' L X R Y R' F J O Z A p T V q c C W d N S e
      J' O' Z' A' p' T' V' q' c' C' W' d' N' S' e' : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (source' : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K' Y R')
    (agree : Ea_agree_d ω κ X Y) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (atoms : Ea_atoms_d ω κ L F) (normal : En_source_d ω κ L X F)
    (hκ : M.IsOrdinal κ) (hL : M.IsOrdinal L) (hωL : M.MemberSubset ω L)
    (h : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (hN : M.TransitiveSet N) (target : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (range : M.IsRangeOf (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) N e) (wc : Wc_graph_d C W e)
    (h' : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L Y R' F J' O' Z' A' p' T' V')
    (limit' : Di_limit_d A' p' T' V' q' C' W')
    (model' : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c' C' W')
    (hN' : M.TransitiveSet N') (target' : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d' N' S')
    (he' : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c' d' C' N' e')
    (range' : M.IsRangeOf (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) N' e') (wc' : Wc_graph_d C' W' e') :
    M.mem L N ∧ M.mem L N' ∧ Ea_agree_d ω L N N' := by
  let hZF := ZFC.models_zf_l hZFC
  have family' := family.transfer_l agree
  have coherent' := coherent.transfer_l hZF agree
  have normal' := normal.transfer_l hZF source source' (fun n D B hn hd sub => (agree n D B hn hd sub).mpr)
  obtain ⟨_, fixed⟩ := ep_seed_collapse_l hZF source hκ.transitive hL.transitive hωL family coherent atoms normal h limit wc
    (fn0_of_function_l (ZF.modelsKP hZF) he.1.1)
  obtain ⟨_, fixed'⟩ := ep_seed_collapse_l hZF source' hκ.transitive hL.transitive hωL family' coherent' atoms normal' h' limit' wc'
    (fn0_of_function_l (ZF.modelsKP hZF) he'.1.1)
  have hLN := ep_support_mem_l hZFC source family coherent h limit model hN target he fixed hκ hL
  have hLN' := ep_support_mem_l hZFC source' family' coherent' h' limit' model' hN' target' he' fixed' hκ hL
  refine ⟨hLN, hLN', fun m E B hm hE sub => ?_⟩
  have bound t ht := (hE t).mp (sub t ht)
  exact ⟨fun hB => ep_successor_mem_l hZFC source source' agree family coherent h limit model hN target he range fixed
      h' limit' model' hN' target' he' fixed' hωL hm (fun _ hx => hx) hLN' hB bound,
    fun hB => ep_successor_mem_l hZFC source' source (fun n D B hn hd hb => (agree n D B hn hd hb).symm)
      family' coherent' h' limit' model' hN' target' he' range' fixed' h limit model hN target he fixed hωL hm (fun _ hx => hx) hLN hB bound⟩

end YesMetaZFC.SetTheory.LargeCardinal
