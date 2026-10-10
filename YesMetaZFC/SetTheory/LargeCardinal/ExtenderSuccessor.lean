import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSetTransfer

/-! # 同一扩展器的两次施加保持支撑以下的子集一致性

每个后继子集先取实际代表，把界序数加入支撑，再正规化为有限 κ 幂的
集合值代表。编码与坐标计算把该集合送入另一后继；交换两源即得一致性。
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
    (hκ : M.TransitiveSet κ) (hL : M.TransitiveSet L) (hωL : M.MemberSubset ω L)
    (hm : M.mem m ω) (hμ : M.mem μ L) (hB : M.mem B N) (bound : ∀ t, M.mem t B → Fn0_d m μ t) : M.mem B N' := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨H, hHB⟩ := (range B).mp hB
  obtain ⟨n, a, D, f, hn, haJ, ha, hD, hfX, hf, fh⟩ :=
    ep_repr_surjective_l hZF family h limit (he.1.1.input_mem_of_pairMember hHB)
  obtain ⟨Hμ, _, nμ, aμ, iμ, Dμ, uμ, haμ, hiμ, hDμ, huμ, uhμ⟩ := ep_seed_exists_l hZF source family h limit hμ
  obtain ⟨a₁, _, haa₁, hμa₁⟩ := h.order.directed a aμ haJ (uhμ.index_l hZF h limit)
  obtain ⟨l, D₁, i, u, hl, ha₁, hi, hD₁, huX, hu, uh⟩ :=
    ep_seed_move_l hZF source family h limit haμ hiμ hDμ huμ uhμ hμa₁
  obtain ⟨_, ha₁J, r, n', l', _, _, hr, ha₁', hra⟩ := (h.order_spec a a₁).mp haa₁
  have en := hra.1.domain_eq_l hZF.1 ha
  have el := ha₁'.domain_eq_l hZF.1 ha₁
  subst n' l'
  obtain ⟨g, hgX, hg, _, gh⟩ := ep_repr_reindex_l hZF source family h limit hn hl hr ha₁J ha₁ hra hD hD₁ hfX hf fh
  obtain ⟨E, _, hE⟩ := source.space_l hZF hm
  obtain ⟨g', hgX', hg', gb', gv'⟩ := ep_value_bound_l hZFC source family coherent h limit model hN target he
    hκ ha₁J hl hm ha₁ hD₁ hE hgX hg ⟨H, gh, hHB⟩ hu
    ⟨Hμ, uh, fixed μ Hμ ⟨l, a₁, i, D₁, u, ha₁, hi, hD₁, hu, uh⟩⟩ bound
  exact ep_set_transfer_l hZFC source source' agree family coherent h limit model hN target he fixed
    h' limit' model' hN' target' he' fixed' hL hωL ha₁J hl hm ha₁ hD₁ hE hgX' hg' gb' gv' huX hu hi bound

/-- 任意实际传递坍塌均在每个 μ∈L 的全部内部有限幂子集上一致。 -/
theorem ep_successor_agree_l (hZFC : M.Models ZFC)
    {ω κ K K' L X R Y R' F J O Z A p T V q c C W d N S e
      J' O' Z' A' p' T' V' q' c' C' W' d' N' S' e' : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (source' : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K' Y R')
    (agree : Ea_agree_d ω κ X Y) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (atoms : Ea_atoms_d ω κ L F) (normal : En_source_d ω κ L X F)
    (hκ : M.TransitiveSet κ) (hL : M.TransitiveSet L) (hωL : M.MemberSubset ω L)
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
    ∀ μ, M.mem μ L → Ea_agree_d ω μ N N' := by
  let hZF := ZFC.models_zf_l hZFC
  have family' := family.transfer_l agree
  have coherent' := coherent.transfer_l hZF agree
  have normal' := normal.transfer_l hZF source source' agree
  have fixed := (ep_seed_collapse_l hZF source hκ hL hωL family coherent atoms normal h limit wc
    (fn0_of_function_l (ZF.modelsKP hZF) he.1.1)).2
  have fixed' := (ep_seed_collapse_l hZF source' hκ hL hωL family' coherent' atoms normal' h' limit' wc'
    (fn0_of_function_l (ZF.modelsKP hZF) he'.1.1)).2
  intro μ hμ m E B hm hE sub
  have bound t ht := (hE t).mp (sub t ht)
  exact ⟨fun hB => ep_successor_mem_l hZFC source source' agree family coherent h limit model hN target he range fixed
      h' limit' model' hN' target' he' fixed' hκ hL hωL hm hμ hB bound,
    fun hB => ep_successor_mem_l hZFC source' source (fun n D B hn hd hb => (agree n D B hn hd hb).symm)
      family' coherent' h' limit' model' hN' target' he' range' fixed' h limit model hN target he fixed hκ hL hωL hm hμ hB bound⟩

end YesMetaZFC.SetTheory.LargeCardinal
