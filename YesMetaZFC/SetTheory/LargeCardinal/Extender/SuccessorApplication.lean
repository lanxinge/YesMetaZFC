import YesMetaZFC.SetTheory.LargeCardinal.Extender.ValueBound
import YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraSupport
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Limit

/-! # 有界集合代表在固定支撑上的迹一致

先搬运处处有界的代表，再把任意有限列加入共同支撑。其投影在两侧均
坍塌为原列，同一测度判定相同的成员关系。这里直接覆盖完整 L，而不把 L
当作支撑中的一个坐标；后续在目标的有限 L 幂中分离实际的迹。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_set_trace_l (hZFC : M.Models ZFC)
    {ω κ K K' L X R Y R' F J O Z A p T V q c C W d N S e
      J' O' Z' A' p' T' V' q' c' C' W' d' N' S' e' n m D E a f B : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R)
    (source' : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K' Y R')
    (agree : Ea_agree_d ω κ X Y) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (hN : M.TransitiveSet N) (target : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (fixed : ∀ α H, Ep_seed_d κ L q α H → Rd_entry_d H α e)
    (h' : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L Y R' F J' O' Z' A' p' T' V')
    (limit' : Di_limit_d A' p' T' V' q' C' W')
    (model' : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c' C' W')
    (hN' : M.TransitiveSet N') (target' : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d' N' S')
    (he' : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c' d' C' N' e')
    (fixed' : ∀ α H, Ep_seed_d κ L q' α H → Rd_entry_d H α e')
    (haJ : M.mem a J) (hn : M.mem n ω) (hm : M.mem m ω) (ha : Fn0_d n L a)
    (hD : Ep_space_d κ n D) (hE : Ep_space_d κ m E)
    (hfX : M.mem f X) (hf : Fn0_d D X f) (fb : ∀ s x, Rd_entry_d s x f → M.MemberSubset x E)
    (fv : Ep_value_d q e a f B) : ∃ B', M.mem B' N' ∧
      ∀ t, Fn0_d m L t → (M.mem t B ↔ M.mem t B') := by
  let hZF := ZFC.models_zf_l hZFC
  have family' := family.transfer_l agree
  have coherent' := coherent.transfer_l hZF agree
  have haJ' := (h'.indices a).mpr ((h.indices a).mp haJ)
  have hfY := agree.subset_l.set_function_l hZF source source' hn hm hD hE hfX hf fb
  have hf' := hf.retarget_l (fun s x hx => (rd_entry_transitive_l source'.transitive hfY hx).2)
  obtain ⟨H', hHC', fh'⟩ := ep_repr_exists_l hZF family' h' limit' haJ' ha hD hfY hf'
  obtain ⟨B', hBN', hHB'⟩ := he'.1.1.2.2 H' hHC'
  -- 把待测有限列并入支撑；同一投影在两侧都代表该列自身。
  refine ⟨B', hBN', fun t ht => ?_⟩
  obtain ⟨l, a₁, r, s, hl, ha₁, hr, hra, hs, hst⟩ := ec_join_l hZF source.omega hn hm ha ht
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

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一扩展器的两次施加保持支撑以下的子集一致性

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
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R)
    (source' : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K' Y R')
    (agree : Ea_agree_d ω κ X Y) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (hN : M.TransitiveSet N) (target : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (range : M.IsRangeOf (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) N e)
    (fixed : ∀ α H, Ep_seed_d κ L q α H → Rd_entry_d H α e)
    (h' : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L Y R' F J' O' Z' A' p' T' V')
    (limit' : Di_limit_d A' p' T' V' q' C' W')
    (model' : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c' C' W')
    (hN' : M.TransitiveSet N') (target' : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d' N' S')
    (he' : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c' d' C' N' e')
    (fixed' : ∀ α H, Ep_seed_d κ L q' α H → Rd_entry_d H α e')
     (hm : M.mem m ω) (hμL : M.MemberSubset μ L) (hμN' : M.mem μ N')
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
    h' limit' model' hN' target' he' fixed' haJ hn hm ha hD hE hgX hg gb gv
  -- 目标的有限 μ 列空间是实际内部集合；在其中取迹，允许 μ=L。
  have haJ' := (h'.indices a).mpr ((h.indices a).mp haJ)
  obtain ⟨b', j', code', hj', _⟩ := ep_value_constants_l hZFC source' (family.transfer_l agree)
    (coherent.transfer_l hZF agree) h' limit' model' he' haJ' ha hD
  have image := hj'.omega_l I hZF source.omega source'.transitive hN' code' target' source'.omega_mem
  have hωN' := hj'.1.1.output_mem_of_pairMember image
  have theory := source'.theory.map_l I hZF source.omega code'.1 target'.1 hj'
  have seq := (sc_sequences_iff_l I hZF source.omega code'.1 target'.1 hj' image).mp source'.sequences
  have a := theory.algebra_l I (ZF.modelsKP hZF) hN' target'
  obtain ⟨Q, hQN', hQ⟩ := ((sc_sequences_mem_l I (ZF.modelsKP hZF) source.omega hN' target' hωN' a.pair a.union).mp seq).1 μ hμN'
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
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R)
    (source' : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K' Y R')
    (agree : Ea_agree_d ω κ X Y) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (atoms : Ea_atoms_d ω κ L F) (normal : En_source_d ω κ L X F)
    (hκ : M.IsOrdinal κ) (hL : M.IsOrdinal L)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (hN : M.TransitiveSet N) (target : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (range : M.IsRangeOf (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) N e) (wc : Wc_graph_d C W e)
    (h' : Ep_system_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L Y R' F J' O' Z' A' p' T' V')
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
  obtain ⟨_, fixed⟩ := ep_seed_collapse_l hZF source hκ.transitive hL.transitive family coherent atoms normal h limit wc
    (fn0_of_function_l (ZF.modelsKP hZF) he.1.1)
  obtain ⟨_, fixed'⟩ := ep_seed_collapse_l hZF source' hκ.transitive hL.transitive family' coherent' atoms normal' h' limit' wc'
    (fn0_of_function_l (ZF.modelsKP hZF) he'.1.1)
  have hLN := ep_support_mem_l hZFC source family coherent h limit model hN target he fixed hκ hL
  have hLN' := ep_support_mem_l hZFC source' family' coherent' h' limit' model' hN' target' he' fixed' hκ hL
  refine ⟨hLN, hLN', fun m E B hm hE sub => ?_⟩
  have bound t ht := (hE t).mp (sub t ht)
  exact ⟨fun hB => ep_successor_mem_l hZFC source source' agree family coherent h limit model hN target he range fixed
      h' limit' model' hN' target' he' fixed' hm (fun _ hx => hx) hLN' hB bound,
    fun hB => ep_successor_mem_l hZFC source' source (fun n D B hn hd hb => (agree n D B hn hd hb).symm)
      family' coherent' h' limit' model' hN' target' he' range' fixed' h limit model hN target he fixed hm (fun _ hx => hx) hLN hB bound⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 后继一致性的自动构造入口

后继证书保留实际源超幂、整个定向极限和传递坍塌，明确把输出模型与
输入扩展器联系起来。短扩展器入口实际生成两侧模型及下一次施加的源证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_successor_d (hZF : M.Models ZF) (ω κ L X R F N S : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ J O Z A p T V q c C W d e,
    Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T V ∧ Di_limit_d A p T V q C W ∧
    Smdl_d I c C W ∧ Smem_d I d N S ∧ M.TransitiveSet N ∧
    Wc_graph_d C W e ∧ M.IsSetBijectionFromTo I e C N ∧ Smap_d I ω c d C N e

theorem Ex_short_d.successors_l (hZFC : M.Models ZFC) {ω κ L F K K' X R Y R' : M.Domain}
    (ex : Ex_short_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L F)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R)
    (source' : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K' Y R') (agree : Ea_agree_d ω κ X Y) :
    ∃ N S N' S', Ep_successor_d (ZFC.models_zf_l hZFC) ω κ L X R F N S ∧
      Ep_successor_d (ZFC.models_zf_l hZFC) ω κ L Y R' F N' S' ∧
      M.mem L N ∧ M.mem L N' ∧ Ea_agree_d ω L N N' ∧
      ∀ μ, (M.mem μ L ∨ μ = L) → M.MemberSubset ω μ → ∃ K K',
        Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω μ K N S ∧ Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω μ K' N' S' := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hκ := ex.critical.1.transitive
  have hL := ex.length.transitive
  have hωL : M.MemberSubset ω L := fun x hx => hL κ ex.above x (hκ ω ex.uncountable x hx)
  have family := ex.measures.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) X
  have coherent := ex.coherent.source_l I X
  obtain ⟨J, O, Z, A, p, T, V, q, c, C, W, h, limit, model, _, _, collapse⟩ := ex.limit_l hZFC source
  obtain ⟨J', O', Z', A', p', T', V', q', c', C', W', h', limit', model', _, _, collapse'⟩ := ex.limit_l hZFC source'
  obtain ⟨_, _, _, N, e, _, d, S, _, _, _, _, hN, wc, bij, code, he, _, _, _, _, _, next⟩ := collapse
  obtain ⟨_, _, _, N', e', _, d', S', _, _, _, _, hN', wc', bij', code', he', _, _, _, _, _, next'⟩ := collapse'
  have range : M.IsRangeOf I N e := fun x => ⟨fun hx => (bij.2 x hx).imp fun E hE => hE.2,
    fun ⟨_, hx⟩ => bij.1.1.output_mem_of_pairMember hx⟩
  have range' : M.IsRangeOf I N' e' := fun x => ⟨fun hx => (bij'.2 x hx).imp fun E hE => hE.2,
    fun ⟨_, hx⟩ => bij'.1.1.output_mem_of_pairMember hx⟩
  obtain ⟨hLN, hLN', common⟩ := ep_successor_agree_l hZFC source source' agree family coherent ex.atoms (ex.normal.source_l X)
    ex.critical.1 ex.length h limit model hN code he range wc h' limit' model' hN' code' he' range' wc'
  refine ⟨N, S, N', S', ⟨J, O, Z, A, p, T, V, q, c, C, W, d, e, h, limit, model, code, hN, wc, bij, he⟩,
    ⟨J', O', Z', A', p', T', V', q', c', C', W', d', e', h', limit', model', code', hN', wc', bij', he'⟩,
    hLN, hLN', common, ?_⟩
  intro μ hμ hωμ
  obtain ⟨K₀, ready⟩ := next
  obtain ⟨K₁, ready'⟩ := next'
  have ho := hμ.elim ex.length.mem (fun eq => eq.symm ▸ ex.length)
  have hm := hμ.elim (hN L hLN μ) (fun eq => eq.symm ▸ hLN)
  have hm' := hμ.elim (hN' L hLN' μ) (fun eq => eq.symm ▸ hLN')
  obtain ⟨K, hk⟩ := ready.rebase_l hm hωμ (sc_ordinal_small_l hZF ready.omega hN code ready.theory hm ho)
  obtain ⟨K', hk'⟩ := ready'.rebase_l hm' hωμ (sc_ordinal_small_l hZF ready'.omega hN' code' ready'.theory hm' ho)
  exact ⟨K, K', hk, hk'⟩

end YesMetaZFC.SetTheory.LargeCardinal
