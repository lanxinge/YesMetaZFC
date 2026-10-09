import YesMetaZFC.SetTheory.LargeCardinal.WoodinTrace
import YesMetaZFC.Model.SetTheory.Internal.TypeRank
import YesMetaZFC.Model.SetTheory.Internal.TypeSource
import YesMetaZFC.Model.SetTheory.Internal.TypeEmbedding
import YesMetaZFC.Model.SetTheory.Internal.TypeGuard

/-! # 强扩展器中的完整类型像

全局谓词是实际完整查询的真值集合。低秩一致性把像类型中的所有新查询
还原为同一个实现元组的真值；标记由查询域不含序数自动排除。
所有像与同一扩展器的实际超幂绑定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 源内任意查询域的类型，经指定强扩展器后在强度以下仍读取原实现的真值。 -/
theorem Ep_strong_limit_d.type_image_l (hZF : M.Models ZF)
    {ω θ κ L X R A C V F j Y α c n s δ U D : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) θ X)
    (hα : M.IsOrdinal α) (hVX : M.MemberSubset V X)
    (truth : Tt_truth_d (kp_pair_l (ZF.modelsKP hZF)) ω c n s δ X A)
    (marker : ∀ p, M.mem p C ↔ M.mem p A ∨ p = α)
    (pool : Tt_pool_d (kp_pair_l (ZF.modelsKP hZF)) ω n U D) (hD : M.mem D X)
    (h : Ep_strong_limit_d hZF ω κ L X R C V F j Y) :
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ b d N S i κ' D' t t', Smem_d I b X R ∧ Smem_d I d N S ∧ It_ultra_d hZF ω κ L F b d i ∧
      Wd_crit_d I X i κ κ' ∧ M.MemberSubset L κ' ∧ M.MemberSubset V N ∧
      Rd_entry_d D D' i ∧ Rd_entry_d t t' i ∧ Tt_truth_d I ω c n s δ D t ∧
        ∀ p, M.mem p V → (M.mem p t' ↔ M.mem p D' ∧ Tt_query_d I ω c n s δ p) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨J, O, Z, H, π, T, Q, q, a, K, W, system, limit, code, _, _, _, _, strength, _⟩ := h
  obtain ⟨b, d, N, S, B, i, k, κ', hm, hn, hN, hi, embed, crit, bound, cover, _, _, _, _, _, _, _, agree, realizer, _⟩ := strength
  obtain ⟨u, e, hu, constants, collapse, bij, he, comp⟩ := realizer
  have ultra : It_ultra_d hZF ω κ L F b d i :=
    ⟨X, R, N, S, J, O, Z, H, π, T, Q, q, a, K, W, u, e, hm, hn, system, limit, code,
      collapse, bij, he, hu, constants, hi, hi.1.1.1.1, fun x y => (comp x y).trans
        ⟨And.right, fun ⟨E, hxE, hEy⟩ => ⟨hu.1.1.input_mem_of_pairMember hxE, E, hxE, hEy⟩⟩⟩
  have transitive := ZF.v_transitive_l I hZF hX
  have no_ordinal p (hp : M.mem p D) : ¬ M.IsOrdinal p := by
    obtain ⟨_, _, _, _, prod⟩ := pool
    obtain ⟨z, _, e, _, pair⟩ := (prod p).mp hp
    exact fun ho => pair.not_transitive_l M (KP.mem_irrefl_d (ZF.modelsKP hZF)) ho.transitive
  obtain ⟨t, type, _⟩ := tt_truth_exists_l I hZF ω c n s δ D
  have ht := ZF.v_subset_mem_l I hZF hX hD (fun p hp => ((type p).mp hp).1)
  obtain ⟨D', _, hDD⟩ := hi.1.1.2.2 D hD
  obtain ⟨t', _, htt⟩ := hi.1.1.2.2 t ht
  have project := type.project_l I truth (transitive D hD)
  have source p : M.mem p t ↔ M.mem p D ∧ M.mem p C := (project p).trans (and_congr_right fun hp =>
    ⟨fun ha => (marker p).mpr (Or.inl ha), fun hC => by
      rcases (marker p).mp hC with ha | rfl
      · exact ha
      · exact (no_ordinal p hp hα).elim⟩)
  have image := spred_trace_l I hZF hω embed hN hDD htt source
  have tr := spred_delta_l I hZF hω embed transitive hN (n := 1)
    (Formula.forallMem (.bound 0) (.neg (KP.ord0_m .newest)))
    (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]) (.forallMem _ (.neg (KP.ord0_delta_l _)))
    ⟨fun _ => D, fun _ => D⟩ ⟨fun _ => D', fun _ => D'⟩ (fun _ => hDD)
  simp only [Formula.satisfies_forallMem_iff, Formula.satisfies_neg_iff, KP.ord0_sat_l (ZF.modelsKP hZF)] at tr
  have no_ordinal' : ∀ p, M.mem p D' → ¬ M.IsOrdinal p := tr.mp no_ordinal
  refine ⟨b, d, N, S, i, κ', D', t, t', hm, hn, ultra, crit, bound, cover, hDD, htt, type, fun p hp => ?_⟩
  exact (image p).trans (and_congr_right fun hD' => (agree p hp).symm.trans ((marker p).trans
    ⟨fun hh => hh.elim (fun ha => ((truth p).mp ha).2) (fun eq => (no_ordinal' p hD' (eq ▸ hα)).elim),
      fun hq => Or.inl ((truth p).mpr ⟨hVX p hp, hq⟩)⟩))

/-- 由同一实际 E-超幂计算的像类型，再按给定查询域投影。 -/
def Et_stretch_d (hZF : M.Models ZF) (ω κ L F X R t D v : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ b d N S i t', Smem_d I b X R ∧ Smem_d I d N S ∧ It_ultra_d hZF ω κ L F b d i ∧
    Rd_entry_d t t' i ∧ ∀ p, M.mem p v ↔ M.mem p D ∧ M.mem p t'

/-- 任意内部有限元组都有无界多个 κ；同时给出 V(η+1) 中的完整类型及其 Vη 前驱。
    前驱对每个 τ<θ 都可由实际强扩展器伸展，保留同一元组及指定常量 θ。 -/
theorem woodin_type_stretch_l (hZFC : M.Models ZFC) {θ η : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ)
    (hη : M.IsOrdinal η) (hθη : M.mem θ η) :
    let hZF := ZFC.models_zf_l hZFC
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω X Z μ W c Q d S, M.IsOmega ω ∧ V_d I θ X ∧ V_d I η Z ∧
      M.SuccessorOf μ η ∧ V_d I μ W ∧ Smem_d I c Z Q ∧ Smem_d I d W S ∧
      ∀ n s, M.mem n ω → Fn0_d n Z s → ∀ α, M.mem α θ →
      ∃ κ B U D t u, M.mem α κ ∧ M.mem κ θ ∧ V_d I κ B ∧
        (∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) ∧ Tt_realized_d I ω c Z Q n s θ U D t ∧
        Tt_realized_d I ω d W S n s θ U D u ∧ Tm_minus_d I ω D u t ∧
        ∀ τ, M.mem τ θ → ∃ L K F R V B₀ U₀ D₀ v,
          M.mem L θ ∧ M.mem κ L ∧ M.mem τ L ∧ M.mem ω L ∧
          M.IsRegularCardinal I L ∧ M.IsStrongLimitCardinal I L ∧ V_d I L V ∧
          Ex_short_d hZF ω κ L F ∧ Ep_source_d hZF ω κ K X R ∧ Ex_strength_d hZF ω κ L X F ∧
          Sc_inaccessible_d ω X L ∧ It_local_d ω X κ L F ∧ V_d I τ B₀ ∧
          (∀ x, M.mem x U₀ ↔ M.mem x B₀ ∨ x = τ) ∧
          Tt_realized_d I ω c Z Q n s θ U₀ D₀ v ∧ Et_stretch_d hZF ω κ L F X R t D₀ v := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, X, hω, hX, all⟩ := woodin_marked_strength_l hZFC hd
  obtain ⟨ω₀, _, hω₀, hωθ, regular, _⟩ := hd
  have eqω := hZF.1.eq_of_same_members ω₀ ω (fun x => ⟨hω₀.2 ω hω.1 x, hω.2 ω₀ hω₀.1 x⟩)
  subst ω₀
  have hθ := regular.isLimitOrdinal
  have hωX := ZF.v_ordinal_mem_l I hZF hX hωθ
  have ht := ZF.v_transitive_l I hZF hX
  obtain ⟨Z, hZ⟩ := ZF.v_exists_l I hZF hη
  have hθZ := ZF.v_ordinal_mem_l I hZF hZ hθη
  have hXZ := ZF.v_mono_l I hZF hX hZ (hη.transitive θ hθη)
  obtain ⟨c, Q, code⟩ := smdl_membership_l I hZF ⟨θ, hθZ⟩
  obtain ⟨μ, hμ⟩ := KP.exists_successor (ZF.modelsKP hZF) η
  obtain ⟨W, hW⟩ := ZF.v_exists_l I hZF (KP.successor_isOrdinal (ZF.modelsKP hZF) hη hμ)
  have hZW := ZF.v_mono_l I hZF hZ hW (fun x hx => (hμ x).mpr (Or.inl hx))
  obtain ⟨d, S, upper⟩ := smdl_membership_l I hZF ⟨θ, hZW θ hθZ⟩
  have hωη := hη.transitive θ hθη ω hωθ
  refine ⟨ω, X, Z, μ, W, c, Q, d, S, hω, hX, hZ, hμ, hW, code, upper, fun n s hn hs α hα => ?_⟩
  obtain ⟨A, truth, relation⟩ := tt_truth_exists_l I hZF ω c n s θ X
  obtain ⟨C, κ, marker, above, hκ, family⟩ := all A (fun p hp => ((truth p).mp hp).1) relation α hα
  obtain ⟨B, U, hB, hUX, constants⟩ := tt_constants_exists_l hZF hX hθ hκ
  obtain ⟨D, t, pool, type, _⟩ := tt_type_exists_l I hZF hω c n s θ U
  have hDX := pool.rank_mem_l hZF hω hX hθ hωX hn hUX
  have lower : Tt_realized_d I ω c Z Q n s θ U D t :=
    ⟨code.1, hn, hs, hθZ, fun x hx => hXZ x (ht U hUX x hx), pool, type⟩
  obtain ⟨u, truthU, _⟩ := tt_truth_exists_l I hZF ω d n s θ D
  have fs := fn0_function_l (ZF.modelsKP hZF) hs
  have lifted : Tt_realized_d I ω d W S n s θ U D u :=
    ⟨upper.1, hn, fn0_of_function_l (ZF.modelsKP hZF) ⟨fs.1, fs.2.1, fun i hi =>
      (fs.2.2 i hi).imp fun x hx => ⟨hZW x hx.1, hx.2⟩⟩, hZW θ hθZ,
      fun x hx => hZW x (lower.constants x hx), pool, truthU⟩
  -- 定义域由实际公式查询核验，再把构造所得前驱与原低层类型逐查询识别。
  obtain ⟨p, _, read, defined⟩ := tt_minus_guarded_l hZF hω hZ hW hμ (hη.transitive ω hωη) hB constants upper lifted
  obtain ⟨c', Q', t', code', minus, realized⟩ := defined.mp
    (read.mpr ⟨hs, hθZ, lower.constants κ ((constants κ).mpr (Or.inr rfl))⟩)
  obtain ⟨ec, eQ⟩ := smem_unique_l I hZF.1 code' code
  subst c' Q'
  have et := hZF.1.eq_of_same_members t' t (fun p => (realized.truth p).trans (type p).symm)
  subst t'
  refine ⟨κ, B, U, D, t, u, above, hκ, hB, constants, lower, lifted, minus, fun τ hτ => ?_⟩
  obtain ⟨L, K, F, R, V, Y, j, hL, hκL, hτL, hωL, rL, sL, hV, short, source, strong⟩ := family τ hτ
  have hVX := ZF.v_mono_l I hZF hV hX (hθ.1.transitive L hL)
  obtain ⟨b, d, N, S, i, κ', D', t₀, t', hm, hm', ultra, crit, bound, cover, hDD, htt, type₀, image⟩ :=
    strong.type_image_l hZF hω hX (hθ.1.mem hα) hVX truth marker pool hDX
  have eqt := hZF.1.eq_of_same_members t₀ t (fun p => (type₀ p).trans (type p).symm)
  subst t₀
  have hi := ultra.elementary_l hZF hm.1 hm'.1
  have hN := ultra.transitive_l hZF hm'.1
  obtain ⟨U', _, hUU⟩ := hi.1.1.2.2 U hUX
  have constants_cover := hi.type_constants_cover_l hZF hω hX hθ hκ hN hm hm' crit.image hUU hB
    (fun x hx => (constants x).mpr (Or.inl hx)) hV cover bound
  -- τ 型的整个查询域已在共同的 V_L 中，因此其中的新名字列属于超幂目标。
  obtain ⟨B₀, U₀, hB₀, hU₀V, constants₀⟩ := tt_constants_exists_l hZF hV rL.isLimitOrdinal hτL
  obtain ⟨D₀, v, pool₀, type₀, _⟩ := tt_type_exists_l I hZF hω c n s θ U₀
  have hD₀V := pool₀.rank_mem_l hZF hω hV rL.isLimitOrdinal (ZF.v_ordinal_mem_l I hZF hV hωL) hn hU₀V
  have vt := ZF.v_transitive_l I hZF hV
  have domain_cover := hi.type_pool_cover_l hZF hω hX hθ hωX hN hm hm' hn
    (crit.fixed n (short.critical.1.transitive ω short.uncountable n hn)) hUX hUU hDD pool pool₀
    (fun x hx => constants_cover x (vt U₀ hU₀V x hx)) (fun p hp => cover p (vt D₀ hD₀V p hp))
  have projection p : M.mem p v ↔ M.mem p D₀ ∧ M.mem p t' := (type₀ p).trans
    ⟨fun hh => ⟨hh.1, (image p (vt D₀ hD₀V p hh.1)).mpr ⟨domain_cover p hh.1, hh.2⟩⟩,
      fun hh => ⟨hh.1, ((image p (vt D₀ hD₀V p hh.1)).mp hh.2).2⟩⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, strength, _, inaccessible, locality⟩ := strong
  exact ⟨L, K, F, R, V, B₀, U₀, D₀, v, hL, hκL, hτL, hωL, rL, sL, hV, short, source, strength,
    inaccessible, locality, hB₀, constants₀,
    ⟨code.1, hn, hs, hθZ, fun x hx => hXZ x (hVX x (vt U₀ hU₀V x hx)), pool₀, type₀⟩,
    b, d, N, S, i, t', hm, hm', ultra, htt, projection⟩

end YesMetaZFC.SetTheory.LargeCardinal
