import YesMetaZFC.SetTheory.LargeCardinal.ExtenderDerivedLimit
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderStrength
import YesMetaZFC.SetTheory.LargeCardinal.MeasurableInaccessible
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderStrengthRank
import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessibleRank
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderInitial
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankLocal

/-! # 按指定秩自动选择短扩展器并恢复覆盖与谓词一致性

临界点随 A 固定；长度随 ν 选择为实际不可达 L>ν。每个严格秩层的短枚举
使同一全系统覆盖整个 V_L；传递坍塌和新谓词保留完整谓词初等性。
同一目标缺少某个 L 的子集，故强度恰为 L；该事实由源内实际有界超幂记录。
长度在所属模型中满足原始的不可达性公式，该公式随初等图及严格秩截断保持。
实际枚举与强度证书一同保留，严格正则秩截断自动取得同一扩展器的全部所属证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 强性证书与同一张 F、同一全系统及其实际商投影绑定。 -/
def Ep_strong_limit_d (hZF : M.Models ZF) (ω κ L X R A V F j Y : M.Domain) : Prop :=
  ∃ J O Z D p T S q c C W, Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z D p T S ∧
    Di_limit_d D p T S q C W ∧ Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C W ∧ Wf_rel_d C W ∧
    Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O D p T S ∧ Ep_collapse_d hZF ω X R q c C W ∧
    Ee_factor_d hZF j Y q C W ∧ Ep_strength_d hZF ω κ L X R A V j Y q c C W ∧
    Ex_strength_d hZF ω κ L X F ∧ Er_level_d X L V ∧ Sc_inaccessible_d ω X L ∧ It_local_d ω X κ L F

/-- 从已构造的强性证书自动得到严格正则秩截断的源与全部扩展器证书。 -/
theorem Ep_strong_limit_d.rank_l (hZF : M.Models ZF) {ω κ K L X R A V F j Y α U : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hU : M.mem U X) (rank : Vr_d X α U)
    (hα : M.IsLimitOrdinal α) (regular : Sc_regular_d X α) (hL : M.mem L U) (hF : M.mem F U)
    (h : Ep_strong_limit_d hZF ω κ L X R A V F j Y) : ∃ S,
      Ep_source_d hZF ω κ K U S ∧ Ex_strength_d hZF ω κ L U F ∧
      Er_level_d U L V ∧ Sc_inaccessible_d ω U L ∧ It_local_d ω U κ L F := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, strength, level, inaccessible, locality⟩ := h
  have above : M.mem κ L := by
    obtain ⟨_, _, _, _, pre⟩ := locality
    simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff] at pre
    exact (Formula.satisfies_mem_iff _ _ _).mp pre.1.2.2.2.2.1
  have limit := inaccessible.limit_l (ZF.modelsKP hZF) source.transitive source.theory.algebra.pair
  have ht := rank.transitive_l hZF source.transitive hU
  have hκ := ht L hL κ above
  have hω := rank.subset_mem_l source.transitive hU hκ source.omega_mem source.below
  obtain ⟨c, S, hm⟩ := smdl_membership_l (kp_pair_l (ZF.modelsKP hZF)) hZF ⟨ω, hω⟩
  obtain ⟨K', cut⟩ := source.rank_l hZF hU rank hα regular hω hm hκ (limit.1.mem above) source.below
  have eq := hZF.1.eq_of_same_members K' K (fun f => (cut.finite f).trans (source.finite f).symm)
  subst K'
  have level' := level.rank_l hZF cut source.transitive hU rank hα hL
  exact ⟨S, cut, strength.rank_l hZF cut source.transitive hU rank hα hL hF limit above level', level',
    inaccessible.rank_l hZF source.transitive source.theory.algebra.pair hU rank hα hL,
    locality.rank_l hZF source hU rank hα hκ hL hF⟩

theorem woodin_rank_strength_l (hZFC : M.Models ZFC) {δ : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ) :
    let hZF := ZFC.models_zf_l hZFC
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω X, M.IsOmega ω ∧ V_d I δ X ∧ ∀ A, M.MemberSubset A X → ∃ κ, M.mem κ δ ∧
      ∀ ν, M.mem ν δ → ∃ L K F R V Y j, M.mem L δ ∧ M.mem κ L ∧ M.mem ν L ∧ M.mem ω L ∧
        M.IsRegularCardinal I L ∧ M.IsStrongLimitCardinal I L ∧ V_d I L V ∧
        Ex_short_d hZF ω κ L F ∧ Ep_source_d hZF ω κ K X R ∧ Ep_strong_limit_d hZF ω κ L X R A V F j Y := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, X, hω, hX, all⟩ := woodin_extender_l hZFC hd
  have inaccessible α (hα : M.mem α δ) := woodin_inaccessible_above_l I hZFC hω hd hα
  obtain ⟨ω₀, _, hω₀, hωδ, hr, hs, _⟩ := hd
  have eqω := hZF.1.eq_of_same_members ω₀ ω (fun x => ⟨hω₀.2 ω hω.1 x, hω.2 ω₀ hω₀.1 x⟩)
  subst ω₀
  refine ⟨ω, X, hω, hX, fun A hA => ?_⟩
  obtain ⟨κ, hκ, family⟩ := all A hA
  refine ⟨κ, hκ, fun ν hν => ?_⟩
  obtain ⟨α, hα, hκα, hνα⟩ : ∃ α, M.mem α δ ∧ (κ = α ∨ M.mem κ α) ∧ (ν = α ∨ M.mem ν α) := by
    rcases hr.isCardinal.1.wellOrder.linear.compare κ hκ ν hν with same | lt | gt
    · exact ⟨ν, hν, Or.inl (hZF.1.eq_of_same_members κ ν same), Or.inl rfl⟩
    · exact ⟨ν, hν, Or.inr lt, Or.inl rfl⟩
    · exact ⟨κ, hκ, Or.inl rfl, Or.inr gt⟩
  obtain ⟨L, hαL, hL, hωL, rL, sL⟩ := inaccessible α hα
  have hκL := hκα.elim (fun eq => eq.symm ▸ hαL) (rL.isCardinal.1.transitive α hαL κ)
  have hνL := hνα.elim (fun eq => eq.symm ▸ hαL) (rL.isCardinal.1.transitive α hαL ν)
  obtain ⟨V₀, hV₀⟩ := ZF.v_exists_l I hZF rL.isCardinal.1
  obtain ⟨ν₀, Y, B, j, W, k, S, F, K, _, R, hw, hLν, hLk, hS, hSY, hF, short, _, _, source, model⟩ :=
    family L hL hκL
  obtain ⟨J, O, Z, D, p, T, V, q, c, C, Q, system, limit, code, wf, elementary, collapse, factor, length⟩ := model
  obtain ⟨hY, _, _, hW, hWY, embed, crit, _, agreement⟩ := hw
  have hν₀ := v_ordinal_l I hW
  have sub : M.MemberSubset V₀ W := ZF.v_mono_l I hZF hV₀ hW (hν₀.transitive L hLν)
  have cover := er_inaccessible_cover_l hZFC source hX hr hs hκ embed hY crit
    (crit.ordinal_image.transitive L hLk) hκL hωL rL sL hS (hY S hSY) hF system limit hV₀ (fun x hx => hWY x (sub x hx))
  have strength := ep_strength_l hZFC source hr hωδ hX (ZFC.inaccessible_hereditary_l I hZFC hω hωδ hr hs hX)
    embed hY crit (crit.ordinal_image.transitive L hLk) hκL hωL rL sL (hY S hSY) hF short.measures short.coherent
    system limit code collapse factor hV₀ length cover (fun x hx => agreement x (sub x hx))
  have hLX := ZF.v_ordinal_mem_l I hZF hX hL
  have hFX := short.measures.rank_mem_l hZF short.graph.1 hω hX hr.isLimitOrdinal source.omega_mem source.cardinal_mem hLX
  obtain ⟨exact_strength, level⟩ : Ex_strength_d hZF ω κ L X F ∧ Er_level_d X L V₀ := by
    obtain ⟨b, d, N, S', B', i, k', κ', hm, hn, _, hi, _, crit', bound, cover', _, _, _, _, _, _, _, _, realizer, missing⟩ := strength
    obtain ⟨t, e, ht, ct, wc, bij, he, comp⟩ := realizer
    have ultra : It_ultra_d hZF ω κ L F b d i :=
      ⟨X, R, N, S', J, O, Z, D, p, T, V, q, c, C, Q, t, e, hm, hn, system, limit, code, wc, bij, he, ht, ct, hi,
        hi.1.1.1.1, fun x y => (comp x y).trans
          ⟨And.right, fun ⟨E, hxE, hEy⟩ => ⟨ht.1.1.input_mem_of_pairMember hxE, E, hxE, hEy⟩⟩⟩
    exact ep_exact_strength_l hZFC source hX hr.isLimitOrdinal hL hκL hωL rL sL hV₀ (short.measures.source_l hZF X)
      hFX hm hn ultra crit'.image bound cover' missing
  exact ⟨L, K, F, R, V₀, Y, j, hL, hκL, hνL, hωL, rL, sL, hV₀, short, source,
    J, O, Z, D, p, T, V, q, c, C, Q, system, limit, code, wf, elementary, collapse, factor, strength, exact_strength, level,
    sc_v_inaccessible_l hZF hX hLX hωL rL sL,
    short.local_l hZF hX hr.isLimitOrdinal hLX hFX⟩

end YesMetaZFC.SetTheory.LargeCardinal
