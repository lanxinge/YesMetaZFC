import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.SourceProjection
import YesMetaZFC.SetTheory.Card.Aleph.Multiplication
import YesMetaZFC.SetTheory.Card.Cofinality.Composition
import YesMetaZFC.SetTheory.Card.Cofinality.LimitLength
import YesMetaZFC.SetTheory.Card.Omega
import YesMetaZFC.SetTheory.CountableChain
import YesMetaZFC.SetTheory.Card.SmallEnumeration
import YesMetaZFC.SetTheory.Choice
import YesMetaZFC.SetTheory.LargeCardinal.Extender.DerivedLimit
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Strength
import YesMetaZFC.SetTheory.LargeCardinal.Extender.StrengthRank
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.SetTheory.LargeCardinal.Extender.LevelTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RankLift
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.Model.SetTheory.Types.ProgramReflect
import YesMetaZFC.Model.SetTheory.Types.PredecessorCode
import YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticNumericTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Game.Elastic
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.SetTheory.LargeCardinal.Game.Reset
import YesMetaZFC.SetTheory.LargeCardinal.Types.OneStep

/-! # 可测基数的正则性

每个有界初段的补集测度一。若短序列共尾，对其全部值取这些补集的交，
完备性给出非空的测度一集合，而共尾性迫使该交为空。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Measurable_d.regular_l (hZF : M.Models ZF) {κ : M.Domain} (h : Measurable_d I κ) : M.IsRegularCardinal I κ := by
  obtain ⟨card, ω, U, hω, hωκ, hU, hn, hc⟩ := h
  have limit := ZF.infiniteCardinal_isLimitOrdinal hZF I hω (ZF.omega_cardinal_l I hZF hω)
    ⟨card, ZF.exists_inclusionInjection hZF I (card.1.transitive ω hωκ)⟩
  have tail α (hα : M.mem α κ) : ∃ r, M.mem r U ∧ ∀ x, M.mem x r ↔ M.mem x κ ∧ ¬ M.mem x α := by
    obtain ⟨f, ff⟩ := ZF.exists_identityBijection hZF I α
    obtain ⟨r, hr, rs⟩ := ed_range_complement_l I hZF hU hn hc hα (ff.1.1.mono_target_l I (card.1.transitive α hα))
    exact ⟨r, hr, fun x => (rs x).trans (and_congr_right fun _ => not_congr
      ⟨fun ⟨_, _, hx⟩ => ff.1.1.output_mem_of_pairMember hx, fun hx => ff.2 x hx⟩)⟩
  refine ⟨card, limit.hasCofinalOrdinalSequence_self hZF I, fun μ ⟨f, seq⟩ => ?_⟩
  rcases card.1.trichotomy hZF.1 seq.isIncreasing.1.1.1 (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) κ μ) with eq | lt | small
  · exact Or.inl (hZF.1.eq_of_same_members κ μ eq)
  · exact Or.inr lt
  apply False.elim
  have fn := seq.isSetFunctionFromTo
  let ρ : Env M 2 := ⟨Fin.cases f (fun _ => κ), fun _ => κ⟩
  let φ : BinarySchema 2 := {
    body := .forallE (.iff (.mem .newest (.bound 1)) (.conj (.mem .newest (.bound 4))
      (.neg (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 3) .newest (.bound 4)) (.mem (.bound 1) .newest)))))) }
  have read i r : φ.denote ρ i r ↔ ∀ x, M.mem x r ↔ M.mem x κ ∧ ¬ ∃ α, M.PairMember I i α f ∧ M.mem x α := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
  have total i (hi : M.mem i μ) : ∃ r, φ.denote ρ i r ∧ M.mem r U := by
    obtain ⟨α, hα, hiα⟩ := fn.2.2 i hi
    obtain ⟨r, hr, rs⟩ := tail α hα
    exact ⟨r, (read i r).mpr (fun x => (rs x).trans (and_congr_right fun _ => not_congr
      ⟨fun hx => ⟨α, hiα, hx⟩, fun ⟨β, hiβ, hx⟩ => fn.1.2 i β α hiβ hiα ▸ hx⟩)), hr⟩
  have unique i r s (hr : φ.denote ρ i r) (hs : φ.denote ρ i s) : r = s :=
    hZF.1.eq_of_same_members r s (fun x => ((read i r).mp hr x).trans ((read i s).mp hs x).symm)
  obtain ⟨g, gf, gs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ
    (fun i hi => (total i hi).imp fun _ hr => hr.1) (fun i _ => unique i) (fun i r hi hr => by
      obtain ⟨s, hs, hsU⟩ := total i hi
      exact unique i s r hs hr ▸ hsU)
  obtain ⟨r, hr, rs⟩ := hc μ small g (fn0_of_function_l (ZF.modelsKP hZF) gf)
  obtain ⟨x, hx⟩ := hU.2.1 r hr
  obtain ⟨hxκ, all⟩ := (rs x).mp hx
  obtain ⟨A, range, un⟩ := seq.isLimit.2.2
  obtain ⟨α, hα, hxα⟩ := (un x).mp hxκ
  obtain ⟨i, hiα⟩ := (range α).mp hα
  have hi := fn.input_mem_of_pairMember hiα
  obtain ⟨s, hs, his⟩ := gf.2.2 i hi
  exact (((read i s).mp ((gs i s).mp his).2 x).mp (all i hi s hs his)).2 ⟨α, hiα, hxα⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 可测基数不可达及武丁基数下方的不可达选择

ZF 中已经得到正则性及小幂集不存在反向单射。对象模型的选择公理提供
幂集的实际序数编号，遂得到强极限性，并接到原武丁测度构造上。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Measurable_d.strong_limit_l (hZFC : M.Models ZFC) {κ : M.Domain}
    (h : Measurable_d I κ) : M.IsStrongLimitCardinal I κ := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨card, _, U, _, _, hU, hn, hc⟩ := h
  refine ⟨card, fun α hα P power => ?_⟩
  have no := ed_power_injection_l I hZF hU hn hc hα power
  obtain ⟨δ, F, hδ, ff, onto⟩ := ZFC.ordinal_enum_l hZFC I P
  obtain ⟨id, ii⟩ := ZF.exists_identityBijection hZF I δ
  have bound := ZF.ordinal_image_bound_l I hZF hδ ⟨id, ii.1⟩ ff onto
  obtain ⟨χ, hχ⟩ := ZF.exists_hartogsNumber hZF I δ
  obtain ⟨ν, g, _, νcard, bij⟩ := ZF.small_enumeration_l I hZF (hχ.isCardinal hZF I)
    ((hχ.2 δ hδ).mpr ⟨id, ii.1⟩) bound
  have lt : M.mem ν κ := by
    rcases νcard.1.trichotomy hZF.1 card.1 (KP.difference_exists_d (ZF.modelsKP hZF))
        (KP.intersection_exists_d (ZF.modelsKP hZF) ν κ) with eq | lt | gt
    · exact (no ⟨g, hZF.1.eq_of_same_members ν κ eq ▸ bij.1⟩).elim
    · exact lt
    · obtain ⟨r, ri⟩ := ZF.exists_inclusionInjection hZF I (νcard.1.transitive κ gt)
      exact (no (ZF.exists_compositionInjection hZF I ri bij.1)).elim
  obtain ⟨r, rb⟩ := ZF.exists_inverseBijection hZF I bij
  obtain ⟨s, si⟩ := ZF.exists_inclusionInjection hZF I (card.1.transitive ν lt)
  exact ⟨ZF.exists_compositionInjection hZF I rb.1 si, fun eq =>
    (eq.symm hZF I).elim fun f hf => no ⟨f, hf.1⟩⟩

/-- 长度由原武丁强嵌入产生的非主完备测度选择，正则和强极限均已实际证明。 -/
theorem woodin_inaccessible_above_l (hZFC : M.Models ZFC) {ω δ α : M.Domain}
    (hω : M.IsOmega ω) (hd : Woodin_d I δ) (hα : M.mem α δ) :
    ∃ κ, M.mem α κ ∧ M.mem κ δ ∧ M.mem ω κ ∧ M.IsRegularCardinal I κ ∧ M.IsStrongLimitCardinal I κ := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨κ, hακ, hκδ, meas⟩ := woodin_measurable_above_l I hZF hd hα
  have hr := meas.regular_l I hZF
  have hs := meas.strong_limit_l I hZFC
  obtain ⟨_, ω₀, _, hω₀, hωκ, _⟩ := meas
  have eq := hZF.1.eq_of_same_members ω₀ ω (fun x => ⟨hω₀.2 ω hω.1 x, hω.2 ω₀ hω₀.1 x⟩)
  exact ⟨κ, hακ, hκδ, eq ▸ hωκ, hr, hs⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 按指定秩自动选择短扩展器并恢复覆盖与谓词一致性

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
    Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F ∧ Er_level_d X L V ∧ Sc_inaccessible_d ω X L ∧ It_local_d (kp_pair_l (ZF.modelsKP hZF)) ω X R κ L F

/-- 从已构造的强性证书自动得到严格正则秩截断的源与全部扩展器证书。 -/
theorem Ep_strong_limit_d.rank_l (hZF : M.Models ZF) {ω κ K L X R A V F j Y α U : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hU : M.mem U X) (rank : Vr_d X α U)
    (hα : M.IsLimitOrdinal α) (regular : Sc_regular_d X α) (hL : M.mem L U) (hF : M.mem F U)
    (h : Ep_strong_limit_d hZF ω κ L X R A V F j Y) : ∃ S,
      Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K U S ∧ Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L U F ∧
      Er_level_d U L V ∧ Sc_inaccessible_d ω U L ∧ It_local_d (kp_pair_l (ZF.modelsKP hZF)) ω U S κ L F := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, strength, level, inaccessible, locality⟩ := h
  have above : M.mem κ L := by
    obtain ⟨_, _, _, _, pre⟩ := (it_local_mem_l (kp_pair_l (ZF.modelsKP hZF)) source.code).mp locality
    simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff] at pre
    exact (Formula.satisfies_mem_iff _ _ _).mp pre.1.2.2.2.2.1
  have limit := inaccessible.limit_l (ZF.modelsKP hZF) source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair
  have ht := rank.transitive_l source.transitive hU
  have hκ := ht L hL κ above
  have hω := rank.subset_mem_l source.transitive hU hκ source.omega_mem source.below
  obtain ⟨c, S, hm⟩ := smdl_membership_l (kp_pair_l (ZF.modelsKP hZF)) hZF ⟨ω, hω⟩
  obtain ⟨K', cut⟩ := source.rank_l hZF hU rank hα regular hω hm hκ (limit.1.mem above) source.below
  have eq := hZF.1.eq_of_same_members K' K (fun f => ((cut.finite_l (ZF.modelsKP hZF)) f).trans ((source.finite_l (ZF.modelsKP hZF)) f).symm)
  subst K'
  have level' := level.rank_l hZF cut source.transitive hU rank hα hL
  exact ⟨S, cut, strength.rank_l hZF cut source.transitive hU rank hα hL hF limit above level', level',
    inaccessible.rank_l hZF source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair hU rank hα hL,
    locality.rank_l hZF source hU rank hα hκ hL hF ⟨c, hm⟩⟩

theorem woodin_rank_strength_l (hZFC : M.Models ZFC) {δ : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ) :
    let hZF := ZFC.models_zf_l hZFC
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω X, M.IsOmega ω ∧ V_d I δ X ∧ ∀ A, M.MemberSubset A X → ∃ κ, M.mem κ δ ∧
      ∀ ν, M.mem ν δ → ∃ L K F R V Y j, M.mem L δ ∧ M.mem κ L ∧ M.mem ν L ∧ M.mem ω L ∧
        M.IsRegularCardinal I L ∧ M.IsStrongLimitCardinal I L ∧ V_d I L V ∧
        Ex_short_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R ∧ Ep_strong_limit_d hZF ω κ L X R A V F j Y := by
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
  obtain ⟨exact_strength, level⟩ : Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F ∧ Er_level_d X L V₀ := by
    obtain ⟨b, d, N, S', B', i, k', κ', hm, hn, _, hi, _, crit', bound, cover', _, _, _, _, _, _, _, _, realizer, missing⟩ := strength
    obtain ⟨t, e, ht, ct, wc, bij, he, comp⟩ := realizer
    have ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F b d i :=
      ⟨X, R, N, S', J, O, Z, D, p, T, V, q, c, C, Q, t, e, hm, hn, system, limit, code, wc, bij, he, ht, ct, hi,
        hi.1.1.1.1, fun x y => (comp x y).trans
          ⟨And.right, fun ⟨E, hxE, hEy⟩ => ⟨ht.1.1.input_mem_of_pairMember hxE, E, hxE, hEy⟩⟩⟩
    exact ep_exact_strength_l hZFC source hX hr.isLimitOrdinal hL hκL hωL rL sL hV₀ (short.measures.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) X)
      hFX hm hn ultra crit'.image bound cover' missing
  exact ⟨L, K, F, R, V₀, Y, j, hL, hκL, hνL, hωL, rL, sL, hV₀, short, source,
    J, O, Z, D, p, T, V, q, c, C, Q, system, limit, code, wf, elementary, collapse, factor, strength, exact_strength, level,
    sc_v_inaccessible_l hZF hX hLX hωL rL sL,
    short.local_l hZF hX hr.isLimitOrdinal hLX hFX source.code⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 武丁强扩展器对谓词截面的作用

给真值码谓词加入一个序数标记 α。低秩一致性和截面初等性迫使 α 固定，
而强度超过 α，故临界点严格大于 α。标记不进入由有序对组成的类型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 在强度以下只有一个序数标记时，该标记严格低于临界点。 -/
theorem Ep_strength_d.above_l (hZF : M.Models ZF)
    {ω δ κ L X R A V j Y q c C W α : M.Domain}
    (hω : M.IsOmega ω) (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X)
    (hL : M.IsOrdinal L) (hLX : M.mem L X) (hα : M.mem α L) (hαV : M.mem α V)
    (marker : ∀ x, M.mem x L → (M.mem x A ↔ x = α))
    (h : Ep_strength_d hZF ω κ L X R A V j Y q c C W) : M.mem α κ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨b, d, N, S, B, i, k, κ', hm, hn, hN, hi, embed, crit, bound, _, _, _, _, _, _, _, _, agree, _⟩ := h
  have ht := v_transitive_l I hX
  have hαX := ht L hLX α hα
  obtain ⟨a, _, ha⟩ := hi.1.1.2.2 α hαX
  obtain ⟨D, _, hD⟩ := hi.1.1.2.2 L hLX
  obtain ⟨t, pair⟩ := KP.exists_pair (ZF.modelsKP hZF) α α
  have singleton x : M.mem x t ↔ x = α := (pair x).trans ⟨fun hh => hh.elim id id, Or.inl⟩
  have htX := v_subset_mem_l I hX hLX (fun x hx => (singleton x).mp hx ▸ hα)
  obtain ⟨t', _, htt⟩ := hi.1.1.2.2 t htX
  have trace x : M.mem x t ↔ M.mem x L ∧ M.mem x A := (singleton x).trans
    ⟨fun eq => ⟨eq ▸ hα, (marker x (eq ▸ hα)).mpr eq⟩, fun hh => (marker x hh.1).mp hh.2⟩
  have image := spred_trace_l I hZF hω embed hN hD htt trace
  have αD := hi.ordinal_le_l hZF hω ht hN hm hn hD hL α hα
  have αB := (agree α hαV).mp ((marker α hα).mpr rfl)
  have tr := spred_delta_l I hZF hω embed ht hN (n := 2)
    (Formula.forallMem (.bound 1) (Formula.extensionalEq .newest (.bound 1)))
    (by simp) (.forallMem _ (.atom _ _ _))
    ⟨Fin.cases α (fun _ => t), fun _ => α⟩ ⟨Fin.cases a (fun _ => t'), fun _ => a⟩
    (Fin.cases ha (fun _ => htt))
  simp only [Formula.satisfies_forallMem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1] at tr
  have eq : α = a := tr.mp (fun x hx => (singleton x).mp hx) α ((image α).mpr ⟨αD, αB⟩)
  subst a
  rcases Structure.IsOrdinal.trichotomy hZF.1 (hL.mem hα) crit.ordinal
      (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) α κ) with he | he | he
  · have e := hZF.1.eq_of_same_members α κ he
    exact (crit.moved (hi.1.1.1.2 κ κ κ' (e ▸ ha) crit.image)).elim
  · exact he
  · have hkα := (ed_member_l I hZF hω embed ht hN crit.image ha).mp he
    exact (KP.mem_irrefl_d (ZF.modelsKP hZF) κ'
      (crit.ordinal_image.transitive α (bound α hα) κ' hkα)).elim

/-- 任意关系码谓词都可加标记；所得强扩展器的临界点超过给定 α。
    C 的完整定义及原强度证书一同返回，类型截面随后可直接消费它们。 -/
theorem woodin_marked_strength_l (hZFC : M.Models ZFC) {δ : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ) :
    let hZF := ZFC.models_zf_l hZFC
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω X, M.IsOmega ω ∧ V_d I δ X ∧ ∀ A, M.MemberSubset A X → M.IsSetRelation I A →
      ∀ α, M.mem α δ → ∃ C κ, (∀ p, M.mem p C ↔ M.mem p A ∨ p = α) ∧ M.mem α κ ∧ M.mem κ δ ∧
        ∀ ν, M.mem ν δ → ∃ L K F R V Y j, M.mem L δ ∧ M.mem κ L ∧ M.mem ν L ∧ M.mem ω L ∧
          M.IsRegularCardinal I L ∧ M.IsStrongLimitCardinal I L ∧ V_d I L V ∧
          Ex_short_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R ∧ Ep_strong_limit_d hZF ω κ L X R C V F j Y := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, X, hω, hX, all⟩ := woodin_rank_strength_l hZFC hd
  refine ⟨ω, X, hω, hX, fun A hA rel α hα => ?_⟩
  let φ : UnarySchema 2 := { body := .disj (.mem .newest (.bound 2)) (Formula.extensionalEq .newest (.bound 1)) }
  let ρ : Env M 2 := ⟨Fin.cases α (fun _ => A), fun _ => A⟩
  obtain ⟨C, sep⟩ := ZF.separation_exists_d hZF φ ρ X
  have spec p : M.mem p C ↔ M.mem p A ∨ p = α := by
    have eq : φ.denote ρ p ↔ M.mem p A ∨ p = α := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
        Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
    exact (sep p).trans ((and_congr_right fun _ => eq).trans
      ⟨And.right, fun hp => ⟨hp.elim (hA p) (fun he => he ▸ ZF.v_ordinal_mem_l I hZF hX hα), hp⟩⟩)
  obtain ⟨κ, hκ, family⟩ := all C (fun p hp => ((sep p).mp hp).1)
  obtain ⟨L, K, F, R, V, Y, j, hL, _, hαL, _, rL, _, hV, _, _, strong⟩ := family α hα
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, strength, _⟩ := strong
  have above := strength.above_l hZF hω hX rL.isCardinal.1 (ZF.v_ordinal_mem_l I hZF hX hL)
    hαL (ZF.v_ordinal_mem_l I hZF hV hαL) (fun x hx => (spec x).trans
      ⟨fun hh => hh.elim (fun ha => by
        obtain ⟨a, b, pair⟩ := rel x ha
        exact (pair.not_transitive_l M (KP.mem_irrefl_d (ZF.modelsKP hZF)) (rL.isCardinal.1.mem hx).transitive).elim) id,
        Or.inr⟩)
  exact ⟨C, κ, spec, above, hκ, family⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 强扩展器中的完整类型像

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
    ∃ b d N S i κ' D' t t', Smem_d I b X R ∧ Smem_d I d N S ∧ It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F b d i ∧
      Wd_crit_d I X i κ κ' ∧ M.MemberSubset L κ' ∧ M.MemberSubset V N ∧
      Rd_entry_d D D' i ∧ Rd_entry_d t t' i ∧ Tt_truth_d I ω c n s δ D t ∧
        ∀ p, M.mem p V → (M.mem p t' ↔ M.mem p D' ∧ Tt_query_d I ω c n s δ p) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨J, O, Z, H, π, T, Q, q, a, K, W, system, limit, code, _, _, _, _, strength, _⟩ := h
  obtain ⟨b, d, N, S, B, i, k, κ', hm, hn, hN, hi, embed, crit, bound, cover, _, _, _, _, _, _, _, agree, realizer, _⟩ := strength
  obtain ⟨u, e, hu, constants, collapse, bij, he, comp⟩ := realizer
  have ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F b d i :=
    ⟨X, R, N, S, J, O, Z, H, π, T, Q, q, a, K, W, u, e, hm, hn, system, limit, code,
      collapse, bij, he, hu, constants, hi, hi.1.1.1.1, fun x y => (comp x y).trans
        ⟨And.right, fun ⟨E, hxE, hEy⟩ => ⟨hu.1.1.input_mem_of_pairMember hxE, E, hxE, hEy⟩⟩⟩
  have transitive := v_transitive_l I hX
  have no_ordinal p (hp : M.mem p D) : ¬ M.IsOrdinal p := by
    obtain ⟨_, _, _, _, prod⟩ := pool
    obtain ⟨z, _, e, _, pair⟩ := (prod p).mp hp
    exact fun ho => pair.not_transitive_l M (KP.mem_irrefl_d (ZF.modelsKP hZF)) ho.transitive
  obtain ⟨t, type, _⟩ := tt_truth_exists_l I hZF ω c n s δ D
  have ht := v_subset_mem_l I hX hD (fun p hp => ((type p).mp hp).1)
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

/-- 任意内部有限元组都有无界多个 κ；同时给出 V(η+1) 中的完整类型及其 Vη 前驱。
    原公式识别全部前驱及伸展候选；每个 τ<θ 的伸展保留同一元组及指定常量 θ。 -/
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
        (∃ h, M.IsSetFunctionFromTo (fp_interpretation_l (ZF.models_kpi_l hZF)) h n Z ∧
          Sx_graph_d I (fp_interpretation_l (ZF.models_kpi_l hZF)) s h ∧ ∀ v,
            (Formula.satisfies (⟨Fin.cases v (Fin.cases D (Fin.cases h (Fin.cases n
              (Fin.cases θ (Fin.cases ω (fun _ => W)))))), fun _ => h⟩ : Env M 7)
                (tf_type_local_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) ↔
              Tm_minus_d I ω D u v)) ∧
        ∀ τ, M.mem τ θ → ∃ L K F R V B₀ U₀ D₀ v,
          M.mem L θ ∧ M.mem κ L ∧ M.mem τ L ∧ M.mem ω L ∧
          M.IsRegularCardinal I L ∧ M.IsStrongLimitCardinal I L ∧ V_d I L V ∧
          Ex_short_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R ∧ Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F ∧
          Sc_inaccessible_d ω X L ∧ It_local_d I ω X R κ L F ∧ V_d I τ B₀ ∧
          (∀ x, M.mem x U₀ ↔ M.mem x B₀ ∨ x = τ) ∧
          Tt_realized_d I ω c Z Q n s θ U₀ D₀ v ∧ Et_stretch_d hZF ω κ L F X R t D₀ v ∧
          ∀ z, Formula.satisfies (⟨Fin.cases z (Fin.cases D₀ (Fin.cases t (Fin.cases F
            (Fin.cases X (Fin.cases L (Fin.cases κ (fun _ => ω))))))), fun _ => t⟩ : Env M 8)
              (et_quality_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) ↔
            Et_stretch_d hZF ω κ L F X R t D₀ z := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, X, hω, hX, all⟩ := woodin_marked_strength_l hZFC hd
  obtain ⟨ω₀, _, hω₀, hωθ, regular, _⟩ := hd
  have eqω := hZF.1.eq_of_same_members ω₀ ω (fun x => ⟨hω₀.2 ω hω.1 x, hω.2 ω₀ hω₀.1 x⟩)
  subst ω₀
  have hθ := regular.isLimitOrdinal
  have hωX := ZF.v_ordinal_mem_l I hZF hX hωθ
  have ht := v_transitive_l I hX
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
  have hDX := pool.rank_mem_l (ZF.modelsKP hZF) hω hX hθ hωX hn hUX
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
  -- 同一公式识别全部候选；唯一性把低层完整类型与原语法前驱算子精确接合。
  obtain ⟨h, hh, graph, formula⟩ := tt_predecessor_formula_l hZF hω hZ hW hμ hX hθ hωθ
    code hn hs hθZ lower.constants pool hUX
  have read v := (formula v).trans (show Tt_truth_d I ω c n s θ D v ↔ Tm_minus_d I ω D u v from by
    constructor
    · intro truth
      have eq := hZF.1.eq_of_same_members v t (fun p => (truth p).trans (type p).symm)
      exact eq.symm ▸ minus
    · intro hv
      exact (hv.unique_l I hZF.1 minus).symm ▸ type)
  refine ⟨κ, B, U, D, t, u, above, hκ, hB, constants, lower, lifted, minus, ⟨h, hh, graph, read⟩, fun τ hτ => ?_⟩
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
  have hD₀V := pool₀.rank_mem_l (ZF.modelsKP hZF) hω hV rL.isLimitOrdinal (ZF.v_ordinal_mem_l I hZF hV hωL) hn hU₀V
  have vt := v_transitive_l I hV
  have domain_cover := hi.type_pool_cover_l hZF hω hX hθ hωX hN hm hm' hn
    (crit.fixed n (short.critical.1.transitive ω short.uncountable n hn)) hUX hUU hDD pool pool₀
    (fun x hx => constants_cover x (vt U₀ hU₀V x hx)) (fun p hp => cover p (vt D₀ hD₀V p hp))
  have projection p : M.mem p v ↔ M.mem p D₀ ∧ M.mem p t' := (type₀ p).trans
    ⟨fun hh => ⟨hh.1, (image p (vt D₀ hD₀V p hh.1)).mpr ⟨domain_cover p hh.1, hh.2⟩⟩,
      fun hh => ⟨hh.1, ((image p (vt D₀ hD₀V p hh.1)).mp hh.2).2⟩⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, strength, _, inaccessible, locality⟩ := strong
  -- 合并公式自行检验扩展器并构造超幂，调用端只保留原类型及查询域。
  let ξ (z : M.Domain) : Env M 8 := ⟨Fin.cases z (Fin.cases D₀ (Fin.cases t (Fin.cases F
    (Fin.cases X (Fin.cases L (Fin.cases κ (fun _ => ω))))))), fun _ => t⟩
  have read (z : M.Domain) := (et_quality_sat_l hZFC (ξ z)
    (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
    source hX hθ hκL hn hB constants pool (fun p hp => ((type p).mp hp).1)).trans
    (show (_ ∧ _ ∧ _ ∧ Et_stretch_d hZF ω κ L F X R t D₀ z) ↔ Et_stretch_d hZF ω κ L F X R t D₀ z from
      ⟨fun h => h.2.2.2, fun h => ⟨locality, inaccessible, strength, h⟩⟩)
  exact ⟨L, K, F, R, V, B₀, U₀, D₀, v, hL, hκL, hτL, hωL, rL, sL, hV, short, source, strength,
    inaccessible, locality, hB₀, constants₀,
    ⟨code.1, hn, hs, hθZ, fun x hx => hXZ x (hVX x (vt U₀ hU₀V x hx)), pool₀, type₀⟩,
    ⟨b, d, N, S, i, t', hm, hm', ultra, htt, projection⟩, read⟩

/-- Neeman 3.22：任意内部有限元组在 V(η+1) 的完整 κ 型，对无界多个 κ 弹性。
    四查询及其统一读取证书一并给出；原类型和前驱类型使用同一编译语言。 -/
theorem woodin_elastic_l (hZFC : M.Models ZFC) {θ η : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) θ)
    (hη : M.IsOrdinal η) (hθη : M.mem θ η) :
    let hZF := ZFC.models_zf_l hZFC
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω X Z μ W c Q d S, M.IsOmega ω ∧ V_d I θ X ∧ V_d I η Z ∧
      M.SuccessorOf μ η ∧ V_d I μ W ∧ Smem_d I c Z Q ∧ Smem_d I d W S ∧
      ∀ n s, M.mem n ω → Fn0_d n Z s → ∀ α, M.mem α θ →
        ∃ κ K R B U D, ∃ q : Ee_queries_d M, ∃ t u,
          M.mem α κ ∧ M.mem κ θ ∧ M.IsLimitOrdinal κ ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R ∧
          Ee_language_d hZF ω κ n B U D q ∧ Tt_realized_d I ω c Z Q n s θ U D t ∧
          Tt_realized_d I ω d W S n s θ U D u ∧ Ee_minus_d I ω D q u t ∧ Ee_elastic_d q u := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, X, Z, μ, W, c, Q, d, S, hω, hX, hZ, hμ, hW, hc, upper, all⟩ := woodin_type_stretch_l hZFC hd hη hθη
  obtain ⟨ω₀, _, hω₀, above, regular, strong, _⟩ := hd
  have eqω := hZF.1.eq_of_same_members ω₀ ω (fun x => ⟨hω₀.2 ω hω.1 x, hω.2 ω₀ hω₀.1 x⟩)
  subst ω₀
  have inacc := sc_v_inaccessible_l hZF hW (ZF.v_ordinal_mem_l I hZF hW ((hμ θ).mpr (Or.inl hθη))) above regular strong
  refine ⟨ω, X, Z, μ, W, c, Q, d, S, hω, hX, hZ, hμ, hW, hc, upper, fun n s hn hs α hα => ?_⟩
  obtain ⟨κ, B, U, D, t, u, bound, hk, hB, constants, lower, lifted, minus, _, steps⟩ := all n s hn hs α hα
  obtain ⟨_, K, _, R, _, _, _, _, _, _, _, _, _, _, _, _, short, source, _⟩ := steps α hα
  have limit := ZF.infiniteCardinal_isLimitOrdinal hZF I hω (ZF.omega_cardinal_l I hZF hω)
    ⟨short.critical, ZF.exists_inclusionInjection hZF I (short.critical.1.transitive ω short.uncountable)⟩
  obtain ⟨B', U', D', q, language⟩ := ee_definition_l hZF hω hn limit
  have eb := ZF.v_unique_l I hZF language.rank hB
  subst B'
  have eu := hZF.1.eq_of_same_members U' U (fun x => (language.constants x).trans (constants x).symm)
  subst U'
  have ed := language.pool.unique_l hZF.1 I lower.pool
  subst D'
  have allτ : ∀ τ, M.mem τ θ → Ee_step_d hZF ω κ θ n s c X R t τ := by
    intro τ hτ
    obtain ⟨L, _, F, R', _, B', U', D', v, hl, hκL, hτL, _, _, _, _, _, source', strength,
      inacc, loc, hB', constants', type, stretch, _⟩ := steps τ hτ
    obtain ⟨b, hb⟩ := source.code
    obtain ⟨b', hb'⟩ := source'.code
    have eqR := (smem_unique_l I hZF.1 hb' hb).2
    exact ⟨L, F, B', U', D', v, hl, hκL, hτL, hB', constants', type.pool, type.truth,
      eqR ▸ loc, inacc, strength, eqR ▸ stretch⟩
  have elastic : Ee_elastic_d q u := (language.read hZFC η μ Z W X d S θ K R s u
    hZ hW hμ hX regular.isLimitOrdinal above hk source upper lifted).mpr ⟨inacc, c, Q, t, hc, minus, lower, allτ⟩
  exact ⟨κ, K, R, B, U, D, q, t, u, bound, hk, limit, source, language, lower, lifted, ⟨elastic.1, minus⟩, elastic⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 武丁基数实际产生弹性 dcp 的游戏类型

在任意给定内部有限历史后添加实现高度；完整新类型的 dcp 字面等于
武丁工厂产生的弹性类型。参数域仍可超过任意给定下界。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem woodin_game_type_l (hZFC : M.Models ZFC) {δ η : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hη : M.IsOrdinal η) (hδη : M.mem δ η) :
    let hZF := ZFC.models_zf_l hZFC
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω Z μ Y c R, M.IsOmega ω ∧ V_d I η Z ∧ M.SuccessorOf μ η ∧ V_d I μ Y ∧ Smem_d I c Y R ∧
      ∀ l s, M.mem l ω → Fn0_d l Z s → ∀ χ, M.mem χ δ →
        ∃ n κ B U D P r t v p, ∃ q : Ee_queries_d M,
          M.SuccessorOf n l ∧ M.mem χ κ ∧ M.mem κ δ ∧ Ee_language_d hZF ω κ l B U D q ∧
          Tt_realized_d I ω c Y R n r δ U P t ∧ Td_dcp_d I l n D t v ∧ Ee_elastic_d q v ∧
          Tg_elastic_d I l n D q t ∧
          (∀ i x, M.mem i l → (Rd_entry_d i x r ↔ Rd_entry_d i x s)) ∧ Rd_entry_d l η r ∧
          Tg_max_query_d I ω l n U P p ∧ M.mem p t := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, X, Z, μ, Y, b, H, c, R, hω, _, hZ, hμ, hY, _, model, all⟩ := woodin_elastic_l hZFC hd hη hδη
  refine ⟨ω, Z, μ, Y, c, R, hω, hZ, hμ, hY, model, fun l s hl fs χ hχ => ?_⟩
  obtain ⟨κ, K, S, B, U, D, q, w, v, above, hk, _, _, language, _, prefixType, _, elastic⟩ := all l s hl fs χ hχ
  obtain ⟨n, hn, _⟩ := hω.1.2 l hl
  obtain ⟨P, pool⟩ := tt_pool_exists_l I hZF hω n U
  obtain ⟨r, t, type, drop, kept, last⟩ := prefixType.append_l hZF hω hn
    (ZF.v_ordinal_mem_l I hZF hY hμ.predecessor_mem) pool
  obtain ⟨p, code⟩ := tt_max_query_l hZF hω hn.predecessor_mem pool
  exact ⟨n, κ, B, U, D, P, r, t, v, p, q, hn, above, hk, language, type, drop, elastic,
    ⟨v, drop, elastic⟩, kept, last, code, (code.2 μ Y c R r δ t η hY model type last).mpr hμ⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 无界参数域的实际弹性重置类型

用武丁无界弹性构造 dcp，再实际添加高度对象。完整节点、空根、
最大序数与 dcp 弹性同时成立，故重置构造已接入规则 (3)、(5)。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem woodin_game_reset_l (hZFC : M.Models ZFC) {δ η B S e : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hB : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) η B) (hδη : M.mem δ η)
    (hS : M.mem S B) (he : ∀ x, ¬ M.mem x e) (root : M.mem e S) :
    let hZF := ZFC.models_zf_l hZFC
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω l μ Y c R, M.IsOmega ω ∧ M.SuccessorOf l e ∧ M.SuccessorOf μ η ∧ V_d I μ Y ∧ Smem_d I c Y R ∧
      ∀ χ, M.mem χ δ → ∃ n κ C U D P r t p₀ p₁ p₂, ∃ q : Ee_queries_d M,
        M.SuccessorOf n l ∧ M.mem χ κ ∧ M.mem κ δ ∧ Ee_language_d hZF ω κ l C U D q ∧
        Tt_realized_d I ω c Y R n r δ U P t ∧ Tg_elastic_d I l n D q t ∧ Rd_entry_d e S r ∧ Rd_entry_d l η r ∧
        Tg_node_query_d I ω e n l U P e e e p₀ ∧ M.mem p₀ t ∧
        Tg_root_query_d I ω e n U P p₁ ∧ M.mem p₁ t ∧ Tg_max_query_d I ω l n U P p₂ ∧ M.mem p₂ t := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, Z, μ, Y, c, R, hω, hZ, hμ, hY, model, all⟩ := woodin_game_type_l hZFC hd (v_ordinal_l I hB) hδη
  have eqB := ZF.v_unique_l I hZF hB hZ
  subst Z
  obtain ⟨e', he', heω⟩ := hω.1.1
  have eqe := hZF.1.eq_of_same_members e' e (fun x => iff_of_false (he' x) (he x))
  subst e'
  obtain ⟨l, hl, hlω⟩ := hω.1.2 e heω
  have zero := tg_graph_empty_l I he
  have empty : M.IsSetFunctionFromTo I e e B := ⟨zero.1, zero.2, fun i hi => (he i hi).elim⟩
  obtain ⟨s, fs, _, first⟩ := tt_column_append_l hZF (hω.members_areOrdinals (ZF.modelsKP hZF) e heω) hl empty hS
  refine ⟨ω, l, μ, Y, c, R, hω, hl, hμ, hY, model, fun χ hχ => ?_⟩
  obtain ⟨n, κ, C, U, D, P, r, t, v, p₂, q, hn, above, hk, language, type, _, _, elastic, kept, last, maxCode, maxTrue⟩ :=
    all l s hlω (fn0_of_function_l (ZF.modelsKP hZF) fs) χ hχ
  have first' := (kept e S hl.predecessor_mem).mpr first
  have heU := (tt_constants_finite_l hZF hω heω language.limit language.rank language.constants).2
  have hen := (hn e).mpr (Or.inl hl.predecessor_mem)
  obtain ⟨p₀, nodeCode⟩ := tt_node_query_l hZF hω type.finite hn.predecessor_mem hl.predecessor_mem type.pool heU heU heU
  obtain ⟨p₁, rootCode⟩ := tt_root_query_l hZF hω he hen type.pool
  have set : Sg_set_d I e l r e := by
    intro x
    refine iff_of_false (he x) ?_
    rintro ⟨i, hi, ne, _⟩
    exact ((hl i).mp hi).elim (he i) (fun eq => ne (hZF.1.eq_of_same_members i e eq))
  refine ⟨n, κ, C, U, D, P, r, t, p₀, p₁, p₂, q, hn, above, hk, language, type, elastic, first', last,
    nodeCode, ?_, rootCode, ?_, maxCode, maxTrue⟩
  · exact (nodeCode.2 c Y R r δ t S model (v_transitive_l I hY) type first').mpr
      ⟨e, type.constants e heU, set, (tg_node_empty_l I hZF.1 he).mpr root⟩
  · exact (rootCode.2 c Y R r δ t S model (v_transitive_l I hY) type first').mpr root

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 武丁基数下的一步伸展实例

对任意 Vη 中的内部有限元组，在 V(η+3) 与 V(η+1) 先后选择弹性类型。
低处类型的域严格大于高处类型的域，故实际超过高处类型；一步引理因此
生成同一原类型的真实扩展器伸展。所有实现高度及元组均显式保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 在任意给定 α<δ 之上构造两个弹性类型及其一步伸展，保持原元组。 -/
theorem woodin_elastic_step_l {δ η : M.Domain} (hd : Woodin_d I δ)
    (hη : M.IsOrdinal η) (hδη : M.mem δ η) :
    ∃ ω Z η₁ η₂ η₃ Y₁ Y₃ c₁ R₁ c₃ R₃,
      M.IsOmega ω ∧ V_d I η Z ∧ M.SuccessorOf η₁ η ∧ M.SuccessorOf η₂ η₁ ∧ M.SuccessorOf η₃ η₂ ∧
      V_d I η₁ Y₁ ∧ V_d I η₃ Y₃ ∧ Smem_d I c₁ Y₁ R₁ ∧ Smem_d I c₃ Y₃ R₃ ∧
      ∀ n s, M.mem n ω → Fn0_d n Z s →
        ∃ b σ a z, Ts_program_d hZF ω n b σ a z ∧ ∀ α, M.mem α δ →
        ∃ κ τ B U D u C V W w, ∃ q p : Ee_queries_d M,
          M.mem α κ ∧ M.mem κ τ ∧ M.mem τ δ ∧
          Ee_language_d hZF ω κ n B U D q ∧ Ee_language_d hZF ω τ n C V W p ∧
          Tt_realized_d I ω c₃ Y₃ R₃ n s δ U D u ∧ Tt_realized_d I ω c₁ Y₁ R₁ n s δ V W w ∧
          Ee_elastic_d q u ∧ Ee_elastic_d p w ∧ Tx_exceeds_d hZF ω δ κ n U D u τ n V W w ∧
          Ee_one_step_d hZF ω κ δ n u τ n w b σ z := by
  obtain ⟨ω, _, Z, η₁, Y₁, _, _, c₁, R₁, hω, _, hZ, h₁, hY₁, _, lower, low⟩ :=
    woodin_elastic_l hZFC hd hη hδη
  obtain ⟨η₂, hη₂, h₂⟩ := KP.ordinal_successor_l (ZF.modelsKP hZF)
    (KP.successor_isOrdinal (ZF.modelsKP hZF) hη h₁)
  have hηη₂ := hη₂.transitive η₁ h₂.predecessor_mem η h₁.predecessor_mem
  obtain ⟨ω', _, Z₂, η₃, Y₃, _, _, c₃, R₃, hω', _, hZ₂, h₃, hY₃, _, upper, high⟩ :=
    woodin_elastic_l hZFC hd hη₂ (hη₂.transitive η hηη₂ δ hδη)
  have eqω := hZF.1.eq_of_same_members ω' ω (fun x => ⟨hω'.2 ω hω.1 x, hω.2 ω' hω'.1 x⟩)
  subst ω'
  have sub := ZF.v_mono_l I hZF hZ hZ₂ (hη₂.transitive η hηη₂)
  refine ⟨ω, Z, η₁, η₂, η₃, Y₁, Y₃, c₁, R₁, c₃, R₃, hω, hZ, h₁, h₂, h₃, hY₁, hY₃,
    lower, upper, fun n s hn hs => ?_⟩
  -- 子类型程序先固定；随后全部临界点、类型和扩展器共用这份代码。
  obtain ⟨b, σ, a, z, prog⟩ := ts_program_l hZF hω hn
  refine ⟨b, σ, a, z, prog, fun α hα => ?_⟩
  have lifted := hs.mono_target_l sub
  obtain ⟨κ, _, _, B, U, D, q, _, u, hακ, hκδ, _, _, language, _, hu, _, elastic⟩ :=
    high n s hn lifted α hα
  obtain ⟨τ, _, _, C, V, W, p, _, w, hκτ, hτδ, hτ, _, language', _, hw, _, elastic'⟩ :=
    low n s hn hs κ hκδ
  have exceeds := tx_exceeds_same_l hZF hω hκτ hY₃ upper hu hY₁ lower hw h₂ h₃.predecessor_mem
  exact ⟨κ, τ, B, U, D, u, C, V, W, w, q, p, hακ, hκτ, hτδ, language, language', hu, hw,
    elastic, elastic', exceeds, ee_one_step_l hZFC hω prog language hτ hτδ language'.rank language'.constants elastic exceeds⟩

end YesMetaZFC.SetTheory.LargeCardinal
