import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Tuple
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyDescent
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinTypeStep
import YesMetaZFC.Model.SetTheory.Types.SubtypeInsertion
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.Model.SetTheory.Types.ExceedsSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.CatalogRead
import YesMetaZFC.SetTheory.LargeCardinal.Types.OneStep
import YesMetaZFC.SetTheory.CumulativeFinite
import YesMetaZFC.Model.Forcing.Ground.TreeShift

/-! # 四元组代码的实际地模型像

只搬运三次真实配对，既不选择新代码坐标，也不读取任一游戏的类型语义。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (e : M.Domain → N.Domain)
  (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
include he

theorem rd_quad_image_l {q a k t g : M.Domain} (code : Rd_quad_d q a k t g) :
    Rd_quad_d (e q) (e a) (e k) (e t) (e g) := by
  obtain ⟨v, vg, w, kw, aw⟩ := code
  exact ⟨e v, image_kpair_l e he vg, e w, image_kpair_l e he kw, image_kpair_l e he aw⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 泛型 I 方向的无界继续类型

反例分支给出下一枚真实标签。原树的严格秩界使所有标签留在 Vβ，武丁工厂
随即产生任意高参数域的弹性类型；交换末两位的实际排列证明它超过原回答。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem woodin_game_continue_l {ω δ e l n τ U D w η Y c R r S g β s t g' x χ : M.Domain}
    (hd : Woodin_d I δ) (hω : M.IsOmega ω) (hel : M.mem e l) (hn : M.SuccessorOf n l)
    (hτ : M.IsOrdinal τ) (hτχ : M.MemberSubset τ χ) (hχ : M.mem χ δ)
    (hY : V_d I η Y) (model : Smem_d I c Y R) (type : Tt_realized_d I ω c Y R n r δ U D w)
    (rS : Rd_entry_d e S r) (last : Rd_entry_d l β r) (set : Sg_set_d I e l r g)
    (bound : Tg_bound_d I δ S β) (height : Tg_height_d β η)
    (node : Tg_node_d I l S s t g') (extend : ∀ a, M.mem a g' ↔ M.mem a g ∨ a = x) :
    ∃ μ A d H κ B V E P m r' u, ∃ q : Ee_queries_d M,
      M.SuccessorOf μ β ∧ V_d I μ A ∧ Smem_d I d A H ∧ M.mem χ κ ∧ M.mem κ δ ∧
      Ee_language_d hZF ω κ n B V E q ∧ M.SuccessorOf m n ∧
      Tt_realized_d I ω d A H m r' δ V P u ∧ Tg_elastic_d I n m E q u ∧
      Rd_entry_d e S r' ∧ Rd_entry_d l x r' ∧ Rd_entry_d n β r' ∧ Sg_set_d I e n r' g' ∧
      Tx_exceeds_d hZF ω δ τ n U D w κ m V P u := by
  obtain ⟨Z, hZ, hS⟩ := bound.2.2
  obtain ⟨ω', Z', μ, A, d, H, hw, hZ', hμ, hA, lower, all⟩ := woodin_game_type_l hZFC hd bound.1 bound.2.1
  have eqω := hZF.1.eq_of_same_members ω' ω (fun i => ⟨hw.2 ω hω.1 i, hω.2 ω' hw.1 i⟩)
  subst ω'
  have eqZ := ZF.v_unique_l I hZF hZ' hZ
  subst Z'
  have labels := node.labels_rank_l hZF hZ hS
  obtain ⟨a, cut⟩ := ZF.exists_restriction hZF I r l
  have fa := cut.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) type.tuple)
    (fun i hi => (hn i).mpr (Or.inl hi))
  have small : M.IsSetFunctionFromTo I a l Z := ⟨fa.1, fa.2.1, fun i hi => by
    obtain ⟨y, _, iy⟩ := fa.2.2 i hi
    have ry := ((cut.2 i y).mp iy).2
    refine ⟨y, ?_, iy⟩
    by_cases eq : i = e
    · exact ((fn0_function_l (ZF.modelsKP hZF) type.tuple).1.2 e y S (eq ▸ ry) rS).symm ▸ hS
    · exact labels y ((extend y).mpr (Or.inl ((set y).mpr ⟨i, hi, eq, ry⟩)))⟩
  have on := hω.members_areOrdinals (ZF.modelsKP hZF) n type.finite
  obtain ⟨b, fb, kept, bx⟩ := tt_column_append_l hZF (on.mem hn.predecessor_mem) hn small
    (labels x ((extend x).mpr (Or.inr rfl)))
  obtain ⟨m, κ, B, V, E, P, r', u, v, p, q, hm, above, hk, language, full, _, _, elastic, keep, rb, _, _⟩ :=
    all n b type.finite (fn0_of_function_l (ZF.modelsKP hZF) fb) χ hχ
  have agree i y (hi : M.mem i l) : Rd_entry_d i y r ↔ Rd_entry_d i y r' :=
    (show Rd_entry_d i y r ↔ Rd_entry_d i y a from
      ⟨fun h => (cut.2 i y).mpr ⟨hi, h⟩, fun h => ((cut.2 i y).mp h).2⟩).trans
      ((kept i y hi).symm.trans (keep i y (on.transitive l hn.predecessor_mem i hi)).symm)
  have rx := (keep l x hn.predecessor_mem).mpr bx
  have nextSet : Sg_set_d I e n r' g' := by
    intro y
    constructor
    · intro hy
      rcases (extend y).mp hy with hy | eq
      · obtain ⟨i, hi, ne, iy⟩ := (set y).mp hy
        exact ⟨i, on.transitive l hn.predecessor_mem i hi, ne, (agree i y hi).mp iy⟩
      · exact ⟨l, hn.predecessor_mem, fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) l (eq.symm ▸ hel), eq.symm ▸ rx⟩
    · rintro ⟨i, hi, ne, iy⟩
      apply (extend y).mpr
      rcases (hn i).mp hi with hi | eq
      · exact Or.inl ((set y).mpr ⟨i, hi, ne, (agree i y hi).mpr iy⟩)
      · exact Or.inr ((fn0_function_l (ZF.modelsKP hZF) full.tuple).1.2 l y x
          (hZF.1.eq_of_same_members i l eq ▸ iy) rx)
  obtain ⟨μ', γ, succ, mid, top⟩ := height
  have eqμ := succ.eq hZF.1 hμ
  subst μ'
  have hγ : M.mem γ η := top.predecessor_mem
  exact ⟨μ, A, d, H, κ, B, V, E, P, m, r', u, q, hμ, hA, lower, above, hk, language, hm, full, elastic,
    (agree e S hel).mp rS, rx, rb, nextSet,
    ordinal_down_l (ZF.modelsKP hZF) hτ language.limit.1 hτχ above,
    fun i hi => (hm i).mpr (Or.inl hi), η, Y, c, R, r, hY, model, type, μ, γ, mid, hγ,
    ts_at_insert_l hZF hω hn hm hA lower full
      ⟨(fn0_function_l (ZF.modelsKP hZF) type.tuple).1, (fn0_function_l (ZF.modelsKP hZF) type.tuple).2.1⟩
      agree last rx rb⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 继续请求在全部后续合适局面中的实际合法性

同一个请求先由反例分支和武丁工厂构造，再接入原固定查询表。只要后续局面
保留原轮、实数前缀相符且前一个参数域低于新 κ，原规则 (2)–(6) 全部成立。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_setup_d.generic_continue_l {p : Tg_params_d M.Domain}
    {X ℓ a₀ ℓ₀ t₀ κ₀ u₀ b₀ j k N τ B U D w η Y c R r g β s t g' x χ Z : M.Domain}
    {q₀ : Tg_reply_queries_d M}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d I p.δ) (hℓ : M.mem ℓ p.ω)
    (oldMove : Tg_aux_data_d a₀ ℓ₀ t₀ κ₀ u₀) (oldAnswer : KPair_d M b₀ τ w)
    (ft₀ : Fn0_d j p.ω t₀) (hk : M.SuccessorOf k j) (hN : M.SuccessorOf N k)
    (ft : Fn0_d k p.ω t) (cut : M.IsRestrictionOf I t₀ t j)
    (oldLanguage : Tg_reply_language_d hZF p.ω p.e k N τ B U D q₀)
    (hY : V_d I η Y) (model : Smem_d I c Y R) (type : Tt_realized_d I p.ω c Y R N r p.δ U D w)
    (rS : Rd_entry_d p.e p.S r) (last : Rd_entry_d k β r) (set : Sg_set_d I p.e k r g)
    (bound : Tg_bound_d I p.δ p.S β) (height : Tg_height_d β η)
    (node : Tg_node_d I k p.S s t g') (extend : ∀ a, M.mem a g' ↔ M.mem a g ∨ a = x)
    (hχ : M.mem χ p.δ) (hτχ : M.MemberSubset τ χ) (hZ : V_d I χ Z) (hs : M.mem s Z) (ht : M.mem t Z) :
    ∃ κ C a u μ A d H m V P r', M.mem χ κ ∧ M.mem κ p.δ ∧ V_d I κ C ∧ M.mem a X ∧ Tg_aux_data_d a ℓ t κ u ∧
      M.SuccessorOf μ β ∧ V_d I μ A ∧ Smem_d I d A H ∧ M.SuccessorOf m N ∧ (∀ x, M.mem x V ↔ M.mem x C ∨ x = κ) ∧
      Tt_realized_d I p.ω d A H m r' p.δ V P u ∧ Rd_entry_d p.e p.S r' ∧ Rd_entry_d N β r' ∧ Sg_set_d I p.e N r' g' ∧
      ∀ n h z, Tg_digits_d hZF p.c p.b n p.A h z → M.IsRestrictionOf I s z k → M.mem ℓ n →
        Tg_event_d I p.c ℓ p.e h a₀ → Tg_event_d I p.c ℓ p.a h b₀ →
        Tg_growth_d hZF p.e p.c p.A n h κ C → Tg_aux_d hZF p n h a := by
  have hnω := type.finite
  have hkω := setup.omega.transitive (ZF.modelsKP hZF) N hnω k hN.predecessor_mem
  have hel := (setup.omega.members_areOrdinals (ZF.modelsKP hZF) k hkω).empty_mem_of_nonempty
    (ZF.modelsKP hZF) ⟨j, hk.predecessor_mem⟩ setup.empty
  obtain ⟨μ, A, d, H, κ, C, V, E, P, m, r', u, q, hμ, hA, lower, above, hκ, language, hm,
    full, elastic, root, _, last', nextSet, exceeds⟩ := woodin_game_continue_l hZFC hd setup.omega hel hN
      oldLanguage.limit.1 hτχ hχ hY model type rS last set bound height node extend
  -- 查询表使用自己的实际编译结果；只通过完整类型的语义转移弹性。
  obtain ⟨C', V', E', q', data, target⟩ := setup.elastic.elim fun _ table =>
    table.get_l hZFC hκ hnω language.limit
  have eqC := ZF.v_unique_l I hZF target.rank language.rank
  subst C'
  have eqV := hZF.1.eq_of_same_members V' V (fun a => (target.constants a).trans (language.constants a).symm)
  subst V'
  have eqE := target.pool.unique_l hZF.1 I language.pool
  subst E'
  obtain ⟨v, drop, elastic⟩ := elastic
  obtain ⟨r₀, v₀, _, drop₀, prefixType⟩ := full.dcp_l hZF setup.omega hm language.pool
  have eqv := drop₀.unique_l I hZF.1 drop
  subst v₀
  have elastic' : Tg_elastic_d I N m E q' u :=
    ⟨v, drop, language.elastic_transfer_l hZFC target setup.omega hκ hA lower prefixType elastic⟩
  have sub := ZF.v_mono_l I hZF hZ language.rank (language.limit.1.transitive χ above)
  have hsV := (language.constants s).mpr (Or.inl (sub s hs))
  have htV := (language.constants t).mpr (Or.inl (sub t ht))
  have request : Tg_query_request_d hZF p.ω κ k s t :=
    ⟨language.limit, hkω, C, V, language.rank, language.constants, hsV, htV⟩
  obtain ⟨key, row, encoded, entry, N', m', C', V', P', qr, qm, qb, qh, qn, pack, tail,
    hN', hm', rowCode, packCode, tailCode, query, _, nodeQuery, _⟩ :=
    setup.queries.get_l hZFC setup.limit setup.above setup.rank hκ request
  have eqN := hN'.eq hZF.1 hN
  subst N'
  have eqm := hm'.eq hZF.1 hm
  subst m'
  have eqC := ZF.v_unique_l I hZF query.rank language.rank
  subst C'
  have eqV := hZF.1.eq_of_same_members V' V (fun a => (query.constants a).trans (language.constants a).symm)
  subst V'
  have eqP := query.pool.unique_l hZF.1 I full.pool
  subst P'
  have queryData : Tg_query_data_d p.Q κ k s t C V P qr qm qb qh qn :=
    ⟨key, row, pack, tail, encoded, entry, rowCode, packCode, tailCode⟩
  obtain ⟨Zβ, hZβ, hSβ⟩ := bound.2.2
  have hg'A := (ZF.v_unfold_l I hZF hA g').mpr ⟨β, Zβ, hμ.predecessor_mem, hZβ, node.labels_rank_l hZF hZβ hSβ⟩
  have truth := (nodeQuery.2 d A H r' p.δ u p.S lower (v_transitive_l I hA) full root).mpr
    ⟨g', hg'A, nextSet, node⟩
  -- 新请求本身属于原 Vδ，故能在坍缩枚举中找到它，而非额外加入字母表。
  have algebra := sc_v_algebra_l hZFC setup.limit setup.rank
  have tr := v_transitive_l I setup.rank
  have hwX := ZF.v_ordinal_mem_l I hZF setup.rank setup.above
  have hVX := tt_constants_rank_l hZF setup.rank setup.limit hκ language.rank language.constants
  have hPX := full.pool.rank_mem_l (ZF.modelsKP hZF) setup.omega setup.rank setup.limit hwX full.finite hVX
  have uu : M.MemberSubset u P := fun a ha => ((full.truth a).mp ha).1
  have huX := v_subset_mem_l I setup.rank hPX uu
  obtain ⟨v₁, hv₁, cv₁⟩ := algebra.kpair_l (ZF.v_ordinal_mem_l I hZF setup.rank hκ) huX
  obtain ⟨v₂, hv₂, cv₂⟩ := algebra.kpair_l (tr V hVX t htV) hv₁
  obtain ⟨a, ha, ca⟩ := algebra.kpair_l (tr p.ω hwX ℓ hℓ) hv₂
  have move : Tg_aux_data_d a ℓ t κ u := ⟨v₁, ⟨v₂, cv₂, ca⟩, cv₁⟩
  have nonempty : t ≠ p.e := by
    intro eq
    obtain ⟨y, _, v, _, hv⟩ := ft.2.1 j hk.predecessor_mem
    exact setup.empty v (eq ▸ hv)
  refine ⟨κ, C, a, u, μ, A, d, H, m, V, P, r', above, hκ, language.rank, ha, move,
    hμ, hA, lower, hm, language.constants, full, root, last', nextSet, fun n h z digits real hℓn old₀ old₁ growth => ?_⟩
  exact ⟨ℓ, t, κ, u, k, N, m, z, s, C, V, P, qr, qm, qb, qh, qn, C, V, E,
    q'.largest, q'.domain, q'.inaccessible, q'.stretch,
    move, hκ, ft, hN, hm, digits, real, request, queryData, uu, data, elastic', truth, growth,
    Or.inr ⟨nonempty, hℓn, a₀, b₀, ℓ₀, t₀, κ₀, u₀, τ, w, j, k, N, B, U, D,
      old₀, oldMove, old₁, oldAnswer, ft₀, hk, cut, hk, hN, oldLanguage.limit,
      oldLanguage.rank, oldLanguage.constants, oldLanguage.pool, exceeds⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限坍缩条件中强制出现可继续请求

任意给定内部有限条件先延长至指定编号之后，再统一界定已有值与节点参数的秩。
武丁继续工厂给出更高 κ；把同一个合法请求追加到条件末尾，所有较早值均在 Vκ。
这里保留请求的实际完整类型及其实现高度，供下一次严格下降使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_setup_d.generic_dense_l {p : Tg_params_d M.Domain}
    {X ℓ a₀ ℓ₀ t₀ κ₀ u₀ b₀ j k N τ B U D w η Y c R r g β s t g' x F f E : M.Domain}
    {q₀ : Tg_reply_queries_d M}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d I p.δ) (hℓ : M.mem ℓ p.ω)
    (oldMove : Tg_aux_data_d a₀ ℓ₀ t₀ κ₀ u₀) (oldAnswer : KPair_d M b₀ τ w)
    (ft₀ : Fn0_d j p.ω t₀) (hk : M.SuccessorOf k j) (hN : M.SuccessorOf N k)
    (ft : Fn0_d k p.ω t) (cut : M.IsRestrictionOf I t₀ t j)
    (oldLanguage : Tg_reply_language_d hZF p.ω p.e k N τ B U D q₀)
    (hY : V_d I η Y) (model : Smem_d I c Y R) (type : Tt_realized_d I p.ω c Y R N r p.δ U D w)
    (rS : Rd_entry_d p.e p.S r) (last : Rd_entry_d k β r) (set : Sg_set_d I p.e k r g)
    (bound : Tg_bound_d I p.δ p.S β) (height : Tg_height_d β η)
    (node : Tg_node_d I k p.S s t g') (extend : ∀ a, M.mem a g' ↔ M.mem a g ∨ a = x)
    (hτ : M.mem τ p.δ) (hs : M.mem s X) (ht : M.mem t X)
    (space : Fseq_space_d I p.ω X F) (hf : M.mem f F) (hE : M.mem E p.ω) :
    ∃ κ C a u μ A d H m V P r' i q,
      M.mem κ p.δ ∧ V_d I κ C ∧ M.mem a X ∧ Tg_aux_data_d a ℓ t κ u ∧
      M.SuccessorOf μ β ∧ V_d I μ A ∧ Smem_d I d A H ∧ M.SuccessorOf m N ∧ (∀ x, M.mem x V ↔ M.mem x C ∨ x = κ) ∧
      Tt_realized_d I p.ω d A H m r' p.δ V P u ∧ Rd_entry_d p.e p.S r' ∧ Rd_entry_d N β r' ∧ Sg_set_d I p.e N r' g' ∧
      M.mem q F ∧ M.MemberSubset f q ∧ M.mem E i ∧ M.mem i p.ω ∧ Rd_entry_d i a q ∧
      (∀ j y, M.mem j i → Rd_entry_d j y q → M.mem y C) ∧
      ∀ n h z, Tg_digits_d hZF p.c p.b n p.A h z → M.IsRestrictionOf I s z k → M.mem ℓ n →
        Tg_event_d I p.c ℓ p.e h a₀ → Tg_event_d I p.c ℓ p.a h b₀ →
        Tg_growth_d hZF p.e p.c p.A n h κ C → Tg_aux_d hZF p n h a := by
  obtain ⟨n, hn, fn⟩ := (space f).mp hf
  have on := setup.omega.members_areOrdinals (ZF.modelsKP hZF) n hn
  have oE := setup.omega.members_areOrdinals (ZF.modelsKP hZF) E hE
  obtain ⟨E', succ, hE'⟩ := setup.omega.1.2 E hE
  have fit : ∃ i, M.mem i p.ω ∧ M.mem E i ∧ M.MemberSubset n i := by
    rcases on.trichotomy hZF.1 oE (KP.difference_exists_d (ZF.modelsKP hZF))
        (KP.intersection_exists_d (ZF.modelsKP hZF) n E) with eq | lt | gt
    · exact ⟨E', hE', succ.predecessor_mem, fun a ha => (succ a).mpr (Or.inl ((eq a).mp ha))⟩
    · exact ⟨E', hE', succ.predecessor_mem, fun a ha => (succ a).mpr (Or.inl (oE.transitive n lt a ha))⟩
    · exact ⟨n, hn, gt, fun _ ha => ha⟩
  obtain ⟨i, hi, hEi, ni⟩ := fit
  have oi := setup.omega.members_areOrdinals (ZF.modelsKP hZF) i hi
  have hwX := ZF.v_ordinal_mem_l I hZF setup.rank setup.above
  have tr := v_transitive_l I setup.rank
  have heω := num_mem_l hZF.1 setup.omega (show Num_d 0 p.e from setup.empty)
  obtain ⟨b, fill, fb⟩ := senv_fill_exists_l I hZF fn (tr p.ω hwX p.e heω)
  obtain ⟨f₀, restrict⟩ := ZF.exists_restriction hZF I b i
  have ff₀ := restrict.isSetFunctionFromTo fb (setup.omega.transitive (ZF.modelsKP hZF) i hi)
  have kept a y (ay : Rd_entry_d a y f) : Rd_entry_d a y f₀ := by
    have ha := fn.input_mem_of_pairMember ay
    exact (restrict.2 a y).mpr ⟨ni a ha, (fill.2 a y).mpr
      ⟨setup.omega.transitive (ZF.modelsKP hZF) n hn a ha, Or.inl ⟨ha, ay⟩⟩⟩
  obtain ⟨C₀, hC₀, values, _⟩ := ZF.v_finite_function_l hZF setup.omega setup.limit setup.rank hwX hi ff₀
  -- 同时界定整段已有枚举值、两张节点图与旧回答的参数域。
  have algebra := sc_v_algebra_l hZFC setup.limit setup.rank
  obtain ⟨S₀, hS₀, pair₀⟩ := algebra.pair s t hs ht
  obtain ⟨T₀, hT₀, pair₁⟩ := algebra.pair S₀ τ hS₀ (ZF.v_ordinal_mem_l I hZF setup.rank hτ)
  obtain ⟨Z₀, hZ₀, cZ, tZ⟩ := v_joint_bound_l I setup.rank hC₀ hT₀
  obtain ⟨χ, Z, hχ, hZ, zz⟩ := (ZF.v_unfold_l I hZF setup.rank Z₀).mp hZ₀
  have trZ := v_transitive_l I hZ
  have hS₀Z := zz S₀ (tZ S₀ ((pair₁ S₀).mpr (Or.inl rfl)))
  have hτZ := zz τ (tZ τ ((pair₁ τ).mpr (Or.inr rfl)))
  have hτχ := ZF.v_ordinal_height_l hZF hZ oldLanguage.limit.1 hτZ
  obtain ⟨κ, C, a, u, μ, A, d, H, m, V, P, r', above, hκ, hC, ha, move, hμ, hA, lower,
    hm, constants, full, first, last', nextSet, legal⟩ := setup.generic_continue_l hZFC hd hℓ oldMove oldAnswer ft₀ hk hN ft cut
      oldLanguage hY model type rS last set bound height node extend hχ
      ((v_ordinal_l I hZ).transitive τ hτχ) hZ
      (trZ S₀ hS₀Z s ((pair₀ s).mpr (Or.inl rfl))) (trZ S₀ hS₀Z t ((pair₀ t).mpr (Or.inr rfl)))
  obtain ⟨i', si, hi'⟩ := setup.omega.1.2 i hi
  obtain ⟨q, fq, old, last⟩ := tt_column_append_l hZF oi si ff₀ ha
  have sub : M.MemberSubset f q := by
    intro v hv
    obtain ⟨j, y, pair⟩ := fn.1.1 v hv
    have jy : Rd_entry_d j y f := ⟨v, pair, hv⟩
    obtain ⟨v', cp, hv'⟩ := (old j y (ni j (fn.input_mem_of_pairMember jy))).mpr (kept j y jy)
    exact (kpair_unique_l M hZF.1 pair cp).symm ▸ hv'
  have before j y (hj : M.mem j i) (jy : Rd_entry_d j y q) : M.mem y C :=
    ZF.v_mono_l I hZF hZ hC ((v_ordinal_l I hC).transitive χ above) y
      (zz y (cZ y (values.output_mem_of_pairMember ((old j y hj).mp jy))))
  exact ⟨κ, C, a, u, μ, A, d, H, m, V, P, r', i, q, hκ, hC, ha, move, hμ, hA, lower, hm, constants,
    full, first, last', nextSet, (space q).mpr ⟨i', hi', fq⟩, sub, hEi, hi, last, before, legal⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 泛型稠密要求的原公式

请求保留实际实现高度与标签图，并对后续局面给出原规则的合法性。全部要求
均为原语言公式，因而可在地模型内分离，不把外部谓词冒充模型内稠密集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_generic_target_d (p : Tg_params_d M.Domain) (ℓ s t k N β g a₀ b₀ κ C a u : M.Domain) : Prop :=
  M.mem κ p.δ ∧ V_d I κ C ∧ Tg_aux_data_d a ℓ t κ u ∧
  (∃ μ A d H m V P r, M.SuccessorOf μ β ∧ V_d I μ A ∧ Smem_d I d A H ∧ M.SuccessorOf m N ∧
    (∀ x, M.mem x V ↔ M.mem x C ∨ x = κ) ∧
    Tt_realized_d I p.ω d A H m r p.δ V P u ∧ Rd_entry_d p.e p.S r ∧ Rd_entry_d N β r ∧ Sg_set_d I p.e N r g) ∧
  ∀ n h z, Tg_digits_d hZF p.c p.b n p.A h z → M.IsRestrictionOf I s z k → M.mem ℓ n →
    Tg_event_d I p.c ℓ p.e h a₀ → Tg_event_d I p.c ℓ p.a h b₀ →
    Tg_growth_d hZF p.e p.c p.A n h κ C → Tg_aux_d hZF p n h a

def tg_generic_target0_m : Formula 1 25 :=
  let p : Tg_params_d (Term 25) := ⟨.bound 0, .bound 1, .bound 2, .bound 3, .bound 4, .bound 5,
    .bound 6, .bound 7, .bound 8, .bound 9, .bound 10, .bound 11⟩
  let v : Fin 25 → Term 25 := Term.bound
  let aux {d} (ω e a b c δ A S ν E P Q n h v : Term d) := tg_aux_m ⟨ω, e, a, b, c, δ, A, S, ν, E, P, Q⟩ n h v
  set[25] ⟪⌜v 21⌝ₛ ∈ ⌜p.δ⌝ₛ ∧ ⌜v_m kpair_convention_l⌝ₚ(⌜v 21⌝ₛ, ⌜v 22⌝ₛ) ∧
    ⌜tg_aux_data_m⌝ₚ(⌜v 23⌝ₛ, ⌜v 12⌝ₛ, ⌜v 14⌝ₛ, ⌜v 21⌝ₛ, ⌜v 24⌝ₛ) ∧
    (∃ μ A d H m V P r, ⌜Formula.isSuccessor⌝ₚ(μ, ⌜v 17⌝ₛ) ∧ ⌜v_m kpair_convention_l⌝ₚ(μ, A) ∧
      ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(d, A, H) ∧ ⌜Formula.isSuccessor⌝ₚ(m, ⌜v 16⌝ₛ) ∧
      ⌜tt_constants0_m⌝ₚ(⌜v 21⌝ₛ, ⌜v 22⌝ₛ, V) ∧ ⌜tt_realized_m⌝ₚ(⌜p.ω⌝ₛ, d, A, H, m, r, ⌜p.δ⌝ₛ, V, P, ⌜v 24⌝ₛ) ∧
      ⌜rd_entry0_m⌝ₚ(⌜p.e⌝ₛ, ⌜p.S⌝ₛ, r) ∧ ⌜rd_entry0_m⌝ₚ(⌜v 16⌝ₛ, ⌜v 17⌝ₛ, r) ∧
      ⌜sg_set_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p.e⌝ₛ, ⌜v 16⌝ₛ, r, ⌜v 18⌝ₛ)) ∧
    (∀ n h z, ⌜tg_digits_m⌝ₚ(⌜p.c⌝ₛ, ⌜p.b⌝ₛ, n, ⌜p.A⌝ₛ, h, z) →
      ⌜Formula.isRestriction kpair_convention_l⌝ₚ(⌜v 13⌝ₛ, z, ⌜v 15⌝ₛ) → ⌜v 12⌝ₛ ∈ n →
      ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ, ⌜v 12⌝ₛ, ⌜p.e⌝ₛ, h, ⌜v 19⌝ₛ) →
      ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ, ⌜v 12⌝ₛ, ⌜p.a⌝ₛ, h, ⌜v 20⌝ₛ) →
      ⌜tg_growth_m⌝ₚ(⌜p.e⌝ₛ, ⌜p.c⌝ₛ, ⌜p.A⌝ₛ, n, h, ⌜v 21⌝ₛ, ⌜v 22⌝ₛ) →
      ⌜aux⌝ₚ(⌜p.ω⌝ₛ, ⌜p.e⌝ₛ, ⌜p.a⌝ₛ, ⌜p.b⌝ₛ, ⌜p.c⌝ₛ, ⌜p.δ⌝ₛ,
        ⌜p.A⌝ₛ, ⌜p.S⌝ₛ, ⌜p.ν⌝ₛ, ⌜p.E⌝ₛ, ⌜p.P⌝ₛ, ⌜p.Q⌝ₛ, n, h, ⌜v 23⌝ₛ))⟫

theorem tg_generic_target0_closed_l : tg_generic_target0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_generic_target0_m, Definitional.Formula.FreeClosed]
  exact tg_aux_closed_l _ _ _ _ (by simp -implicitDefEqProofs [Tg_params_d.closed_l]) rfl rfl rfl

def tg_generic_target_m {d} (p : Tg_params_d (Term d)) (ℓ s t k N β g a₀ b₀ κ C a u : Term d) : Formula 1 d :=
  tg_generic_target0_m.bind (fun i => [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q,
    ℓ, s, t, k, N, β, g, a₀, b₀, κ, C, a, u].get i)

@[simp] theorem tg_generic_target_closed_l {d} (p : Tg_params_d (Term d)) (ℓ s t k N β g a₀ b₀ κ C a u : Term d)
    (hp : p.closed_l) (hℓ : ℓ.freeSupport = []) (hs : s.freeSupport = []) (ht : t.freeSupport = [])
    (hk : k.freeSupport = []) (hN : N.freeSupport = []) (hβ : β.freeSupport = []) (hg : g.freeSupport = [])
    (h₀ : a₀.freeSupport = []) (h₁ : b₀.freeSupport = []) (hκ : κ.freeSupport = []) (hC : C.freeSupport = [])
    (ha : a.freeSupport = []) (hu : u.freeSupport = []) : (tg_generic_target_m p ℓ s t k N β g a₀ b₀ κ C a u).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_generic_target0_closed_l
  rcases hp with ⟨hω, he, ha', hb, hc, hd, hA, hS, hν, hE, hP, hQ⟩
  simp only [Fin.forall_fin_succ]
  exact ⟨hω, he, ha', hb, hc, hd, hA, hS, hν, hE, hP, hQ,
    hℓ, hs, ht, hk, hN, hβ, hg, h₀, h₁, hκ, hC, ha, hu, fun i => Fin.elim0 i⟩

theorem tg_generic_target_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (ℓ s t k N β g a₀ b₀ κ C a u : Term d) :
    Formula.satisfies ρ (tg_generic_target_m p ℓ s t k N β g a₀ b₀ κ C a u) ↔
      Tg_generic_target_d hZF (p.map_l (fun t => t.eval ρ)) (ℓ.eval ρ) (s.eval ρ) (t.eval ρ) (k.eval ρ)
        (N.eval ρ) (β.eval ρ) (g.eval ρ) (a₀.eval ρ) (b₀.eval ρ) (κ.eval ρ) (C.eval ρ) (a.eval ρ) (u.eval ρ) := by
  simp only [tg_generic_target_m, Formula.satisfies_bind, tg_generic_target0_m, Tg_generic_target_d,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, v_sat_l I hZF.1, tg_aux_data_sat_l hZF.1,
    Formula.satisfies_exists_iff, Formula.satisfies_isSuccessor_iff, smem_sat_l I, tt_constants0_sat_l hZF.1, tt_realized_sat_l I (ZF.modelsKP hZF),
    rd_entry0_sat_l hZF.1, sg_set_sat_l I hZF.1, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    tg_digits_sat_l hZF, Formula.satisfies_isRestriction_iff I, tg_event_sat_l I hZF.1, tg_growth_sat_l hZF,
    tg_aux_sat_l hZF, Definitional.Term.eval_weaken, Tg_params_d.map_l]
  rfl

def Tg_dense_hit_d (p : Tg_params_d M.Domain) (ℓ s t k N β g a₀ b₀ E q : M.Domain) : Prop :=
  ∃ κ C a u i, Tg_generic_target_d hZF p ℓ s t k N β g a₀ b₀ κ C a u ∧
    M.mem E i ∧ M.mem i p.ω ∧ Rd_entry_d i a q ∧ ∀ j y, M.mem j i → Rd_entry_d j y q → M.mem y C

def tg_dense_hit_m {d} (p : Tg_params_d (Term d)) (ℓ s t k N β g a₀ b₀ E q : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (tg_generic_target_m (p.map_l (fun t => t.weaken.weaken.weaken.weaken.weaken))
      ℓ.weaken.weaken.weaken.weaken.weaken s.weaken.weaken.weaken.weaken.weaken t.weaken.weaken.weaken.weaken.weaken
      k.weaken.weaken.weaken.weaken.weaken N.weaken.weaken.weaken.weaken.weaken β.weaken.weaken.weaken.weaken.weaken
      g.weaken.weaken.weaken.weaken.weaken a₀.weaken.weaken.weaken.weaken.weaken b₀.weaken.weaken.weaken.weaken.weaken
      (.bound 4) (.bound 3) (.bound 2) (.bound 1))
    (set[d+5] ⟪⌜E.weaken.weaken.weaken.weaken.weaken⌝ₛ ∈ ⌜(.bound 0 : Term (d+5))⌝ₛ ∧
      ⌜(.bound 0 : Term (d+5))⌝ₛ ∈ ⌜p.ω.weaken.weaken.weaken.weaken.weaken⌝ₛ ∧
      ⌜rd_entry0_m⌝ₚ(⌜(.bound 0 : Term (d+5))⌝ₛ, ⌜(.bound 2 : Term (d+5))⌝ₛ, ⌜q.weaken.weaken.weaken.weaken.weaken⌝ₛ) ∧
      (∀ j y, j ∈ ⌜(.bound 0 : Term (d+5))⌝ₛ →
        ⌜rd_entry0_m⌝ₚ(j, y, ⌜q.weaken.weaken.weaken.weaken.weaken⌝ₛ) → y ∈ ⌜(.bound 3 : Term (d+5))⌝ₛ)⟫))))))

theorem tg_dense_hit_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (ℓ s t k N β g a₀ b₀ E q : Term d) :
    Formula.satisfies ρ (tg_dense_hit_m p ℓ s t k N β g a₀ b₀ E q) ↔
      Tg_dense_hit_d hZF (p.map_l (fun t => t.eval ρ)) (ℓ.eval ρ) (s.eval ρ) (t.eval ρ) (k.eval ρ)
        (N.eval ρ) (β.eval ρ) (g.eval ρ) (a₀.eval ρ) (b₀.eval ρ) (E.eval ρ) (q.eval ρ) := by
  simp only [tg_dense_hit_m, Tg_dense_hit_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tg_generic_target_sat_l hZF, Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Definitional.Term.eval_weaken, Tg_params_d.map_l]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 地模型中的请求实现高度关系

只收集旧请求、旧有限标签图及有界高度；完整类型的实现仍在地模型中求值。
扩张以后读取这个实际集合的像，不能把旧 Vα 当成扩张模型的 Vα。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_level_d (ω e δ S l κ u α g : M.Domain) : Prop := ∃ μ A d H n C V P r,
  M.SuccessorOf μ α ∧ V_d I μ A ∧ Smem_d I d A H ∧ M.SuccessorOf n l ∧ V_d I κ C ∧
  (∀ x, M.mem x V ↔ M.mem x C ∨ x = κ) ∧ Tt_realized_d I ω d A H n r δ V P u ∧
  Rd_entry_d e S r ∧ Rd_entry_d l α r ∧ Sg_set_d I e l r g

def tg_level_m {d} (ω e δ S l κ u α g : Term d) : Formula 1 d := set[d] ⟪∃ μ A d H n C V P r,
  ⌜Formula.isSuccessor⌝ₚ(μ, ⌜α⌝ₛ) ∧ ⌜v_m kpair_convention_l⌝ₚ(μ, A) ∧
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(d, A, H) ∧ ⌜Formula.isSuccessor⌝ₚ(n, ⌜l⌝ₛ) ∧
  ⌜v_m kpair_convention_l⌝ₚ(⌜κ⌝ₛ, C) ∧ ⌜tt_constants0_m⌝ₚ(⌜κ⌝ₛ, C, V) ∧
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, d, A, H, n, r, ⌜δ⌝ₛ, V, P, ⌜u⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, ⌜S⌝ₛ, r) ∧ ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, ⌜α⌝ₛ, r) ∧
  ⌜sg_set_m (𝒞 := kpair_convention_l)⌝ₚ(⌜e⌝ₛ, ⌜l⌝ₛ, r, ⌜g⌝ₛ)⟫
derive_free_closed tg_level_m

theorem tg_level_sat_l {d} (ρ : Env M d) (ω e δ S l κ u α g : Term d) :
    Formula.satisfies ρ (tg_level_m ω e δ S l κ u α g) ↔ Tg_level_d hZF
      (ω.eval ρ) (e.eval ρ) (δ.eval ρ) (S.eval ρ) (l.eval ρ) (κ.eval ρ) (u.eval ρ) (α.eval ρ) (g.eval ρ) := by
  simp only [tg_level_m, Tg_level_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, v_sat_l I hZF.1, smem_sat_l I, tt_constants0_sat_l hZF.1,
    tt_realized_sat_l I (ZF.modelsKP hZF), rd_entry0_sat_l hZF.1, sg_set_sat_l I hZF.1, Definitional.Term.eval_weaken]; rfl

def Tg_level_key_d (p : Tg_params_d M.Domain) (X Z a k t g α : M.Domain) : Prop :=
  M.mem a X ∧ M.mem k p.ω ∧ M.mem t X ∧ M.MemberSubset g Z ∧ (M.mem α p.ν ∨ α = p.ν) ∧
  ∃ ℓ κ u l, Tg_aux_data_d a ℓ t κ u ∧ M.mem κ p.δ ∧ Fn0_d k p.ω t ∧ M.SuccessorOf l k ∧
    Tg_level_d hZF p.ω p.e p.δ p.S l κ u α g

def tg_level_key_m {d} (ω e δ S ν X Z a k t g α : Term d) : Formula 1 d := set[d] ⟪
  ⌜a⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜k⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜t⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜g⌝ₛ ⊆ ⌜Z⌝ₛ ∧ (⌜α⌝ₛ ∈ ⌜ν⌝ₛ ∨ ⌜α⌝ₛ = ⌜ν⌝ₛ) ∧
  (∃ ℓ κ u l, ⌜tg_aux_data_m⌝ₚ(⌜a⌝ₛ, ℓ, ⌜t⌝ₛ, κ, u) ∧ κ ∈ ⌜δ⌝ₛ ∧ ⌜fn0_m⌝ₚ(⌜k⌝ₛ, ⌜ω⌝ₛ, ⌜t⌝ₛ) ∧
    ⌜Formula.isSuccessor⌝ₚ(l, ⌜k⌝ₛ) ∧ ⌜tg_level_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜δ⌝ₛ, ⌜S⌝ₛ, l, κ, u, ⌜α⌝ₛ, ⌜g⌝ₛ))⟫
derive_free_closed tg_level_key_m

theorem tg_level_key_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X Z a k t g α : Term d) :
    Formula.satisfies ρ (tg_level_key_m p.ω p.e p.δ p.S p.ν X Z a k t g α) ↔
      Tg_level_key_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (Z.eval ρ) (a.eval ρ) (k.eval ρ) (t.eval ρ) (g.eval ρ) (α.eval ρ) := by
  simp only [tg_level_key_m, Tg_level_key_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_exists_iff, tg_aux_data_sat_l hZF.1, fn0_sat_l hZF.1, Formula.satisfies_isSuccessor_iff,
    tg_level_sat_l hZF, Definitional.Term.eval_weaken, Tg_params_d.map_l]; rfl

def Tg_level_table_d (p : Tg_params_d M.Domain) (X Z R : M.Domain) : Prop := M.IsSetRelation I R ∧
  ∀ q α, Rd_entry_d q α R ↔ ∃ a k t g, Rd_quad_d q a k t g ∧ Tg_level_key_d hZF p X Z a k t g α

theorem tg_level_table_l (p : Tg_params_d M.Domain) (X Z : M.Domain) : ∃ R, Tg_level_table_d hZF p X Z R := by
  obtain ⟨P, power⟩ := ZF.exists_powerSet hZF Z
  obtain ⟨D₁, prod₁⟩ := ZF.exists_cartesianProduct hZF I X P
  obtain ⟨D₂, prod₂⟩ := ZF.exists_cartesianProduct hZF I p.ω D₁
  obtain ⟨D₃, prod₃⟩ := ZF.exists_cartesianProduct hZF I X D₂
  obtain ⟨ν, succ⟩ := KP.exists_successor (ZF.modelsKP hZF) p.ν
  obtain ⟨C, union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) D₃ ν
  let ρ : Env M 7 := ⟨fun i => [p.ω, p.e, p.δ, p.S, p.ν, X, Z].get i, fun _ => p.ω⟩
  let φ : BinarySchema 7 := { body := set[9] ⟪∃ a k t g,
    ⌜rd_quad_m⌝ₚ(⌜(.bound 1 : Term 9)⌝ₛ, a, k, t, g) ∧
    ⌜tg_level_key_m⌝ₚ(⌜(.bound 2 : Term 9)⌝ₛ, ⌜(.bound 3 : Term 9)⌝ₛ, ⌜(.bound 4 : Term 9)⌝ₛ,
      ⌜(.bound 5 : Term 9)⌝ₛ, ⌜(.bound 6 : Term 9)⌝ₛ, ⌜(.bound 7 : Term 9)⌝ₛ, ⌜(.bound 8 : Term 9)⌝ₛ,
      a, k, t, g, ⌜(.newest : Term 9)⌝ₛ)⟫ }
  have sat q α : φ.denote ρ q α ↔ ∃ a k t g, Rd_quad_d q a k t g ∧ Tg_level_key_d hZF p X Z a k t g α := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_quad_sat_l hZF.1, tg_level_key_m, Tg_level_key_d, Formula.satisfies_mem_iff,
      Formula.satisfies_subset_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
      tg_aux_data_sat_l hZF.1, fn0_sat_l hZF.1, Formula.satisfies_isSuccessor_iff,
      tg_level_sat_l hZF, Definitional.Term.eval_weaken]; rfl
  obtain ⟨R, rel, read⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ C
  refine ⟨R, rel.1, fun q α => (read q α).trans ⟨fun h => (sat q α).mp h.2.2, fun h => ?_⟩⟩
  obtain ⟨a, k, t, g, code, key⟩ := h
  obtain ⟨v, vg, w, kw, aw⟩ := code
  have hq := (prod₃ q).mpr ⟨a, key.1, w, (prod₂ w).mpr ⟨k, key.2.1, v,
    (prod₁ v).mpr ⟨t, key.2.2.1, g, (power g).mpr key.2.2.2.1, vg⟩, kw⟩, aw⟩
  have hα := key.2.2.2.2.1.elim (fun h => (succ α).mpr (Or.inl h)) (fun eq => eq.symm ▸ succ.predecessor_mem)
  exact ⟨(union q).mpr (Or.inl hq), (union α).mpr (Or.inr hα),
    (sat q α).mpr ⟨a, k, t, g, ⟨v, vg, w, kw, aw⟩, key⟩⟩

/-- 稠密工厂的真实实现直接进入旧高度关系。 -/
theorem Tg_generic_target_d.level_l {p : Tg_params_d M.Domain} {ℓ s t k n β g a₀ b₀ κ C a u : M.Domain}
    (h : Tg_generic_target_d hZF p ℓ s t k n β g a₀ b₀ κ C a u) : Tg_level_d hZF p.ω p.e p.δ p.S n κ u β g := by
  obtain ⟨μ, A, d, H, m, V, P, r, hμ, hA, model, hm, constants, full, first, last, labels⟩ := h.2.2.2.1
  exact ⟨μ, A, d, H, m, C, V, P, r, hμ, hA, model, hm, h.2.1, constants, full, first, last, labels⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 已捕获请求的实际有界高度谓词

谓词只读取递归图、枚举图和旧实现关系的像。它是扩张内部的原公式，
可对实际已捕获高度取最小元；反向读取同时恢复同一个地请求和两个旧前缀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} (hM : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)

def Tg_tracked_d (ω H K enum R T G α : M.Domain) : Prop := ∃ n h i a k t g q,
  M.mem n ω ∧ Rd_entry_d n h H ∧ Rd_entry_d h i K ∧ Rd_entry_d i a enum ∧
  Rd_quad_d q a k t g ∧ Rd_entry_d q α R ∧ M.IsRestrictionOf I t T k ∧ M.IsRestrictionOf I g G k

def tg_tracked_m {d} (ω H K enum R T G α : Term d) : Formula 1 d := set[d] ⟪∃ n h i a k t g q,
  n ∈ ⌜ω⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(n, h, ⌜H⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(h, i, ⌜K⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(i, a, ⌜enum⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(q, a, k, t, g) ∧ ⌜rd_entry0_m⌝ₚ(q, ⌜α⌝ₛ, ⌜R⌝ₛ) ∧
  ⌜(Formula.isRestriction kpair_convention_l)⌝ₚ(t, ⌜T⌝ₛ, k) ∧ ⌜(Formula.isRestriction kpair_convention_l)⌝ₚ(g, ⌜G⌝ₛ, k)⟫
derive_free_closed tg_tracked_m

theorem tg_tracked_sat_l {d} (ρ : Env M d) (ω H K enum R T G α : Term d) :
    Formula.satisfies ρ (tg_tracked_m ω H K enum R T G α) ↔ Tg_tracked_d hM
      (ω.eval ρ) (H.eval ρ) (K.eval ρ) (enum.eval ρ) (R.eval ρ) (T.eval ρ) (G.eval ρ) (α.eval ρ) := by
  simp only [tg_tracked_m, Tg_tracked_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rd_entry0_sat_l hM.1, rd_quad_sat_l hM.1,
    Formula.satisfies_isRestriction_iff I, Definitional.Term.eval_weaken]; rfl

variable {N : Structure.{v}} (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Tg_level_table_d.track_l {p : Tg_params_d M.Domain} {X Z R n h a k t g α : M.Domain}
    {H K enum T G i : N.Domain} (table : Tg_level_table_d hM p X Z R)
    (hn : M.mem n p.ω) (nh : Rd_entry_d (e n) (e h) H) (ki : Rd_entry_d (e h) i K) (ia : Rd_entry_d i (e a) enum)
    (key : Tg_level_key_d hM p X Z a k t g α) (rt : N.IsRestrictionOf J (e t) T (e k)) (rg : N.IsRestrictionOf J (e g) G (e k)) :
    Tg_tracked_d hN (e p.ω) H K enum (e R) T G (e α) := by
  obtain ⟨q, code⟩ := rd_quad_exists_l (ZF.modelsKP hM) a k t g
  exact ⟨e n, e h, i, e a, e k, e t, e g, e q, (image_member_l e hi he).mpr hn, nh, ki, ia,
    rd_quad_image_l e he code, (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 q α R).mp
      ((table.2 q α).mpr ⟨a, k, t, g, code, key⟩), rt, rg⟩

omit hi in
theorem Tg_level_table_d.read_tracked_l {p : Tg_params_d M.Domain} {X Z R F : M.Domain}
    {H K enum T G α : N.Domain} (table : Tg_level_table_d hM p X Z R) (hf : Fn0_d (e p.ω) (e F) H)
    (tracked : Tg_tracked_d hN (e p.ω) H K enum (e R) T G α) :
    ∃ n h a k t g β, ∃ i : N.Domain, e β = α ∧ M.mem n p.ω ∧ Rd_entry_d (e n) (e h) H ∧
      Rd_entry_d (e h) i K ∧ Rd_entry_d i (e a) enum ∧ Tg_level_key_d hM p X Z a k t g β ∧
      N.IsRestrictionOf J (e t) T (e k) ∧ N.IsRestrictionOf J (e g) G (e k) := by
  obtain ⟨n, h, i, a, k, t, g, q, hn, nh, ki, ia, code, ent, rt, rg⟩ := tracked
  obtain ⟨n₀, hn₀, en⟩ := (he p.ω n).mp hn; subst n
  obtain ⟨h₀, _, eh⟩ := (he F h).mp (hf.bound_l nh).2; subst h
  obtain ⟨q₀, β, ent₀, eq, eβ⟩ := (image_entries_l e he table.1 q α).mp ent; subst q α
  obtain ⟨a₀, k₀, t₀, g₀, code₀, key⟩ := (table.2 q₀ β).mp ent₀
  obtain ⟨rfl, rfl, rfl, rfl⟩ := (rd_quad_image_l e he code₀).unique_l code
  exact ⟨n₀, h₀, a₀, k₀, t₀, g₀, β, i, rfl, hn₀, nh, ki, ia, key, rt, rg⟩

omit hi he in
/-- 同一严格下降在扩张内部的最小高度上给出矛盾；不额外使用依赖选择。 -/
theorem tg_tracked_min_l {ω H K enum R T G α : M.Domain} (hα : M.IsOrdinal α)
    (initial : Tg_tracked_d hM ω H K enum R T G α) :
    ∃ β, M.IsOrdinal β ∧ Tg_tracked_d hM ω H K enum R T G β ∧
      ∀ γ, M.mem γ β → ¬ Tg_tracked_d hM ω H K enum R T G γ := by
  let ρ : Env M 7 := ⟨fun i => [ω, H, K, enum, R, T, G].get i, fun _ => ω⟩
  let φ : UnarySchema 7 := { body := tg_tracked_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) .newest }
  have sat β : φ.denote ρ β ↔ Tg_tracked_d hM ω H K enum R T G β := tg_tracked_sat_l hM ..
  obtain ⟨β, hβ, state, least⟩ := ZF.ordinal_min_l hM φ ρ hα ((sat α).mpr initial)
  exact ⟨β, hβ, (sat β).mp state, fun γ hγ h => least γ hγ ((sat γ).mpr h)⟩

end YesMetaZFC.SetTheory.LargeCardinal
