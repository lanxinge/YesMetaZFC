import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericExtension
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameSetup
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameCatalogRead
import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticRead

/-! # 继续请求在全部后续合适局面中的实际合法性

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
      M.SuccessorOf μ β ∧ V_d I μ A ∧ Smem_d I d A H ∧ M.SuccessorOf m N ∧
      Tt_realized_d I p.ω d A H m r' p.δ V P u ∧ Rd_entry_d p.e p.S r' ∧ Rd_entry_d N β r' ∧ Sg_set_d I p.e N r' g' ∧
      ∀ n h z, Tg_digits_d hZF p.c p.b n p.A h z → M.IsRestrictionOf I s z k → M.mem ℓ n →
        Tg_event_d I p.c ℓ p.e h a₀ → Tg_event_d I p.c ℓ p.a h b₀ →
        Tg_growth_d hZF p.e p.c p.A n h κ C → Tg_aux_d hZF p n h a := by
  have hnω := type.finite
  have hkω := setup.omega.transitive hZF N hnω k hN.predecessor_mem
  have hel := (setup.omega.members_areOrdinals hZF k hkω).empty_mem_of_nonempty
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
  have truth := (nodeQuery.2 d A H r' p.δ u p.S lower (ZF.v_transitive_l I hZF hA) full root).mpr
    ⟨g', hg'A, nextSet, node⟩
  -- 新请求本身属于原 Vδ，故能在坍缩枚举中找到它，而非额外加入字母表。
  have algebra := sc_v_algebra_l hZFC setup.limit setup.rank
  have tr := ZF.v_transitive_l I hZF setup.rank
  have hwX := ZF.v_ordinal_mem_l I hZF setup.rank setup.above
  have hVX := tt_constants_rank_l hZF setup.rank setup.limit hκ language.rank language.constants
  have hPX := full.pool.rank_mem_l hZF setup.omega setup.rank setup.limit hwX full.finite hVX
  have uu : M.MemberSubset u P := fun a ha => ((full.truth a).mp ha).1
  have huX := ZF.v_subset_mem_l I hZF setup.rank hPX uu
  obtain ⟨v₁, hv₁, cv₁⟩ := algebra.kpair_l (ZF.v_ordinal_mem_l I hZF setup.rank hκ) huX
  obtain ⟨v₂, hv₂, cv₂⟩ := algebra.kpair_l (tr V hVX t htV) hv₁
  obtain ⟨a, ha, ca⟩ := algebra.kpair_l (tr p.ω hwX ℓ hℓ) hv₂
  have move : Tg_aux_data_d a ℓ t κ u := ⟨v₁, ⟨v₂, cv₂, ca⟩, cv₁⟩
  have nonempty : t ≠ p.e := by
    intro eq
    obtain ⟨y, _, v, _, hv⟩ := ft.2.1 j hk.predecessor_mem
    exact setup.empty v (eq ▸ hv)
  refine ⟨κ, C, a, u, μ, A, d, H, m, V, P, r', above, hκ, language.rank, ha, move,
    hμ, hA, lower, hm, full, root, last', nextSet, fun n h z digits real hℓn old₀ old₁ growth => ?_⟩
  exact ⟨ℓ, t, κ, u, k, N, m, z, s, C, V, P, qr, qm, qb, qh, qn, C, V, E,
    q'.largest, q'.domain, q'.inaccessible, q'.stretch,
    move, hκ, ft, hN, hm, digits, real, request, queryData, uu, data, elastic', truth, growth,
    Or.inr ⟨nonempty, hℓn, a₀, b₀, ℓ₀, t₀, κ₀, u₀, τ, w, j, k, N, B, U, D,
      old₀, oldMove, old₁, oldAnswer, ft₀, hk, cut, hk, hN, oldLanguage.limit,
      oldLanguage.rank, oldLanguage.constants, oldLanguage.pool, exceeds⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
