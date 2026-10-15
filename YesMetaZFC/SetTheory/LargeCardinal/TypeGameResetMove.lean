import YesMetaZFC.SetTheory.LargeCardinal.WoodinGameReset
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameSetup
import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticRead

/-! # 任意参数域下界以上的原游戏重置走法

武丁工厂产生完整重置类型，再按实际语义对齐固定查询表。返回原字母表中的
真实走法；任意已有实数历史均可重置，唯一的历史约束就是原参数域增长规则。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_setup_d.reset_move_l {p : Tg_params_d M.Domain} {X χ : M.Domain}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S) (hχ : M.mem χ p.δ) :
    ∃ κ C a u, M.mem χ κ ∧ M.mem κ p.δ ∧ V_d I κ C ∧ M.mem a X ∧ Tg_aux_data_d a p.e p.e κ u ∧
      ∀ n h z, Tg_digits_d hZF p.c p.b n p.A h z →
        Tg_growth_d hZF p.e p.c p.A n h κ C → Tg_aux_d hZF p n h a := by
  have heω := num_mem_l hZF.1 setup.omega (show Num_d 0 p.e from setup.empty)
  obtain ⟨dν, Z, hZ, hSZ⟩ := setup.low.read_l hZF setup.limit.1
  obtain ⟨ω, l, μ, Y, c, R, hw, hl, hμ, hY, model, all⟩ :=
    woodin_game_reset_l hZFC hd hZ dν hSZ setup.empty root
  have eq := hZF.1.eq_of_same_members ω p.ω (fun x =>
    ⟨hw.2 p.ω setup.omega.1 x, setup.omega.2 ω hw.1 x⟩); subst ω
  have eq := hl.eq hZF.1 setup.one; subst l
  obtain ⟨m, κ, C, U, D, P, r, u, q₀, q₁, q₂, q, hm, above, hκ, language, full,
    elastic, first, last, _, _, _, _, _, _⟩ := all χ hχ
  have eq := hm.eq hZF.1 setup.two; subst m
  have haω := setup.omega.transitive hZF p.b full.finite p.a setup.two.predecessor_mem
  obtain ⟨C', U', D', q', data, target⟩ := setup.elastic.elim fun _ table =>
    table.get_l hZFC hκ haω language.limit
  have eq := ZF.v_unique_l I hZF target.rank language.rank; subst C'
  have eq := hZF.1.eq_of_same_members U' U (fun x => (target.constants x).trans (language.constants x).symm); subst U'
  have eq := target.pool.unique_l hZF.1 I language.pool; subst D'
  obtain ⟨v, drop, elastic⟩ := elastic
  obtain ⟨r₀, v₀, _, drop₀, prefixType⟩ := full.dcp_l hZF setup.omega setup.two language.pool
  have eq := drop₀.unique_l I hZF.1 drop; subst v₀
  have elastic' : Tg_elastic_d I p.a p.b D q' u :=
    ⟨v, drop, language.elastic_transfer_l hZFC target setup.omega hκ hY model prefixType elastic⟩
  have heU := (tt_constants_finite_l hZF setup.omega heω language.limit language.rank language.constants).2
  have request : Tg_query_request_d hZF p.ω κ p.e p.e p.e :=
    ⟨language.limit, heω, C, U, language.rank, language.constants, heU, heU⟩
  obtain ⟨key, row, encoded, entry, N, m, C', U', P', qr, qm, qb, qh, qn, pack, tail,
    hN, hm, rowCode, packCode, tailCode, query, _, nodeQuery, _⟩ :=
    setup.queries.get_l hZFC setup.limit setup.above setup.rank hκ request
  have eq := hN.eq hZF.1 setup.one; subst N
  have eq := hm.eq hZF.1 setup.two; subst m
  have eq := ZF.v_unique_l I hZF query.rank language.rank; subst C'
  have eq := hZF.1.eq_of_same_members U' U (fun x => (query.constants x).trans (language.constants x).symm); subst U'
  have eq := query.pool.unique_l hZF.1 I full.pool; subst P'
  have queryData : Tg_query_data_d p.Q κ p.e p.e p.e C U P qr qm qb qh qn :=
    ⟨key, row, pack, tail, encoded, entry, rowCode, packCode, tailCode⟩
  have labels : Sg_set_d I p.e p.a r p.e := by
    intro x
    refine iff_of_false (setup.empty x) ?_
    rintro ⟨i, hi, ne, _⟩
    exact ((setup.one i).mp hi).elim (setup.empty i) (fun eq => ne (hZF.1.eq_of_same_members i p.e eq))
  have truth := (nodeQuery.2 c Y R r p.δ u p.S model (ZF.v_transitive_l I hZF hY) full first).mpr
    ⟨p.e, full.constants p.e heU, labels, (tg_node_empty_l I hZF.1 setup.empty).mpr root⟩
  have algebra := sc_v_algebra_l hZFC setup.limit setup.rank
  have hwX := ZF.v_ordinal_mem_l I hZF setup.rank setup.above
  have heX := ZF.v_transitive_l I hZF setup.rank p.ω hwX p.e heω
  have hUX := tt_constants_rank_l hZF setup.rank setup.limit hκ language.rank language.constants
  have hPX := full.pool.rank_mem_l hZF setup.omega setup.rank setup.limit hwX full.finite hUX
  have sub : M.MemberSubset u P := fun x hx => ((full.truth x).mp hx).1
  obtain ⟨v₁, hv₁, cv₁⟩ := algebra.kpair_l (ZF.v_ordinal_mem_l I hZF setup.rank hκ)
    (ZF.v_subset_mem_l I hZF setup.rank hPX sub)
  obtain ⟨v₂, hv₂, cv₂⟩ := algebra.kpair_l heX hv₁
  obtain ⟨a, ha, ca⟩ := algebra.kpair_l heX hv₂
  have move : Tg_aux_data_d a p.e p.e κ u := ⟨v₁, ⟨v₂, cv₂, ca⟩, cv₁⟩
  have fe : Fn0_d p.e p.ω p.e := ⟨fun x hx => (setup.empty x hx).elim,
    fun x hx => (setup.empty x hx).elim, fun x hx => (setup.empty x hx).elim⟩
  refine ⟨κ, C, a, u, above, hκ, language.rank, ha, move, fun n h z digits growth => ?_⟩
  have rest : M.IsRestrictionOf I p.e z p.e := ⟨(tg_graph_empty_l I setup.empty).1.1,
    fun i v => iff_of_false (fun ⟨q, _, hq⟩ => setup.empty q hq) (fun h => setup.empty i h.1)⟩
  exact ⟨p.e, p.e, κ, u, p.e, p.a, p.b, z, p.e, C, U, P, qr, qm, qb, qh, qn, C, U, D,
    q'.largest, q'.domain, q'.inaccessible, q'.stretch, move, hκ, fe, setup.one, setup.two, digits, rest,
    request, queryData, sub, data, elastic', truth, growth,
    Or.inl ⟨rfl, μ, Y, c, R, r, hμ, hY, model, full, first, last⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
