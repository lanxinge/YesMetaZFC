import YesMetaZFC.SetTheory.LargeCardinal.Game.DigitsImage
import YesMetaZFC.SetTheory.LargeCardinal.Game.Tracked
import YesMetaZFC.Model.Forcing.Truth.Definability
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinTypeStep
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Types.OneStep

/-! # 三阶段历史中的原字母图追加

同一实际历史的包含、末轮事件和函数性产生新的原字母前缀。
此纯时钟引理由两种类型游戏共同消费，不依赖任一种游戏的合法性规则。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_digits_d.append_l {ω c b n m A h t z y : M.Domain}
    (hw : M.IsOmega ω) (hc : M.IsOrdinal c) (hn : M.mem n ω) (succ : M.SuccessorOf m n)
    (digits : Tg_digits_d hZF c b n A h z) (sub : M.MemberSubset h t) (ft : M.IsSetFunction I t)
    (hy : M.mem y A) (event : Tg_event_d I c n b t y) :
    ∃ z', Fseq_end_d I ω z' z y ∧ Tg_digits_d hZF c b m A t z' := by
  obtain ⟨m', z', hm', fz', endz⟩ := ZF.fseq_end_exists_l I hZF hw hn (fn0_function_l (ZF.modelsKP hZF) digits.1) hy
  obtain ⟨r, s, dec⟩ := endz
  have es := dec.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) digits.1).2.1; subst s
  have er := dec.source.2.2.2.eq hZF.1 fz'.2.1; subst r
  have em := dec.length_successor.eq hZF.1 succ; subst m'
  refine ⟨z', ⟨m, n, dec⟩, fn0_of_function_l (ZF.modelsKP hZF) fz', fun i v hi => ?_⟩
  obtain ⟨w, _, iw⟩ := fz'.2.2 i hi
  have ew : Tg_event_d I c i b t w := by
    rcases (succ i).mp hi with hin | eq
    · obtain ⟨j, clock, q, pair, hq⟩ := (digits.2 i w hin).mp ((dec.prefix_restriction.2 i w).mpr ⟨hin, iw⟩)
      exact ⟨j, clock, q, pair, sub q hq⟩
    · have eq := hZF.1.eq_of_same_members i n eq; subst i
      exact (fz'.1.2 n w y iw dec.last_value).symm ▸ event
  exact ⟨fun iv => (fz'.1.2 i w v iw iv) ▸ ew,
    fun ev => (ew.unique_l hZF hc ft ev) ▸ iw⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 地模型稠密集与真实泛型性调用

有限条件的延长定理给出稠密性；原公式给出地模型中的分离集合。
直接使用已有泛型滤子的 meets，不假设泛型枚举具有额外的请求公平性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
open Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

theorem tg_dense_hit_defined_l (hZF : M.Models ZF) (p : Tg_params_d M.Domain) (ℓ s t k N β g a₀ b₀ E : M.Domain) :
    Defined_d M (Tg_dense_hit_d hZF p ℓ s t k N β g a₀ b₀ E) := by
  let ρ : Env M 22 := ⟨fun i => [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q,
    ℓ, s, t, k, N, β, g, a₀, b₀, E].get i, fun _ => p.ω⟩
  let a : Tg_params_d (Term 23) := ⟨.bound 1, .bound 2, .bound 3, .bound 4, .bound 5, .bound 6,
    .bound 7, .bound 8, .bound 9, .bound 10, .bound 11, .bound 12⟩
  let φ : UnarySchema 22 := {
    body := tg_dense_hit_m a (.bound 13) (.bound 14) (.bound 15) (.bound 16) (.bound 17)
      (.bound 18) (.bound 19) (.bound 20) (.bound 21) (.bound 22) .newest
    freeClosed := by
      simp -implicitDefEqProofs [tg_dense_hit_m, Definitional.Formula.FreeClosed, a]
      apply tg_generic_target_closed_l <;>
        simp -implicitDefEqProofs [Tg_params_d.closed_l, Tg_params_d.map_l] }
  refine ⟨22, φ, ρ, fun q => ?_⟩
  exact tg_dense_hit_sat_l hZF (ρ.push q) a (.bound 13) (.bound 14) (.bound 15) (.bound 16) (.bound 17)
    (.bound 18) (.bound 19) (.bound 20) (.bound 21) (.bound 22) .newest

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_setup_d.generic_meet_l {p : Tg_params_d M.Domain}
    {X ℓ a₀ ℓ₀ t₀ κ₀ u₀ b₀ j k N τ B U D w η Y c R r g β s t g' x F Q E : M.Domain}
    {q₀ : Tg_reply_queries_d M} {G : M.Domain → Prop}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d I p.δ) (hℓ : M.mem ℓ p.ω)
    (oldMove : Tg_aux_data_d a₀ ℓ₀ t₀ κ₀ u₀) (oldAnswer : KPair_d M b₀ τ w)
    (ft₀ : Fn0_d j p.ω t₀) (hk : M.SuccessorOf k j) (hN : M.SuccessorOf N k)
    (ft : Fn0_d k p.ω t) (cut : M.IsRestrictionOf I t₀ t j)
    (oldLanguage : Tg_reply_language_d hZF p.ω p.e k N τ B U D q₀)
    (hY : V_d I η Y) (model : Smem_d I c Y R) (type : Tt_realized_d I p.ω c Y R N r p.δ U D w)
    (rS : Rd_entry_d p.e p.S r) (last : Rd_entry_d k β r) (set : Sg_set_d I p.e k r g)
    (bound : Tg_bound_d I p.δ p.S β) (height : Tg_height_d β η)
    (node : Tg_node_d I k p.S s t g') (extend : ∀ a, M.mem a g' ↔ M.mem a g ∨ a = x)
    (hτ : M.mem τ p.δ) (hs : M.mem s X) (ht : M.mem t X) (space : Fseq_space_d I p.ω X F)
    (order : ∀ q r, Entry_d M q r Q ↔ M.mem q F ∧ M.mem r F ∧ M.MemberSubset r q)
    (generic : Generic_d M F Q F G) (hE : M.mem E p.ω) :
    ∃ q, G q ∧ Tg_dense_hit_d hZF p ℓ s t k N β g' a₀ b₀ E q := by
  obtain ⟨f, hf⟩ := generic.inhabited
  apply generic_pick_l hZF generic (tg_dense_hit_defined_l hZF p ℓ s t k N β g' a₀ b₀ E) hf
  intro q hq
  obtain ⟨κ, C, a, u, μ, A, d, H, m, V, P, r', i, q', hκ, hC, ha, move, hμ, hA, lower,
    hm, constants, full, first, last, labels, hq', sub, hEi, hi, ia, before, legal⟩ :=
    setup.generic_dense_l hZFC hd hℓ oldMove oldAnswer ft₀ hk hN ft cut oldLanguage hY model type
      rS last set bound height node extend hτ hs ht space hq.1 hE
  exact ⟨q', subset_below_l hZF order hq.1 hq' sub,
    κ, C, a, u, i, ⟨hκ, hC, move, ⟨μ, A, d, H, m, V, P, r', hμ, hA, lower, hm, constants, full, first, last, labels⟩, legal⟩,
    hEi, hi, ia, before⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 首达时刻的实际请求捕获

首达之前的最后一个请求落在目标 Vκ 中，故其参数域严格小于 κ。由原规则
推出目标请求合法，再以最小编号性排除越过目标编号；整个类型检查留在地模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} (hM : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)

theorem Tg_aux_data_d.domain_bound_l {a ℓ t τ u κ C : M.Domain}
    (data : Tg_aux_data_d a ℓ t τ u) (hC : V_d I κ C) (hτ : M.IsOrdinal τ) (ha : M.mem a C) : M.mem τ κ := by
  obtain ⟨b, ⟨d, pair₀, pair₁⟩, pair₂⟩ := data
  have tr := v_transitive_l I hC
  exact ZF.v_ordinal_height_l hM hC hτ
    (KPair_d.mem_l M pair₂ tr (KPair_d.mem_l M pair₀ tr (KPair_d.mem_l M pair₁ tr ha).2).2).1

/-- 原逐步检查给出实际可追加历史，不把“合法请求”当作额外判定器。 -/
theorem Tg_histories_d.admit_l {p : Tg_params_d M.Domain} {X F L i n h a : M.Domain}
    (histories : Tg_histories_d hM p X F L) (hw : M.IsOmega p.ω) (hi : M.mem i p.ω)
    (hn : M.mem n p.ω) (fn : Fn0_d i X h) (div : M.IsOrdinalDivision I i p.c n p.e)
    (ha : M.mem a X) (aux : Tg_aux_d hM p n h a) : Cg_admit_d hM p.ω L h a := by
  obtain ⟨j, t, hj, ft, endt⟩ := ZF.fseq_end_exists_l I hM hw hi (fn0_function_l (ZF.modelsKP hM) fn) ha
  obtain ⟨j', i', d⟩ := endt
  have ei := d.prefix_sequence.2.2.2.eq hM.1 (fn0_function_l (ZF.modelsKP hM) fn).2.1
  have ej := d.source.2.2.2.eq hM.1 ft.2.1
  have succ : M.SuccessorOf j i := ej ▸ ei ▸ d.length_successor
  exact ⟨t, (histories.2 t).mpr ⟨(histories.1 t).mpr ⟨j, hj, ft⟩,
    tg_check_end_l hM hj succ (fn0_of_function_l (ZF.modelsKP hM) ft) fn ⟨j', i', d⟩
      ⟨n, p.e, hn, div, Or.inl ⟨rfl, aux⟩⟩⟩, j', i', d⟩

variable {N : Structure.{v}} (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

/-- 6.6 的捕获步骤：首次不低于 i 的选择只能等于 i。此前只需最后一次选择的界。 -/
theorem Tg_generic_target_d.capture_l {p : Tg_params_d M.Domain}
    {X F L ℓ s t k m β g a₀ b₀ κ C a u q d i n z h r j a' ℓ' t' τ u' : M.Domain}
    {f v w : N.Domain}
    (target : Tg_generic_target_d hM p ℓ s t k m β g a₀ b₀ κ C a u)
    (hw : M.IsOmega p.ω) (hw' : N.IsOmega (e p.ω)) (histories : Tg_histories_d hM p X F L)
    (fq : Fn0_d d X q) (dw : M.mem d p.ω) (ia : Rd_entry_d i a q) (iw : M.mem i p.ω)
    (before : ∀ j y, M.mem j i → Rd_entry_d j y q → M.mem y C)
    (ff : N.IsSetFunction J f) (kept : ∀ j y, Rd_entry_d j y q → Rd_entry_d (e j) (e y) f)
    (scan : Cg_scan_d hN (e p.ω) (e L) f (e h) v) (cross : ¬ N.mem v (e i))
    (lastIndex : Rd_entry_d w (e a') f) (below : N.mem w (e i))
    (old : Tg_aux_data_d a' ℓ' t' τ u') (oτ : M.IsOrdinal τ)
    (succ : M.SuccessorOf n j) (oldEvent : Tg_event_d I p.c j p.e h a')
    (hn : M.mem n p.ω) (hr : M.mem r p.ω) (fn : Fn0_d r X h)
    (div : M.IsOrdinalDivision I r p.c n p.e)
    (digits : Tg_digits_d hM p.c p.b n p.A h z) (real : M.IsRestrictionOf I s z k)
    (hℓ : M.mem ℓ n) (event₀ : Tg_event_d I p.c ℓ p.e h a₀) (event₁ : Tg_event_d I p.c ℓ p.a h b₀) :
    v = e i ∧ Rd_entry_d v (e a) f ∧ Tg_aux_d hM p n h a := by
  obtain ⟨j₀, hj₀, eq⟩ := (he i w).mp below
  have fq' := fn0_function_l (ZF.modelsKP hM) fq
  have hid := fq'.input_mem_of_pairMember ia
  -- i 是有限条件已有的坐标，故 i 之前的枚举值均来自该条件。
  have od := hw.members_areOrdinals (ZF.modelsKP hM) d dw
  obtain ⟨y, _, jy⟩ := fq'.2.2 j₀ (od.transitive i hid j₀ hj₀)
  have same : e a' = e y := ff.2 (e j₀) (e a') (e y) (eq.symm ▸ lastIndex) (kept j₀ y jy)
  have bound := old.domain_bound_l hM target.2.1 oτ ((hi same).symm ▸ before j₀ y hj₀ jy)
  have aux := target.2.2.2.2 n h z digits real hℓ event₀ event₁ (Or.inr ⟨j, a', ℓ', t', τ, u', succ, oldEvent, old, bound⟩)
  have legal := histories.admit_l hM hw hr hn fn div (fq.bound_l ia).2 aux
  have hh := (histories.1 h).mpr ⟨r, hr, fn0_function_l (ZF.modelsKP hM) fn⟩
  have legal' := (image_admit_l hM hN e hi he hw hw' histories.1 (fun t ht => ((histories.2 t).mp ht).1) hh).mp legal
  have eq := (scan.le_l hN hw' ((image_member_l e hi he).mpr iw) (kept i a ia) legal').elim (fun lt => (cross lt).elim) (fun eq => eq)
  exact ⟨eq, eq.symm ▸ kept i a ia, aux⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意参数域下界以上的原游戏重置走法

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
  have haω := setup.omega.transitive (ZF.modelsKP hZF) p.b full.finite p.a setup.two.predecessor_mem
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
  have truth := (nodeQuery.2 c Y R r p.δ u p.S model (v_transitive_l I hY) full first).mpr
    ⟨p.e, full.constants p.e heU, labels, (tg_node_empty_l I hZF.1 setup.empty).mpr root⟩
  have algebra := sc_v_algebra_l hZFC setup.limit setup.rank
  have hwX := ZF.v_ordinal_mem_l I hZF setup.rank setup.above
  have heX := v_transitive_l I setup.rank p.ω hwX p.e heω
  have hUX := tt_constants_rank_l hZF setup.rank setup.limit hκ language.rank language.constants
  have hPX := full.pool.rank_mem_l (ZF.modelsKP hZF) setup.omega setup.rank setup.limit hwX full.finite hUX
  have sub : M.MemberSubset u P := fun x hx => ((full.truth x).mp hx).1
  obtain ⟨v₁, hv₁, cv₁⟩ := algebra.kpair_l (ZF.v_ordinal_mem_l I hZF setup.rank hκ)
    (v_subset_mem_l I setup.rank hPX sub)
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

/-! ## 原辅助轮开始时的有限状态与可继续性

状态保存实际三阶段时钟、已落下的实数图和前一个请求。由武丁重置构造直接
证明每个这样的状态都有合法请求；不把“存在下一步”加入递归的假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_ready_d (p : Tg_params_d M.Domain) (X n h : M.Domain) : Prop :=
  M.mem n p.ω ∧ ∃ i z, M.mem i p.ω ∧ Fn0_d i X h ∧ M.IsOrdinalDivision I i p.c n p.e ∧
    Tg_digits_d hZF p.c p.b n p.A h z ∧
    (n = p.e ∨ ∃ j a ℓ t κ u, M.SuccessorOf n j ∧ Tg_event_d I p.c j p.e h a ∧ Tg_aux_data_d a ℓ t κ u ∧ M.mem κ p.δ)

def tg_ready_m {d} (ω e c b δ A X n h : Term d) : Formula 1 d := set[d] ⟪⌜n⌝ₛ ∈ ⌜ω⌝ₛ ∧
  (∃ i z, i ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(i, ⌜X⌝ₛ, ⌜h⌝ₛ) ∧
    ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(i, ⌜c⌝ₛ, ⌜n⌝ₛ, ⌜e⌝ₛ) ∧
    ⌜tg_digits_m⌝ₚ(⌜c⌝ₛ, ⌜b⌝ₛ, ⌜n⌝ₛ, ⌜A⌝ₛ, ⌜h⌝ₛ, z) ∧
    (⌜n⌝ₛ = ⌜e⌝ₛ ∨ (∃ j a ℓ t κ u, ⌜Formula.isSuccessor⌝ₚ(⌜n⌝ₛ, j) ∧
      ⌜tg_event_m⌝ₚ(⌜c⌝ₛ, j, ⌜e⌝ₛ, ⌜h⌝ₛ, a) ∧ ⌜tg_aux_data_m⌝ₚ(a, ℓ, t, κ, u) ∧ κ ∈ ⌜δ⌝ₛ)))⟫
derive_free_closed tg_ready_m

theorem tg_ready_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X n h : Term d) :
    Formula.satisfies ρ (tg_ready_m p.ω p.e p.c p.b p.δ p.A X n h) ↔
      Tg_ready_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (n.eval ρ) (h.eval ρ) := by
  simp only [tg_ready_m, Tg_ready_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, fn0_sat_l hZF.1, Formula.satisfies_isOrdinalDivision_iff I hZF.1,
    tg_digits_sat_l hZF, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_isSuccessor_iff, tg_event_sat_l I hZF.1, tg_aux_data_sat_l hZF.1,
    Tg_params_d.map_l, Definitional.Term.eval_weaken]; rfl

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hZ)

theorem Tg_setup_d.ready_empty_l {p : Tg_params_d M.Domain} {X : M.Domain}
    (setup : Tg_setup_d hZFC p X) : Tg_ready_d hZ p X p.e p.e := by
  have he := num_mem_l hZ.1 setup.omega (show Num_d 0 p.e from setup.empty)
  have oe := setup.omega.members_areOrdinals (ZF.modelsKP hZ) p.e he
  obtain ⟨hc, _⟩ := tg_clock_l hZ setup.omega setup.empty setup.one setup.two setup.three he
  have oc := setup.omega.members_areOrdinals (ZF.modelsKP hZ) p.c hc
  have ec := oc.empty_mem_of_nonempty (ZF.modelsKP hZ) ⟨p.b, setup.three.predecessor_mem⟩ setup.empty
  have empty (Y : M.Domain) : Fn0_d p.e Y p.e := ⟨fun x hx => (setup.empty x hx).elim,
    fun x hx => (setup.empty x hx).elim, fun x hx => (setup.empty x hx).elim⟩
  exact ⟨he, p.e, p.e, he, empty X, ⟨oe, ec, p.e,
    (ZF.ordinalMultiplication_zero_iff hZ K oc setup.empty).mpr setup.empty,
    (ZF.ordinalAddition_zero_iff hZ K setup.empty).mpr rfl⟩,
    ⟨empty p.A, fun i _ hi => (setup.empty i hi).elim⟩, Or.inl rfl⟩

/-- 可继续性来自原重置类型工厂，包括零轮的字母表秩界和后继轮的参数域增长。 -/
theorem Tg_setup_d.ready_move_l {p : Tg_params_d M.Domain} {X n h : M.Domain}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d K p.δ) (root : M.mem p.e p.S)
    (ready : Tg_ready_d hZ p X n h) : ∃ a, M.mem a X ∧ Tg_aux_d hZ p n h a := by
  obtain ⟨_, i, z, _, _, _, digits, old⟩ := ready
  have heω := num_mem_l hZ.1 setup.omega (show Num_d 0 p.e from setup.empty)
  have zero := setup.limit.1.transitive p.ω setup.above p.e heω
  have bound : ∃ τ, M.mem τ p.δ ∧ (n = p.e ∨ ∃ j a ℓ t u,
      M.SuccessorOf n j ∧ Tg_event_d K p.c j p.e h a ∧ Tg_aux_data_d a ℓ t τ u) := by
    rcases old with eq | ⟨j, a, ℓ, t, τ, u, succ, event, data, below⟩
    · exact ⟨p.e, zero, Or.inl eq⟩
    · exact ⟨τ, below, Or.inr ⟨j, a, ℓ, t, u, succ, event, data⟩⟩
  obtain ⟨τ, hτ, old⟩ := bound
  obtain ⟨B, hB, pair⟩ := (sc_v_algebra_l hZFC setup.limit setup.rank).pair p.A τ setup.letters
    (ZF.v_ordinal_mem_l K hZ setup.rank hτ)
  obtain ⟨χ, Z, hχ, hZ', sub⟩ := (ZF.v_unfold_l K hZ setup.rank B).mp hB
  have hAZ := sub p.A ((pair p.A).mpr (Or.inl rfl))
  have hτχ := ZF.v_ordinal_height_l hZ hZ' (setup.limit.1.mem hτ) (sub τ ((pair τ).mpr (Or.inr rfl)))
  obtain ⟨κ, C, a, u, above, _, rank, ha, _, legal⟩ := setup.reset_move_l hZFC hd root hχ
  refine ⟨a, ha, legal n h z digits ?_⟩
  rcases old with eq | ⟨j, v, ℓ, t, u, succ, event, data⟩
  · exact Or.inl ⟨eq, ZF.v_mono_l K hZ hZ' rank ((v_ordinal_l K rank).transitive χ above) p.A hAZ⟩
  · exact Or.inr ⟨j, v, ℓ, t, τ, u, succ, event, data, (v_ordinal_l K rank).transitive χ above τ hτχ⟩

end YesMetaZFC.SetTheory.LargeCardinal
