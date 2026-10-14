import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlRoot
import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePadding
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnswerHistory
import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePastEvents
import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePastRoots
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRank
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunState

/-! # 原获胜策略产生带 padding 的实际首轮

原策略的首个合法走法自动给出重置输入。先加恒等边 0→1，再从原偶数根
作超幂 0→2；原控制记录与已经走出的历史也沿这条实际边进入新反射层，
并用同一个完整回答推进到实数落子及下一辅助阶段。第一份内部历史同时
保存原模型、完整回答和实际奇数结点，全部坐标与本次原记录一致。后继
控制记录的尝试秩由原获胜策略自动提供，反射层无需满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_game_d.run_start_l {p : Tg_params_d M.Domain} {A F₀ L₀ G₀ J₀ B₀ W₀ O Z g σ : M.Domain}
    (game : Tg_game_d hZFC p A F₀ L₀ G₀ J₀ B₀ W₀ O Z g) (woodin : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I false p.ω A F₀ J₀ B₀ W₀ σ) :
    ∃ θ X R c C γ V, M.IsRegularCardinal I θ ∧ V_d I θ X ∧ Smem_d I c X R ∧
      M.IsLimitOrdinal γ ∧ M.mem p.ω V ∧ M.mem p.A V ∧
      ∀ x, M.mem x p.A → ∃ v u, Tg_run_d hZF p.ω c p.e C γ V p.A v u ∧ u 19 = p.a := by
  obtain ⟨H, r, θ, X, R, c, K, η, C, regular, rank, code, source, context, record, nc, ρ, valid, eqρ,
    a, h, value, fn, next, event, ε, seed, hw, he, hd, hS, hν, hk, hb, hs, ht, hg, move, elastic, program, limit₀, letters,
    α, T, Q, D, π, hα, tree, hc, self, iRoot, anchor, ℓ₀, issued⟩ := game.root_l hZFC woodin root win
  -- 初始支撑列为空；先固定这两个小前提，避免在整份后继证书中反复推断。
  have lower : M.MemberSubset (ε.bound 5).val (ε.bound 5).val := fun _ hx => hx
  have above : ∀ i ν, Rd_entry_d i ν p.e → M.mem ν (ε.bound 23).val ∨ ν = (ε.bound 23).val :=
    fun _ _ hh => (hh.elim fun z hz => game.setup.empty z hz.2).elim
  have step := context.pad_round_l hZFC nc ε source tree hα hc code hw game.setup.empty self iRoot anchor lower above seed
  obtain ⟨w, round, β, T₁, Q₁, D₁, E₁, id, π₁, padded, pad, hc₁, edge₁, idFixed, empty,
    root₁, iRoot₁, anchor₁, γ, T', Q', D', E', L', c', j, N, R', K', ℓ, F, κ, U', D'', u', η', C', W,
    result, ext, target, edge, mn, ready, ultra, critical, limit, bound, subset, heights,
    hU, hD, hu, reply, iη, iC, context', legal, hW, hWC, common, level, hQW, hwW, agreement, _, π₂, root₂, _, anchor₂, past⟩ := step
  have eq₁ := padded.tree.diagram.map_unique_l hZF root₁ edge₁
  subst π₁
  have eq₂ := result.tree.diagram.map_unique_l hZF root₂ edge
  subst π₂
  have oldRoot := pad.2.2.1 p.e c hc
  have heβ := (padded.tree.diagram.model_domain p.e).mpr ⟨c, oldRoot⟩
  have self₁ := (pad.2.2.2.1 p.e p.e π hα.predecessor_mem).mpr self
  have self₂ := (ext.2.2.2.1 p.e p.e π heβ).mpr self₁
  have ne : p.e ≠ α := fun eq => game.setup.empty p.e (eq.symm ▸ hα.predecessor_mem)
  have empty₂ q (hq : Rd_entry_d p.e q E') := empty q ((ext.2.2.2.2.2 p.e q ne).mp hq)
  have hj := ultra.elementary_l hZF code.1 mn.1
  have hwκ := critical.omega_lt_l hZF game.setup.omega source.source.transitive ready.source.transitive code mn hj source.source.omega_mem
  have hwB := anchor.rank.ordinal_subset_l hZF source.source.transitive anchor.member p.ω hwκ
  -- 整份原策略控制记录和原历史都沿同一条偶数边搬运。
  obtain ⟨r', _, ir⟩ := hj.1.1.2.2 r (source.source.transitive C context.member r record.member_l)
  have record' := record.map_l hZF tg_control0_closed_l game.setup.omega source.source.transitive ready.source.transitive code mn hj iC ir
  let nv : Nonempty {x // M.mem x C'} := ⟨⟨p.ω, context'.omega⟩⟩
  obtain ⟨ρ', images, valid'⟩ := hj.relative_image_l hZF game.setup.omega source.source.transitive ready.source.transitive code mn
    (context.read_l hZF source.source).1.transitive (context'.read_l hZF ready.source).1.transitive
    nc nv iC tg_control0_m tg_control0_closed_l ρ
  obtain ⟨h', _, ih⟩ := hj.1.1.2.2 h.val (source.source.transitive C context.member h.val h.property)
  have hh' := (hj.member_l I hZF game.setup.omega code mn ih iC).mp h.property
  have hH : (ρ.bound 18).val = H := eqρ 18
  have hA : (ρ.bound 12).val = A := eqρ 12
  have next' := (hj.member_l I hZF game.setup.omega code mn ih (hH ▸ images 18)).mp next
  have one := hj.natural_l hZF game.setup.omega source.source.transitive ready.source.transitive code mn source.source.omega_mem
    p.a (num_mem_l hZF.1 game.setup.omega (show Num_d 1 p.a from ⟨p.e, game.setup.empty, game.setup.one⟩))
  have fn' := (hj.function_l hZF game.setup.omega source.source.transitive ready.source.transitive code mn one (hA ▸ images 12) ih).mp fn
  obtain ⟨ζ, carried, issued'⟩ := hj.relative_image_l hZF game.setup.omega source.source.transitive ready.source.transitive code mn
    (context.read_l hZF source.source).1.transitive (context'.read_l hZF ready.source).1.transitive
    nc nv iC tg_issued0_m tg_issued0_closed_l (tg_issued_start_env_d ρ ε a h ℓ₀ (ρ.bound 2))
  -- 内部自然数及原程序沿实际嵌入固定；大类型和常量域则使用同一超幂的像。
  let ξ := tg_round_env_d ε w
  have natural := hj.natural_l hZF game.setup.omega source.source.transitive ready.source.transitive
    code mn source.source.omega_mem
  have fixed {x y : M.Domain} (hx : M.mem x p.ω) (xy : Rd_entry_d x y j) : y = x :=
    hj.1.1.1.2 x y x xy (natural x hx)
  have iω : Rd_entry_d p.ω (ζ.bound 0).val j :=
    (show (ρ.bound 0).val = p.ω from eqρ 0) ▸
      (show Rd_entry_d (ρ.bound 0).val (ζ.bound 0).val j from carried 0)
  have zω := hj.1.1.1.2 p.ω (ζ.bound 0).val p.ω iω
    (hj.omega_l I hZF game.setup.omega source.source.transitive ready.source.transitive code mn source.source.omega_mem)
  have heω := num_mem_l hZF.1 game.setup.omega (show Num_d 0 p.e from game.setup.empty)
  have ie : Rd_entry_d p.e (ζ.bound 1).val j :=
    (show (ρ.bound 1).val = p.e from eqρ 1) ▸
      (show Rd_entry_d (ρ.bound 1).val (ζ.bound 1).val j from carried 1)
  have ze := fixed heω ie
  have data := (Formula.satisfies_conj_iff ..).mp round |>.2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at data
  obtain ⟨_, _, _, _, _, _, _, _, _, language, _, _, _, hbω, hzω, hs₀, hs₁, hs₂, hs₃, hs₄, hs₅, hs₆, _⟩ := data
  simp only [tg_reply_language_m, Formula.satisfies_bind, tg_reply_language0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at language
  have hnω : M.mem (ε.bound 8).val p.ω := hw ▸ language.1
  have hlω : M.mem (ε.bound 7).val p.ω := source.source.omega.transitive hZF _ hnω _ language.2.2.1
  have same : ∀ i : Fin 14, (ζ.bound ([0, 1, 26, 27, 28, 36, 37, 38, 39, 40, 41, 42, 43, 44].get i)).val =
      (ξ.bound ([16, 17, 22, 23, 24, 36, 38, 47, 48, 49, 50, 51, 52, 53].get i)).val := by
    intro i
    exact Fin.cases (zω.trans hw.symm) (Fin.cases (ze.trans he.symm)
      (Fin.cases (fixed (hk.symm ▸ heω) (carried 26))
      (Fin.cases (fixed hlω (carried 27)) (Fin.cases (fixed hnω (carried 28))
      (Fin.cases (fixed (hw ▸ hbω) (carried 36)) (Fin.cases (fixed (hw ▸ hzω) (carried 37))
      (Fin.cases (fixed (hw ▸ hs₀) (carried 38)) (Fin.cases (fixed (hw ▸ hs₁) (carried 39))
      (Fin.cases (fixed (hw ▸ hs₂) (carried 40)) (Fin.cases (fixed (hw ▸ hs₃) (carried 41))
      (Fin.cases (fixed (hw ▸ hs₄) (carried 42)) (Fin.cases (fixed (hw ▸ hs₅) (carried 43))
      (Fin.cases (fixed (hw ▸ hs₆) (carried 44)) (fun a => Fin.elim0 a)))))))))))))) i
  have zκ := hj.1.1.1.2 (ε.bound 5).val (ζ.bound 24).val κ (carried 24) critical.image
  have zU := hj.1.1.1.2 (ε.bound 15).val (ζ.bound 30).val U' (carried 30) hU
  have zD := hj.1.1.1.2 (ε.bound 16).val (ζ.bound 31).val D'' (carried 31) hD
  have zu := hj.1.1.1.2 (ε.bound 18).val (ζ.bound 25).val u' (carried 25) hu
  have hδ : M.IsOrdinal (ε.bound 2).val := (context.round_regular_l hZF nc ξ source hw round).1.1
  have iδ : Rd_entry_d p.δ (ζ.bound 5).val j :=
    (show (ρ.bound 5).val = p.δ from eqρ 5) ▸
      (show Rd_entry_d (ρ.bound 5).val (ζ.bound 5).val j from carried 5)
  have δ' := hj.ordinal_l hZF game.setup.omega source.source.transitive ready.source.transitive
    code mn iδ (hd ▸ hδ)
  have fs' := (context'.read_l hZF ready.source).1
  have state := (tg_issued_sat_l (rt_pair_l fs'.transitive nv hZF.1 fs'.pair)
    (rt_model_ext_l hZF.1 fs'.transitive nv) ζ).mp (issued'.mp issued)
  have below := δ'.transitive κ (zκ ▸ state.bound) (w 15).val (subset _ bound)
  have rootNode := ext.2.2.1 p.e c oldRoot
  have rootMap := result.tree.diagram.elementary p.e p.e π c X R c X R self₂ rootNode rootNode code.1 code.1
  have response := context.answer_history_l hZF nc ξ context' source.source ready.source ready.hierarchy
    source.source.transitive code code mn rootMap hj iRoot iC anchor anchor₂ limit₀ hwB
    hW common level.member level.hierarchy limit (common.ordinal_subset_l hZF source.source.transitive hW _ bound)
    nv ζ (issued'.mp issued) hw same below round (by
      rw [zκ, zU, zD, zu]
      exact reply)
  have initial : Tg_past_d hZF p.ω p.e p.e X p.e := tg_past_empty_l hZF game.setup.empty
  have heκ := limit₀.1.empty_mem_of_nonempty (ZF.modelsKP hZF) limit₀.2.1 game.setup.empty
  obtain ⟨n, P₀, q₀, _, sn, history, _, savedCode, newest, entries, _, links⟩ :=
    past p.e p.e p.e heω initial heκ (tg_past_links_empty_l I game.setup.empty)
  have en : n = p.a := sn.eq hZF.1 game.setup.one
  subst n
  have body := (Formula.satisfies_conj_iff ..).mp round |>.2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at body
  have low : M.MemberSubset (ε.bound 5).val (w 15).val := (limit.1.mem bound).transitive _ body.2.1
  have roots := Tg_past_roots_d.push_l hZF history sn newest entries
    (tg_past_roots_empty_l game.setup.empty)
    ((ext.2.2.2.1 p.e α id pad.1.predecessor_mem).mpr root₁) iRoot₁ anchor₁ ⟨_, savedCode, low⟩
  have zn : (ζ.bound 19).val = p.e := fixed heω ((show (ρ.bound 1).val = p.e from eqρ 1) ▸ carried 19)
  have zt : (ζ.bound 23).val = (ξ.bound 41).val :=
    (fixed heω (ht ▸ carried 23)).trans ht.symm
  have add {s : M.Domain}
      (trace : Tg_trace_d p.ω C' (ζ.bound 4).val (ζ.bound 1).val (ζ.bound 2).val
        (ζ.bound 19).val s (ζ.bound 23).val (w 15).val (w 11).val) :
      Tg_past_events_d p.ω P₀ C' (ζ.bound 4).val (ζ.bound 1).val (ζ.bound 2).val s := by
    apply Tg_past_events_d.push_l hZF history sn newest entries
      (tg_past_events_empty_l game.setup.empty) _ savedCode
    exact zn ▸ zt ▸ trace
  obtain ⟨v, t, q, pair, position, endt, trace, advance⟩ := response
  refine ⟨θ, X, R, c, C, (ε.bound 5).val, (ε.bound 14).val, regular, rank, code, limit₀, hwB, letters, ?_⟩
  intro x hx
  have iA : Rd_entry_d p.A (ζ.bound 6).val j := (show (ρ.bound 6).val = p.A from eqρ 6) ▸ carried 6
  have Aζ := hj.1.1.1.2 p.A (ζ.bound 6).val p.A iA (anchor₂.fixed p.A letters)
  have hxζ : M.mem x (ζ.bound 6).val := Aζ.symm ▸ hx
  let x' : (rt_model_l C' nv).Domain := ⟨x, fs'.transitive _ (ζ.bound 6).property x hxζ⟩
  obtain ⟨v', t', j', n', hv, even, odd, digit, succ, start, ε', head, num, issued', value, aux, growth, keep, _, trace'⟩ := advance x' hxζ
  have control (i : Fin 19) : ε'.bound (i.castAdd 27) = ζ.bound (i.castAdd 27) :=
    (head i).trans (by simp only [tg_position_env_d, Fin.addCases_left])
  have sn' := (rt_successor_l fs'.transitive nv hZF.1 (ε'.bound 19) (ζ.bound 19)).mp (num.symm ▸ succ)
  have en' : (ε'.bound 19).val = p.a := (show M.SuccessorOf (ε'.bound 19).val p.e from zn ▸ sn').eq hZF.1 game.setup.one
  have events := add trace'
  have events : Tg_past_events_d p.ω P₀ C' (ε'.bound 4).val (ε'.bound 1).val (ε'.bound 2).val (ε'.bound 20).val :=
    (congrArg Subtype.val (control 4)).symm ▸ (congrArg Subtype.val (control 1)).symm ▸
      (congrArg Subtype.val (control 2)).symm ▸ events
  obtain ⟨r₂, record₂, values₂⟩ := context'.save_issued_l hZF ready.source nv ε' issued'
  let J := rt_pair_l fs'.transitive nv hZF.1 fs'.pair
  have extC := rt_model_ext_l hZF.1 fs'.transitive nv
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, lang⟩ :=
    tg_issued_query_l J extC ε' issued'
  simp only [tg_reply_language0_m, Formula.satisfies_conj_iff] at lang
  have κlimit := (rt_limit_l fs'.transitive nv (ZF.modelsKP hZF) (ε'.bound 24)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp lang.2.2.2.1)
  have growing : M.mem κ (ε'.bound 24).val := zκ ▸ growth
  have high : M.MemberSubset (ε.bound 5).val κ := fun y hy => subset y (limit.1.transitive _ bound y (low y hy))
  have nextω {a b : M.Domain} (ha : M.mem a p.ω) (hs : M.SuccessorOf b a) : M.mem b p.ω := by
    obtain ⟨b', hs', hb'⟩ := game.setup.omega.1.2 a ha
    exact hs'.eq hZF.1 hs ▸ hb'
  let v₂ : Fin 18 → M.Domain := fun i => [N, R', ℓ, K', η', C', γ, β, T', Q', D', E', L', P₀, κ, c', j, r₂].get i
  have span : M.mem (ε'.bound 19).val γ := en'.symm ▸
    (show M.mem p.a γ from (hα.eq hZF.1 game.setup.one) ▸
      result.tree.diagram.order.ordinal.transitive β ext.1.predecessor_mem α pad.1.predecessor_mem)
  exact ⟨v₂, (fun i => (ε'.bound i).val),
    ⟨ready, context', nextω (nextω heω hα) pad.1, ext.1, result, target, mn, edge, iC, anchor₂, record₂, values₂,
      (congrArg Subtype.val (control 0)).trans zω, (congrArg Subtype.val (control 6)).trans Aζ,
      fun y hy => κlimit.1.transitive κ growing y (high y hy), en'.symm ▸ history, links, roots, events, growing, heights, span⟩, en'⟩

end YesMetaZFC.SetTheory.LargeCardinal
