import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlRoot
import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePadding
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnswerHistory
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRank

/-! # 原获胜策略产生带 padding 的实际首轮

原策略的首个合法走法自动给出重置输入。先加恒等边 0→1，再从原偶数根
作超幂 0→2；原控制记录与已经走出的历史也沿这条实际边进入新反射层，
并用同一个完整回答推进到实数落子及下一辅助阶段。后继控制记录的实际
尝试秩由原获胜策略自动提供，反射层无需满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_game_d.tree_step_l {p : Tg_params_d M.Domain} {A F₀ L₀ G₀ J₀ B₀ W₀ O Z g σ : M.Domain}
    (game : Tg_game_d hZFC p A F₀ L₀ G₀ J₀ B₀ W₀ O Z g) (woodin : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I false p.ω A F₀ J₀ B₀ W₀ σ) :
    ∃ H r θ X R c K η C, M.IsRegularCardinal I θ ∧ V_d I θ X ∧ Smem_d I c X R ∧
      Ic_model_d hZF p.ω p.ω K X R ∧ Tg_context_d p.ω X η C ∧ Rt_record_in_d tg_control0_m C r ∧
      ∃ nc : Nonempty {x // M.mem x C}, ∃ ρ : Env (rt_model_l C nc) 19,
        Formula.satisfies ρ tg_control0_m ∧
        (∀ i, (ρ.bound i).val = [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, A, F₀, L₀, G₀, J₀, σ, H].get i) ∧
      ∃ a h : (rt_model_l C nc).Domain, Rd_entry_d p.e a.val σ ∧ Fn0_d p.a A h.val ∧ M.mem h.val H ∧
      Formula.satisfies (⟨fun i => [ρ.bound 4, ρ.bound 1, ρ.bound 1, h, a].get i, ρ.free⟩ : Env (rt_model_l C nc) 5)
        (tg_event_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)) ∧
      ∃ ε : Env (rt_model_l C nc) 38,
        let v : Fin 38 → M.Domain := fun i => (ε.bound i).val
        let s : Fin 7 → M.Domain := Fin.cases (v 31) (Fin.cases (v 32) (Fin.cases (v 33)
          (Fin.cases (v 34) (Fin.cases (v 35) (Fin.cases (v 36) (fun _ => v 37))))))
        Formula.satisfies ε tg_seed0_m ∧ v 0 = p.ω ∧ v 1 = p.e ∧ v 2 = p.δ ∧ v 3 = p.S ∧ v 4 = p.ν ∧
        v 6 = p.e ∧ v 23 = v 5 ∧ v 24 = p.e ∧ v 25 = p.e ∧ v 26 = p.e ∧
        (∃ ℓ, Tg_aux_data_d a ℓ (ε.bound 25) (ε.bound 5) (ε.bound 18)) ∧
        Tg_ee_data_d (ρ.bound 9) (ε.bound 5) (ε.bound 7) (ε.bound 14) (ε.bound 15) (ε.bound 16)
          ⟨ε.bound 27, ε.bound 28, ε.bound 29, ε.bound 30⟩ ∧
        Tg_program_data_d (ρ.bound 10) (ε.bound 7) (ε.bound 20) (ε.bound 22)
          (Fin.cases (ε.bound 31) (Fin.cases (ε.bound 32) (Fin.cases (ε.bound 33) (Fin.cases (ε.bound 34)
            (Fin.cases (ε.bound 35) (Fin.cases (ε.bound 36) (fun _ => ε.bound 37))))))) ∧
        M.IsLimitOrdinal (v 5) ∧ M.mem p.A (v 14) ∧
        ∃ ℓ₀, Formula.satisfies (tg_issued_start_env_d ρ ε a h ℓ₀ (ρ.bound 2)) tg_issued0_m ∧
        ∃ w : Fin 16 → (rt_model_l C nc).Domain,
          Formula.satisfies (tg_round_env_d ε w) tg_round0_m ∧
          ∃ α β γ T Q D E L id c' j N R' K' ℓ F κ U' D' u' η' C' W π,
            M.SuccessorOf α p.e ∧ M.SuccessorOf β α ∧ M.SuccessorOf γ β ∧ It_pnice_d hZF p.ω c γ T Q D E L ∧
            Rd_entry_d p.e c Q ∧ Rd_entry_d α c Q ∧ It_map_d D p.e α id ∧
            (∀ x y, Rd_entry_d x y id → x = y) ∧ (∀ q, Rd_entry_d p.e q E → ∀ x, ¬ M.mem x q) ∧
            Rd_entry_d β c' Q ∧ It_map_d D p.e β j ∧ Smem_d I c' N R' ∧ Ic_model_d hZF p.ω ℓ K' N R' ∧
            It_ultra_d hZF p.ω (v 5) ℓ F c c' j ∧ Wd_crit_d I X j (v 5) κ ∧
            M.IsLimitOrdinal ℓ ∧ M.mem (w 15).val ℓ ∧ M.MemberSubset ℓ κ ∧
            (∀ i μ, Rd_entry_d i μ L → M.mem μ κ ∨ μ = κ) ∧
            Rd_entry_d (v 15) U' j ∧ Rd_entry_d (v 16) D' j ∧ Rd_entry_d (v 18) u' j ∧
            Tg_reply_d I p.ω (v 7) (v 8) κ (w 15).val U' D' (w 12).val u' (w 11).val (v 20) s (v 22)
              ⟨(w 2).val, (w 1).val, (w 0).val⟩ ∧
            Rd_entry_d η η' j ∧ Rd_entry_d C C' j ∧ Tg_context_d p.ω N η' C' ∧
            Tg_reply_in_d p.ω (v 7) (v 8) κ (w 15).val U' D' (w 12).val u' (w 11).val (v 20) (v 22)
              (w 2).val (w 1).val (w 0).val s C' ∧
            M.mem W X ∧ M.mem W C ∧ Vr_d X ℓ W ∧ Er_level_d N ℓ W ∧ M.mem (w 12).val W ∧ M.mem (w 11).val W ∧
            (∀ μ, M.mem μ ℓ → Ea_agree_d p.ω μ X N) ∧
            It_map_d D p.e p.e π ∧ Rd_entry_d C C π ∧ M.mem p.ω (v 14) ∧
            Tg_anchor_d (v 5) (v 14) X π ∧ Tg_anchor_d (v 5) (v 14) X id ∧ Tg_anchor_d (v 5) (v 14) N j ∧
            ∃ r', Rd_entry_d r r' j ∧ Rt_record_in_d tg_control0_m C' r' ∧
            ∃ nv : Nonempty {x // M.mem x C'}, ∃ ρ' : Env (rt_model_l C' nv) 19,
              (∀ i, Rd_entry_d (ρ.bound i).val (ρ'.bound i).val j) ∧ Formula.satisfies ρ' tg_control0_m ∧
              (∃ θ' f, M.mem θ' C' ∧ M.mem f C' ∧ Cg_rank_d (ρ'.bound 0).val (ρ'.bound 12).val (ρ'.bound 18).val θ' f) ∧
              ∃ h' : (rt_model_l C' nv).Domain, Rd_entry_d h.val h'.val j ∧
                Fn0_d p.a (ρ'.bound 12).val h'.val ∧ M.mem h'.val (ρ'.bound 18).val ∧
                ∃ ζ : Env (rt_model_l C' nv) 46,
                  (∀ i, Rd_entry_d ((tg_issued_start_env_d ρ ε a h ℓ₀ (ρ.bound 2)).bound i).val (ζ.bound i).val j) ∧
                  Formula.satisfies ζ tg_issued0_m ∧
                  ∃ v t q : (rt_model_l C' nv).Domain, KPair_d M v.val (w 15).val (w 11).val ∧
                    Formula.satisfies (tg_position_env_d
                      ⟨fun i => ζ.bound (i.castAdd 27), fun _ => ζ.bound 0⟩ (ζ.bound 19) t q) (tg_position0_m 2) ∧
                    Formula.satisfies (⟨fun i => [ζ.bound 0, t, ζ.bound 20, v].get i, fun _ => v⟩ :
                      Env (rt_model_l C' nv) 4)
                      (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
                    let ψ := tg_position_env_d
                      (⟨fun i => ζ.bound (i.castAdd 27), fun _ => ζ.bound 0⟩ : Env (rt_model_l C' nv) 19) (ζ.bound 19) t q
                    ∀ x, (rt_model_l C' nv).mem x (ψ.bound 6) → ∃ v' t' j' n',
                      (rt_model_l C' nv).mem v' (ψ.bound 6) ∧
                      (Formula.satisfies ψ (gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) → v' = x) ∧
                      (¬ Formula.satisfies ψ (gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) →
                        Rd_entry_d (ψ.bound 20) v' (ψ.bound 17)) ∧
                      Formula.satisfies (⟨fun i => [ψ.bound 0, t', ψ.bound 20, v'].get i, fun _ => v'⟩ : Env (rt_model_l C' nv) 4)
                        (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
                      (rt_model_l C' nv).SuccessorOf n' (ψ.bound 19) ∧
                      Formula.satisfies (tg_position_env_d ⟨fun i => ψ.bound (i.castAdd 3), fun _ => ψ.bound 0⟩ n' t' j')
                        (tg_position0_m 0) ∧
                      ∃ ε' : Env (rt_model_l C' nv) 46, (∀ i : Fin 19, ε'.bound (i.castAdd 27) = ψ.bound (i.castAdd 3)) ∧
                        ε'.bound 19 = n' ∧ Formula.satisfies ε' tg_issued0_m ∧ Rd_entry_d t' (ε'.bound 21) (ψ.bound 17) ∧
                        Formula.satisfies (⟨fun i => [ψ.bound 0, ε'.bound 20, t', ε'.bound 21].get i,
                          fun _ => ε'.bound 21⟩ : Env (rt_model_l C' nv) 4)
                          (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) := by
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
    hU, hD, hu, reply, iη, iC, context', legal, hW, hWC, common, level, hQW, hwW, agreement, _, π₂, root₂, _, anchor₂⟩ := step
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
  exact ⟨H, r, θ, X, R, c, K, η, C, regular, rank, code, source, context, record, nc, ρ, valid, eqρ,
    a, h, value, fn, next, event, ε, seed, hw, he, hd, hS, hν, hk, congrArg Subtype.val hb, hs, ht, hg,
    move, elastic, program, limit₀, letters, ℓ₀, issued, w, round, α, β, γ, T', Q', D', E', L', id, c', j, N, R', K', ℓ, F, κ, U', D'', u', η', C', W, π,
    hα, pad.1, ext.1, result, ext.2.2.1 p.e c oldRoot, ext.2.2.1 α c hc₁,
    (ext.2.2.2.1 p.e α id pad.1.predecessor_mem).mpr edge₁, idFixed, empty₂, target, edge, mn, ready,
    ultra, critical, limit, bound, subset, heights, hU, hD, hu, reply, iη, iC, context', legal,
    hW, hWC, common, level, hQW, hwW, agreement, self₂, iRoot, hwB, anchor, anchor₁, anchor₂,
    r', ir, record', nv, ρ', images, valid'.mp valid,
    tg_control_rank_l (ZF.modelsKP hZF) fs'.transitive nv ρ' (valid'.mp valid),
    ⟨h', hh'⟩, ih, fn', next', ζ, carried, issued'.mp issued, response⟩

end YesMetaZFC.SetTheory.LargeCardinal
