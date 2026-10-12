import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlRoot
import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePadding

/-! # 原获胜策略产生带 padding 的实际首轮

原策略的首个合法走法自动给出重置输入。先加恒等边 0→1，再从原偶数根
作超幂 0→2；原控制记录与已经走出的历史也沿这条实际边进入新反射层。
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
              ∃ h' : (rt_model_l C' nv).Domain, Rd_entry_d h.val h'.val j ∧
                Fn0_d p.a (ρ'.bound 12).val h'.val ∧ M.mem h'.val (ρ'.bound 18).val ∧
                ∃ ζ : Env (rt_model_l C' nv) 46,
                  (∀ i, Rd_entry_d ((tg_issued_start_env_d ρ ε a h ℓ₀ (ρ.bound 2)).bound i).val (ζ.bound i).val j) ∧
                  Formula.satisfies ζ tg_issued0_m := by
  obtain ⟨H, r, θ, X, R, c, K, η, C, regular, rank, code, source, context, record, nc, ρ, valid, eqρ,
    a, h, value, fn, next, event, ε, seed, hw, he, hd, hS, hν, hk, hb, hs, ht, hg, move, elastic, program, limit₀, letters,
    α, T, Q, D, π, hα, tree, hc, self, iRoot, anchor, ℓ₀, issued⟩ := game.root_l hZFC woodin root win
  obtain ⟨w, round, β, T₁, Q₁, D₁, E₁, id, π₁, padded, pad, hc₁, edge₁, idFixed, empty,
    root₁, iRoot₁, anchor₁, γ, T', Q', D', E', L', c', j, N, R', K', ℓ, F, κ, U', D'', u', η', C', W,
    result, ext, target, edge, mn, ready, ultra, critical, limit, bound, subset, heights,
    hU, hD, hu, reply, iη, iC, context', legal, hW, hWC, common, level, hQW, hwW, agreement, _, π₂, root₂, _, anchor₂⟩ :=
    context.pad_round_l hZFC nc ε source tree hα hc code hw game.setup.empty self iRoot anchor
      (fun _ hx => hx) (fun _ _ hh => (hh.elim fun z hz => game.setup.empty z hz.2).elim) seed
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
  exact ⟨H, r, θ, X, R, c, K, η, C, regular, rank, code, source, context, record, nc, ρ, valid, eqρ,
    a, h, value, fn, next, event, ε, seed, hw, he, hd, hS, hν, hk, congrArg Subtype.val hb, hs, ht, hg,
    move, elastic, program, limit₀, letters, ℓ₀, issued, w, round, α, β, γ, T', Q', D', E', L', id, c', j, N, R', K', ℓ, F, κ, U', D'', u', η', C', W, π,
    hα, pad.1, ext.1, result, ext.2.2.1 p.e c oldRoot, ext.2.2.1 α c hc₁,
    (ext.2.2.2.1 p.e α id pad.1.predecessor_mem).mpr edge₁, idFixed, empty₂, target, edge, mn, ready,
    ultra, critical, limit, bound, subset, heights, hU, hD, hu, reply, iη, iC, context', legal,
    hW, hWC, common, level, hQW, hwW, agreement, self₂, iRoot, hwB, anchor, anchor₁, anchor₂,
    r', ir, record', nv, ρ', images, valid'.mp valid, ⟨h', hh'⟩, ih, fn', next', ζ, carried, issued'.mp issued⟩

end YesMetaZFC.SetTheory.LargeCardinal
