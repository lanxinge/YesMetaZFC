import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlContext
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlRead
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnchor

/-! # 从 II 原策略直接构造有限递归的迭代根

首个辅助走法、实际重置输入、工作模型、控制记录和锚点同时产生。
原字母表位于首个临界点以下；没有外加的首轮类型或分支选择参数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_game_d.root_l {p : Tg_params_d M.Domain} {A F L G J B W O Z g σ : M.Domain}
    (game : Tg_game_d hZFC p A F L G J B W O Z g) (woodin : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I false p.ω A F J B W σ) :
    ∃ H r θ X R c K η C, M.IsRegularCardinal I θ ∧ V_d I θ X ∧ Smem_d I c X R ∧
      Ic_model_d hZF p.ω p.ω K X R ∧ Tg_context_d p.ω X η C ∧ Rt_record_in_d tg_control0_m C r ∧
      ∃ nc : Nonempty {x // M.mem x C}, ∃ ρ : Env (rt_model_l C nc) 19,
        Formula.satisfies ρ tg_control0_m ∧
        (∀ i, (ρ.bound i).val = [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, A, F, L, G, J, σ, H].get i) ∧
        ∃ a h : (rt_model_l C nc).Domain, Rd_entry_d p.e a.val σ ∧ Fn0_d p.a A h.val ∧ M.mem h.val H ∧
        Formula.satisfies (⟨fun i => [ρ.bound 4, ρ.bound 1, ρ.bound 1, h, a].get i, ρ.free⟩ : Env (rt_model_l C nc) 5)
          (tg_event_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)) ∧
        ∃ ε : Env (rt_model_l C nc) 38, Formula.satisfies ε tg_seed0_m ∧
          (ε.bound 0).val = p.ω ∧ (ε.bound 1).val = p.e ∧ (ε.bound 2).val = p.δ ∧
          (ε.bound 3).val = p.S ∧ (ε.bound 4).val = p.ν ∧ (ε.bound 6).val = p.e ∧
          ε.bound 23 = ε.bound 5 ∧ (ε.bound 24).val = p.e ∧ (ε.bound 25).val = p.e ∧ (ε.bound 26).val = p.e ∧
          (∃ ℓ, Tg_aux_data_d a ℓ (ε.bound 25) (ε.bound 5) (ε.bound 18)) ∧
          Tg_ee_data_d (ρ.bound 9) (ε.bound 5) (ε.bound 7) (ε.bound 14) (ε.bound 15) (ε.bound 16)
            ⟨ε.bound 27, ε.bound 28, ε.bound 29, ε.bound 30⟩ ∧
          Tg_program_data_d (ρ.bound 10) (ε.bound 7) (ε.bound 20) (ε.bound 22)
            (Fin.cases (ε.bound 31) (Fin.cases (ε.bound 32) (Fin.cases (ε.bound 33) (Fin.cases (ε.bound 34)
              (Fin.cases (ε.bound 35) (Fin.cases (ε.bound 36) (fun _ => ε.bound 37))))))) ∧
          M.IsLimitOrdinal (ε.bound 5).val ∧ M.mem p.A (ε.bound 14).val ∧
          ∃ α T Q D π, M.SuccessorOf α p.e ∧ It_pnice_d hZF p.ω c α T Q D p.e p.e ∧
            Rd_entry_d p.e c Q ∧ It_map_d D p.e p.e π ∧ Rd_entry_d C C π ∧
            Tg_anchor_d (ε.bound 5).val (ε.bound 14).val X π ∧
            ∃ ℓ, Formula.satisfies (tg_issued_start_env_d ρ ε a h ℓ (ρ.bound 2)) tg_issued0_m := by
  obtain ⟨H, r, θ, X, R, c, K, η, C, regular, rank, code, source, context, record, _, nc, ρ, eqρ, valid⟩ :=
    game.control_context_l hZFC woodin root win
  have fs := (context.read_l hZF source.source).1
  let Q := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  obtain ⟨a, h, j, _, value, _, _, succ, fn, next, _, event, v, seed, hw, he, hd, hS, hν, hk, hb, hs, ht, hg, move, elastic, program, letters,
    ℓ, issued⟩ :=
    tg_control_start_l Q ext ρ valid
  let ε : Env (rt_model_l C nc) 38 := ⟨v, ρ.free⟩
  have event : Formula.satisfies
      (⟨fun i => [ρ.bound 4, ρ.bound 1, ρ.bound 1, h, a].get i, ρ.free⟩ : Env (rt_model_l C nc) 5)
      (tg_event_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)) :=
    (tg_event_sat_l Q ext ..).mpr event
  have hρe : (ρ.bound 1).val = p.e := eqρ 1
  have hρA : (ρ.bound 12).val = A := eqρ 12
  have hρσ : (ρ.bound 17).val = σ := eqρ 17
  have hρH : (ρ.bound 18).val = H := eqρ 18
  have hρB : (ρ.bound 6).val = p.A := eqρ 6
  have value := (rt_entry_l fs.transitive nc hZF.1 (ρ.bound 1) a (ρ.bound 17)).mp value
  have value : Rd_entry_d p.e a.val σ := hρe ▸ hρσ ▸ value
  have sj := (rt_successor_l fs.transitive nc hZF.1 j (ρ.bound 1)).mp succ
  have ej : j.val = p.a := (show M.SuccessorOf j.val p.e from hρe ▸ sj).eq hZF.1 game.setup.one
  have ej' : j = ρ.bound 2 := Subtype.ext (ej.trans (eqρ 2).symm)
  let ι : Env (rt_model_l C nc) 3 := ⟨Fin.cases j (Fin.cases (ρ.bound 12) (fun _ => h)), ρ.free⟩
  have fn := (fn0_sat_l hZF.1 _ (.bound 0) (.bound 1) (.bound 2)).mp
    ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2)) ι).mp
      ((fn0_sat_l ext ι (.bound 0) (.bound 1) (.bound 2)).mpr fn))
  have fn : Fn0_d p.a A h.val := ej ▸ hρA ▸ fn
  have next : M.mem h.val H := hρH ▸ next
  have letters : M.mem p.A (v 14).val := hρB ▸ letters
  have facts := seed
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff] at facts
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, language, _⟩ := facts
  let pick : Fin 10 → Term 38 := fun i => [.bound 0, .bound 5, .bound 7, .bound 14, .bound 15,
    .bound 16, .bound 27, .bound 28, .bound 29, .bound 30].get i
  let ζ := Definitional.Env.substitute ε pick
  have language : Formula.satisfies ζ ee_language0_m := (Formula.satisfies_bind ε pick ee_language0_m).mp language
  simp only [ee_language0_m, Formula.satisfies_conj_iff] at language
  have limit := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (v 5)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1)
  have inner := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ζ (.bound 1) (.bound 3)).mp language.2.2.1
  have hκ := source.source.transitive C context.member (v 5).val (v 5).property
  have hB := source.source.transitive C context.member (v 14).val (v 14).property
  have relative := context.rank.of_rank_l hZF source.source.transitive context.member (v 14).property inner
  obtain ⟨o, α, T, Q₀, D, ho, ha, tree⟩ := it_nice_root_l hZF ⟨X, R, K, code, source.source⟩
  have eo := hZF.1.eq_of_same_members o p.e (fun z => iff_of_false (ho z) (game.setup.empty z))
  subst o
  have hc := tree.tree.root p.e game.setup.empty
  obtain ⟨π, self, fixed, anchor⟩ := tree.tree.diagram.anchor_root_l hZF hc code source.source.transitive hκ hB relative
  exact ⟨H, r, θ, X, R, c, K, η, C, regular, rank, code, source, context, record, nc, ρ, valid, eqρ,
    a, h, value, fn, next, event, ε, seed, (congrArg Subtype.val hw).trans (eqρ 0),
    (congrArg Subtype.val he).trans (eqρ 1), (congrArg Subtype.val hd).trans (eqρ 5),
    (congrArg Subtype.val hS).trans (eqρ 7), (congrArg Subtype.val hν).trans (eqρ 8),
    (congrArg Subtype.val hk).trans (eqρ 1), hb, (congrArg Subtype.val hs).trans (eqρ 1),
    (congrArg Subtype.val ht).trans (eqρ 1), (congrArg Subtype.val hg).trans (eqρ 1),
    move, elastic, program, limit, letters, α, T, Q₀, D, π, ha, tree.toIt_pnice_d, hc, self, fixed C context.member, anchor,
    ℓ, ej' ▸ issued⟩

end YesMetaZFC.SetTheory.LargeCardinal
