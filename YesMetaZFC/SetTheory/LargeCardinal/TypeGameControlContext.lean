import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlMove
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameContext
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative

/-! # 原获胜策略的实际反射初值

控制记录与更新核同时进入同一个有限反射层。原参数和原策略仍是记录的
实际坐标；后继层只搬运这份记录及其所属集合，不重新选择策略。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_game_d.control_context_l
    {p : Tg_params_d M.Domain} {A F L G J B W O Z g σ : M.Domain}
    (game : Tg_game_d hZFC p A F L G J B W O Z g) (woodin : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I false p.ω A F J B W σ) :
    ∃ H r θ X R c K η C,
      M.IsRegularCardinal I θ ∧ V_d I θ X ∧ Smem_d I c X R ∧
      Ic_model_d hZF p.ω p.ω K X R ∧ Tg_context_d p.ω X η C ∧
      Rt_record_in_d tg_control0_m C r ∧
      let v : Fin 19 → M.Domain := fun i =>
        [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, A, F, L, G, J, σ, H].get i
      Rt_tuple_d v r ∧ ∃ nc : Nonempty {x // M.mem x C}, ∃ ρ : Env (rt_model_l C nc) 19,
        (∀ i, (ρ.bound i).val = v i) ∧ Formula.satisfies ρ tg_control0_m := by
  obtain ⟨H, r, tuple, _, valid⟩ := game.control_l hZFC woodin root win
  let φ : Formula 1 1 := rt_record_m tg_control0_m .newest
  have hc : φ.FreeClosed := rt_record_closed_l _ _ tg_control0_closed_l rfl
  obtain ⟨θ, X, R, c, K, η, C, regular, rank, model, source, context, hr, reflect⟩ :=
    tg_context_l hZFC game.setup.omega r [⟨1, φ, hc⟩]
  have reflected := (reflect ⟨1, φ, hc⟩ (List.mem_cons_self ..)
    ((⟨Fin.elim0, fun _ => p.ω⟩ : Env M 0).push r) (Fin.cases hr (fun i => Fin.elim0 i))).mp valid
  have record : Rt_record_in_d tg_control0_m C r := by
    apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨hr, ?_⟩
    exact (Formula.closed_env_l _ (lr_rel_closed_l φ hc .newest (fun i => .bound i.succ)
      rfl (fun _ => rfl)) (ρ := ((⟨Fin.elim0, fun _ => p.ω⟩ : Env M 0).push r).push C)
      (η := ⟨Fin.cases C (fun _ => r), fun _ => C⟩)
      (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))).mp reflected
  let nc : Nonempty {x // M.mem x C} := ⟨⟨p.ω, context.omega⟩⟩
  obtain ⟨_, v, code, valid⟩ := (rt_record_in_read_l hZF tg_control0_m tg_control0_closed_l
    (context.read_l hZF source.source).1.transitive nc).mp record
  have eq := rt_tuple_inj_l code tuple
  exact ⟨H, r, θ, X, R, c, K, η, C, regular, rank, model, source, context, record, tuple,
    nc, ⟨v, fun _ => v 0⟩, congrFun eq, valid⟩

end YesMetaZFC.SetTheory.LargeCardinal
