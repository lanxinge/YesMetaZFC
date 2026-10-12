import YesMetaZFC.SetTheory.LargeCardinal.TypeGameStages
import YesMetaZFC.SetTheory.Descriptive.ClosedDeterminacy

/-! # 完整辅助闭博弈的决定性

直接对已经装配的三阶段游戏应用闭博弈定理，返回原策略空间中的获胜策略。
本结论确定有一方获胜；5.15 将 II 的策略从辅助博弈转到原博弈，仍待完成。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_game_d.determined_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g : M.Domain}
    (game : Tg_game_d hZFC p X F L G J B W O Z g) :
    ∃ b : Bool, ∃ σ, M.mem σ Z ∧ Cg_win_d I b p.ω X F J B W σ := by
  have heω := num_mem_l hZF.1 game.setup.omega (show Num_d 0 p.e from game.setup.empty)
  have heX := ZF.v_transitive_l I hZF game.setup.rank p.ω
    (ZF.v_ordinal_mem_l I hZF game.setup.rank game.setup.above) p.e heω
  have sub : M.MemberSubset W B := by
    obtain ⟨_, _, _, _, body⟩ := game.payoff
    exact fun f hf => ((body f).mp hf).1
  rcases cg_closed_det_l hZFC game.setup.omega game.histories.1 game.runs heX sub game.complement game.closed with
    ⟨σ, win⟩ | ⟨σ, win⟩
  · exact ⟨true, σ, (game.strategies σ).mpr (fn0_function_l (ZF.modelsKP hZF) win.1), win⟩
  · exact ⟨false, σ, (game.strategies σ).mpr (fn0_function_l (ZF.modelsKP hZF) win.1), win⟩

end YesMetaZFC.SetTheory.LargeCardinal
