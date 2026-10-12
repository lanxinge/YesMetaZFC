import YesMetaZFC.SetTheory.LargeCardinal.TypeGame

/-! # 完整博弈的自动阶段读取

从任意内部自然数时刻恢复唯一轮号和阶段，再同时读出责任玩家及该步规则。
因此不存在漏掉的内部时刻，尤其不依赖 ω 在外部标准。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_game_d.stage_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g i : M.Domain}
    (game : Tg_game_d hZFC p X F L G J B W O Z g) (hi : M.mem i p.ω) :
    ∃ n r, M.mem n p.ω ∧ M.IsOrdinalDivision I i p.c n r ∧ (r = p.e ∨ r = p.a ∨ r = p.b) ∧
      (M.mem i J ↔ r = p.a ∨ r = p.b ∧ Gm_even_d I p.ω n) ∧
      (∀ h v, Tg_step_d hZF p i h v ↔
        (r = p.e ∧ Tg_aux_d hZF p n h v) ∨ (r = p.a ∧ Tg_answer_d hZF p n h v) ∨ (r = p.b ∧ M.mem v p.A)) ∧
      ∀ n' r', M.IsOrdinalDivision I i p.c n' r' → n' = n ∧ r' = r := by
  obtain ⟨hc, n, r, hn, div, phase, unique⟩ := tg_clock_l hZF game.setup.omega game.setup.empty
    game.setup.one game.setup.two game.setup.three hi
  have ord := game.setup.omega.members_areOrdinals hZF
  exact ⟨n, r, hn, div, phase, game.owner.read_l hZF (game.setup.omega.isOrdinal hZF) (ord p.c hc)
    ⟨p.b, game.setup.three.predecessor_mem⟩ hi hn div,
    fun _ _ => tg_step_read_l hZF (ord i hi) (ord p.c hc) ⟨p.b, game.setup.three.predecessor_mem⟩ hn div, unique⟩

end YesMetaZFC.SetTheory.LargeCardinal
