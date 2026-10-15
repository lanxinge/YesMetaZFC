import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericAvoid
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameDeterminacy

/-! # 6.1 的实际两侧获胜策略

原博弈的 I 收益为三坐标树第一投影的补集。II 分支使用已完成的 5.15；
I 分支构造泛型最小请求策略，并由严格高度矛盾证明每个服从对局属于该补集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

variable (hZFC : M.Models ZFC) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Tg_game_d.generic_transfer_l {p : Tg_params_d M.Domain}
    {X F L G O B W C Z v σ a Γ P Y S Q : M.Domain} {U : M.Domain → Prop} {g : N.Domain}
    (game : Tg_game_d hZFC p X F L G O B W C Z v) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I true p.ω X F O B W σ) (ha : M.mem a p.A) (hw : N.IsOmega (e p.ω))
    (fg : Fn0_d (e p.ω) (e X) g) (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X))
    (space : Fseq_space_d I p.ω Y S) (prod : M.IsCartesianProduct I P p.ω Γ) (letters : M.IsCartesianProduct I Y p.A P)
    (order : ∀ q r, Entry_d M q r Q ↔ M.mem q F ∧ M.mem r F ∧ M.MemberSubset r q)
    (generic : Generic_d M F Q F U)
    (origin : ∀ q, U q → ∀ j y, Rd_entry_d j y q → Rd_entry_d (e j) (e y) g) :
    Tg_projection_win_d hN true (e p.ω) (e p.A) (e Y) (e S) (e p.S) := by
  obtain ⟨F', O', B', W', finite, bs, turns, payoff⟩ := tg_projection_game_l hN hw (e p.A) (e Y) (e S) (e p.S)
  obtain ⟨R, K, D, T, τ, control, scan, strategy, values, runs⟩ :=
    game.generic_strategy_l hZFC hN e hi he hd root win ha hw fg surj finite
  refine ⟨F', O', B', W', τ, finite, bs, turns, payoff, strategy, fun f hf follow => (payoff f).mpr ⟨hf, ?_⟩⟩
  have ff := fn0_of_function_l (ZF.modelsKP hN) ((bs f).mp hf)
  obtain ⟨H, run, _⟩ := runs f ff
  exact game.setup.generic_no_branch_l hZFC hN e hi he hd root game.histories game.owner control ha hw scan surj ff
    (fun s y sy => ((values s y).mp sy).2)
    (fun n hn even s cut y ny => follow n hn ((turns n).mpr ⟨hn, even⟩) s cut y ny)
    run space prod letters order generic origin

/-- 原辅助闭博弈直接给出地 II 或泛型 I 的实际策略，两个收益均为同一树投影。 -/
theorem Tg_game_d.generic_dichotomy_l {p : Tg_params_d M.Domain}
    {X F L G O B W C Z v a Γ P Y S Q : M.Domain} {U : M.Domain → Prop} {g : N.Domain}
    (game : Tg_game_d hZFC p X F L G O B W C Z v) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (ha : M.mem a p.A) (hw : N.IsOmega (e p.ω)) (fg : Fn0_d (e p.ω) (e X) g)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (space : Fseq_space_d I p.ω Y S) (tree : Tree_d S p.S)
    (prod : M.IsCartesianProduct I P p.ω Γ) (letters : M.IsCartesianProduct I Y p.A P)
    (order : ∀ q r, Entry_d M q r Q ↔ M.mem q F ∧ M.mem r F ∧ M.MemberSubset r q)
    (generic : Generic_d M F Q F U)
    (origin : ∀ q, U q → ∀ j y, Rd_entry_d j y q → Rd_entry_d (e j) (e y) g) :
    Tg_projection_win_d hM false p.ω p.A Y S p.S ∨ Tg_projection_win_d hN true (e p.ω) (e p.A) (e Y) (e S) (e p.S) := by
  obtain ⟨b, σ, _, win⟩ := game.determined_l hZFC
  cases b
  · exact Or.inl (game.transfer_l hZFC hd root win ha space tree)
  · exact Or.inr (game.generic_transfer_l hZFC hN e hi he hd root win ha hw fg surj space prod letters order generic origin)

end YesMetaZFC.SetTheory.LargeCardinal
