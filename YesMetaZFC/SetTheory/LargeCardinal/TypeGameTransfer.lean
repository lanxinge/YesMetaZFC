import YesMetaZFC.SetTheory.LargeCardinal.TypeGameProjection
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameStrategyPlay
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunSequence
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameTreeStep

/-! # Neeman 5.15：辅助博弈 II 策略到原博弈 II 策略

原收益集合是三坐标树体第一投影的补集。响应表在原对局开始前统一选择，
有限前缀确定策略；任意服从该策略的对局由同一递归、奇数返回及三图取并
得到第一坐标恰为该对局的原树分支。因此它不属于 I 的收益集合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}
section Transfer
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 统一构造原有限局面空间、偶数时序、无限对局空间、原收益集合及 II 获胜策略。 -/
theorem Tg_game_d.transfer_l {p : Tg_params_d M.Domain} {X₀ F₀ L₀ G₀ J₀ B₀ W₀ O Z g σ a Y T : M.Domain}
    (game : Tg_game_d hZFC p X₀ F₀ L₀ G₀ J₀ B₀ W₀ O Z g)
    (woodin : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I false p.ω X₀ F₀ J₀ B₀ W₀ σ)
    (ha : M.mem a p.A) (space : Fseq_space_d I p.ω Y T)
    (tree : Tree_d T p.S) : ∃ F J B W τ,
      Fseq_space_d I p.ω p.A F ∧
      M.IsFunctionSpace I B p.ω p.A ∧
      (∀ n, M.mem n J ↔ M.mem n p.ω ∧ Gm_even_d I p.ω n) ∧
      (∀ x, M.mem x W ↔ M.mem x B ∧ ¬ Tg_projection_d hZF p.ω Y T p.S x) ∧
      Cg_win_d I false p.ω p.A F J B W τ := by
  have hw := game.setup.omega
  have ho := game.setup.empty
  obtain ⟨θ,X,R,c,C,γ,V,_,rank,model,limit,hwV,hAV,memS,v,u,run,num,image⟩ := game.run_start_l hZFC woodin root win
  let q : Fin 64 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) v u
  obtain ⟨r,code⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) q
  have initial : Tg_run_code_d hZF p.ω c p.e C γ V p.A p.e r := by
    refine ⟨q,code,?_,num⟩
    simpa only [q,Fin.addCases_left,Fin.addCases_right] using run
  obtain ⟨D,E,K,machine⟩ := initial.choice_l hZFC hw ho limit hwV hAV ⟨q,code,image⟩
  obtain ⟨F,J,B,W,finite,bs,turns,payoff⟩ := tg_projection_game_l hZF hw p.A Y T p.S
  obtain ⟨τ,strategy,values⟩ := machine.strategy_l hZF hw ho ha finite
  refine ⟨F,J,B,W,τ,finite,bs,turns,payoff,strategy,?_⟩
  intro x hx follows bad
  have input := fn0_of_function_l (ZF.modelsKP hZF) ((bs x).mp hx)
  have play : Gm_follows_d I false p.ω τ x := fun n hn odd s cut y ny =>
    follows n hn (fun nj => odd ((turns n).mp nj).2) s cut y ny
  obtain ⟨H,sequence,names,played⟩ := machine.sequence_l hZF hw ho ha finite strategy values input play
  obtain ⟨q,t,u,fn,branch,ft,fu,join⟩ := sequence.branch_l hZFC hw ho rank model memS names played input space tree
  exact ((payoff x).mp bad).2 ⟨q,t,u,fn,branch,ft,fu,join⟩

end Transfer
end YesMetaZFC.SetTheory.LargeCardinal
