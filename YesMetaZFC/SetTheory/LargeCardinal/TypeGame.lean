import YesMetaZFC.SetTheory.LargeCardinal.TypeGameSetup
import YesMetaZFC.SetTheory.Descriptive.ScheduledGame
import YesMetaZFC.SetTheory.Descriptive.FirstViolationMinimum

/-! # Neeman 5.13 的完整辅助闭博弈

由原数学输入构造固定语言、全部内部有限历史、七条规则、三阶段归属和
闭收益集合。返回的四元组是模型内的游戏码；策略空间也由模型内幂集构造。
本层装配游戏；决定性见 TypeGameDeterminacy，5.15 的迭代论证仍待完成。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Tg_game_d (p : Tg_params_d M.Domain) (X F L G J B W O Z g : M.Domain) : Prop where
  setup : Tg_setup_d hZFC p X
  histories : Tg_histories_d hZF p X F L
  legal : Cg_legal_d F L G
  legal_tree : Tree_d F G
  owner : Tg_owner_d hZF p.ω p.c p.a p.b J
  runs : M.IsFunctionSpace I B p.ω X
  strategies : M.IsFunctionSpace I Z F X
  code : Rd_quad_d g X J F W
  payoff : Cg_payoff_d p.ω X F L J B W
  complement : ∀ f, M.mem f O ↔ M.mem f B ∧ ¬ M.mem f W
  closed : Open_d F B O

/-- 固定参数的实际实例直接装配成模型内闭博弈，不留下策略或代码表占位参数。 -/
theorem tg_assemble_l {p : Tg_params_d M.Domain} {X : M.Domain} (setup : Tg_setup_d hZFC p X) :
    ∃ F L G J B W O Z g, Tg_game_d hZFC p X F L G J B W O Z g := by
  obtain ⟨F, L, histories⟩ := tg_histories_l hZF p setup.omega
  obtain ⟨G, legal, tree⟩ := cg_legal_l (ZF.modelsKP hZF) F L
  obtain ⟨J, owner⟩ := tg_owner_l hZF p.ω p.c p.a p.b
  obtain ⟨B, runs⟩ := ZF.exists_functionSpace hZF I p.ω X
  obtain ⟨Z, strategies⟩ := ZF.exists_functionSpace hZF I F X
  obtain ⟨W, O, payoff, complement, closed⟩ := cg_payoff_l hZF p.ω X F L J B
  obtain ⟨g, code⟩ := rd_quad_exists_l (ZF.modelsKP hZF) X J F W
  exact ⟨F, L, G, J, B, W, O, Z, g, setup, histories, legal, tree, owner, runs, strategies, code, payoff, complement, closed⟩

/-- 原输入只有 δ、实数落子字母表 A 与树 S；规范低点和全部表项均自动生成。 -/
theorem tg_game_l {ω δ A S X : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hwδ : M.mem ω δ) (hX : V_d I δ X) (hA : M.mem A X) :
    ∃ p : Tg_params_d M.Domain, ∃ F L G J B W O Z g,
      p.ω = ω ∧ p.δ = δ ∧ p.A = A ∧ p.S = S ∧ Tg_game_d hZFC p X F L G J B W O Z g := by
  obtain ⟨p, hw, hd, ha, hs, setup⟩ := tg_setup_l hZFC (S := S) hω hδ hwδ hX hA
  obtain ⟨F, L, G, J, B, W, O, Z, g, game⟩ := tg_assemble_l hZFC setup
  exact ⟨p, F, L, G, J, B, W, O, Z, g, hw, hd, ha, hs, game⟩

theorem Tg_game_d.empty_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g : M.Domain}
    (game : Tg_game_d hZFC p X F L G J B W O Z g) : M.mem p.e G := by
  have he := game.setup.empty
  have graph := tg_graph_empty_l I he
  have fn : M.IsSetFunctionFromTo I p.e p.e X := ⟨graph.1, graph.2, fun i hi => (he i hi).elim⟩
  have heF := (game.histories.1 p.e).mpr ⟨p.e, num_mem_l hZF.1 game.setup.omega (show Num_d 0 p.e from he), fn⟩
  refine (game.legal p.e).mpr ⟨heF, fun q hq sub => (game.histories.2 q).mpr ⟨hq, Or.inl ?_⟩⟩
  exact fun x hx => he x (sub x hx)

/-- 全部有限轮都遵守七条规则的无限对局，由玩家 I 获胜。 -/
theorem Tg_game_d.legal_run_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g f : M.Domain}
    (game : Tg_game_d hZFC p X F L G J B W O Z g) (hf : M.mem f B)
    (legal : Branch_d F G f) : M.mem f W :=
  game.payoff.all_legal_l hf (fun h hh sub => game.legal.current_l (legal h hh sub))

theorem Tg_game_d.i_violation_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g f h i : M.Domain}
    (game : Tg_game_d hZFC p X F L G J B W O Z g) (hf : M.mem f B) (hh : M.mem h F)
    (sub : M.MemberSubset h f) (turn : M.mem i J) (first : Cg_first_d p.ω X F L i h) : ¬ M.mem f W :=
  (game.payoff.read_l hf).mpr ⟨h, i, hh, sub, turn, first⟩

theorem Tg_game_d.ii_violation_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g f h i : M.Domain}
    (game : Tg_game_d hZFC p X F L G J B W O Z g) (hf : M.mem f B) (hh : M.mem h F)
    (sub : M.MemberSubset h f) (turn : ¬ M.mem i J) (first : Cg_first_d p.ω X F L i h) : M.mem f W :=
  game.payoff.ii_first_l (ZF.modelsKP hZF) (game.setup.omega.isOrdinal hZF) ((game.runs f).mp hf).1 hf hh sub first turn

/-- 对局或处处合法，或有模型内部的最早违规；不存在借用外部 ω 良基性的缺口。 -/
theorem Tg_game_d.classify_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g f : M.Domain}
    (game : Tg_game_d hZFC p X F L G J B W O Z g) (hf : M.mem f B) :
    Branch_d F G f ∨ ∃ i h, M.mem h F ∧ M.MemberSubset h f ∧ Cg_first_d p.ω X F L i h := by
  classical
  by_cases legal : Branch_d F L f
  · exact Or.inl (fun h hh sub => (game.legal h).mpr ⟨hh,
      fun q hq qh => legal q hq (fun x hx => sub x (qh x hx))⟩)
  · apply Or.inr
    apply cg_first_exists_l hZF game.setup.omega game.histories.1 ((game.runs f).mp hf).1
      (fun h hh empty => (game.histories.2 h).mpr ⟨hh, Or.inl empty⟩)
    apply Classical.byContradiction
    intro no
    exact legal (fun h hh sub => Classical.byContradiction (fun bad => no ⟨h, hh, sub, bad⟩))

theorem Tg_game_d.payoff_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g f : M.Domain}
    (game : Tg_game_d hZFC p X F L G J B W O Z g) (hf : M.mem f B) :
    M.mem f W ↔ Branch_d F G f ∨
      ∃ i h, M.mem h F ∧ M.MemberSubset h f ∧ ¬ M.mem i J ∧ Cg_first_d p.ω X F L i h := by
  constructor
  · intro win
    rcases game.classify_l hZFC hf with legal | ⟨i, h, hh, sub, first⟩
    · exact Or.inl legal
    · exact Or.inr ⟨i, h, hh, sub, fun turn => game.i_violation_l hZFC hf hh sub turn first win, first⟩
  · rintro (legal | ⟨i, h, hh, sub, turn, first⟩)
    · exact game.legal_run_l hZFC hf legal
    · exact game.ii_violation_l hZFC hf hh sub turn first

/-- 策略类型有真实的常值实例；定义不把“存在策略”作为额外前提。 -/
theorem Tg_game_d.strategy_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g : M.Domain}
    (game : Tg_game_d hZFC p X F L G J B W O Z g) : ∃ σ, M.mem σ Z := by
  have heω := num_mem_l hZF.1 game.setup.omega (show Num_d 0 p.e from game.setup.empty)
  have heX := ZF.v_transitive_l I hZF game.setup.rank p.ω
    (ZF.v_ordinal_mem_l I hZF game.setup.rank game.setup.above) p.e heω
  obtain ⟨σ, fn, _⟩ := ZF.exists_constantFunction hZF I (source := F) heX
  exact ⟨σ, (game.strategies σ).mpr fn⟩

end YesMetaZFC.SetTheory.LargeCardinal
