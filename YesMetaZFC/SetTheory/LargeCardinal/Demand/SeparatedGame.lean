import YesMetaZFC.SetTheory.LargeCardinal.Demand.Setup
import YesMetaZFC.SetTheory.LargeCardinal.Demand.HistoryConstruction
import YesMetaZFC.SetTheory.Descriptive.Game.ClosedDeterminacy
import YesMetaZFC.SetTheory.Descriptive.Game.FirstViolationMonotone
import YesMetaZFC.SetTheory.Descriptive.Game.GameAttemptRank
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.Model.SetTheory.Demand.ReplyRestore
import YesMetaZFC.Model.SetTheory.Demand.Separated

/-! # Neeman 7.1 的完整辅助闭博弈

由原数学输入构造固定语言、全部内部有限历史、六条规则、三阶段归属和
闭收益集合。返回的四元组是模型内的游戏码；策略空间也由模型内幂集构造。
辅助阶段归 II，回答及偶数轮实数落子归 I；完整策略和闭决定性也由实际游戏构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Td_game_d (p : Tg_params_d M.Domain) (X F L G J B W O Z g : M.Domain) : Prop where
  setup : Td_setup_d hZFC p X
  histories : Td_histories_d hZF p X F L
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
theorem td_assemble_l {p : Tg_params_d M.Domain} {X : M.Domain} (setup : Td_setup_d hZFC p X) :
    ∃ F L G J B W O Z g, Td_game_d hZFC p X F L G J B W O Z g := by
  obtain ⟨F, L, histories⟩ := td_histories_l hZF p setup.omega
  obtain ⟨G, legal, tree⟩ := cg_legal_l (ZF.modelsKP hZF) F L
  obtain ⟨J, owner⟩ := tg_owner_l hZF p.ω p.c p.a p.b
  obtain ⟨B, runs⟩ := ZF.exists_functionSpace hZF I p.ω X
  obtain ⟨Z, strategies⟩ := ZF.exists_functionSpace hZF I F X
  obtain ⟨W, O, payoff, complement, closed⟩ := cg_payoff_l hZF p.ω X F L J B
  obtain ⟨g, code⟩ := rd_quad_exists_l (ZF.modelsKP hZF) X J F W
  exact ⟨F, L, G, J, B, W, O, Z, g, setup, histories, legal, tree, owner, runs, strategies, code, payoff, complement, closed⟩

/-- 原输入只有 δ、实数落子字母表 A 与树 S；规范低点和全部表项均自动生成。 -/
theorem td_game_l {ω δ A S X : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hwδ : M.mem ω δ) (hX : V_d I δ X) (hA : M.mem A X) :
    ∃ p : Tg_params_d M.Domain, ∃ F L G J B W O Z g,
      p.ω = ω ∧ p.δ = δ ∧ p.A = A ∧ p.S = S ∧ Td_game_d hZFC p X F L G J B W O Z g := by
  obtain ⟨p, hw, hd, ha, hs, setup⟩ := td_setup_l hZFC (S := S) hω hδ hwδ hX hA
  obtain ⟨F, L, G, J, B, W, O, Z, g, game⟩ := td_assemble_l hZFC setup
  exact ⟨p, F, L, G, J, B, W, O, Z, g, hw, hd, ha, hs, game⟩

theorem Td_game_d.empty_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g : M.Domain}
    (game : Td_game_d hZFC p X F L G J B W O Z g) : M.mem p.e G := by
  have he := game.setup.empty
  have graph := tg_graph_empty_l I he
  have fn : M.IsSetFunctionFromTo I p.e p.e X := ⟨graph.1, graph.2, fun i hi => (he i hi).elim⟩
  have heF := (game.histories.1 p.e).mpr ⟨p.e, num_mem_l hZF.1 game.setup.omega (show Num_d 0 p.e from he), fn⟩
  refine (game.legal p.e).mpr ⟨heF, fun q hq sub => (game.histories.2 q).mpr ⟨hq, Or.inl ?_⟩⟩
  exact fun x hx => he x (sub x hx)

/-- 全部有限轮都遵守六条规则的无限对局，由玩家 I 获胜。 -/
theorem Td_game_d.legal_run_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g f : M.Domain}
    (game : Td_game_d hZFC p X F L G J B W O Z g) (hf : M.mem f B)
    (legal : Branch_d F G f) : M.mem f W :=
  game.payoff.all_legal_l hf (fun h hh sub => game.legal.current_l (legal h hh sub))

theorem Td_game_d.i_violation_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g f h i : M.Domain}
    (game : Td_game_d hZFC p X F L G J B W O Z g) (hf : M.mem f B) (hh : M.mem h F)
    (sub : M.MemberSubset h f) (turn : M.mem i J) (first : Cg_first_d p.ω X F L i h) : ¬ M.mem f W :=
  (game.payoff.read_l hf).mpr ⟨h, i, hh, sub, turn, first⟩

theorem Td_game_d.ii_violation_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g f h i : M.Domain}
    (game : Td_game_d hZFC p X F L G J B W O Z g) (hf : M.mem f B) (hh : M.mem h F)
    (sub : M.MemberSubset h f) (turn : ¬ M.mem i J) (first : Cg_first_d p.ω X F L i h) : M.mem f W :=
  game.payoff.ii_first_l (ZF.modelsKP hZF) (game.setup.omega.isOrdinal (ZF.modelsKP hZF)) ((game.runs f).mp hf).1 hf hh sub first turn

/-- 对局或处处合法，或有模型内部的最早违规；不存在借用外部 ω 良基性的缺口。 -/
theorem Td_game_d.classify_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g f : M.Domain}
    (game : Td_game_d hZFC p X F L G J B W O Z g) (hf : M.mem f B) :
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

theorem Td_game_d.payoff_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g f : M.Domain}
    (game : Td_game_d hZFC p X F L G J B W O Z g) (hf : M.mem f B) :
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
theorem Td_game_d.strategy_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g : M.Domain}
    (game : Td_game_d hZFC p X F L G J B W O Z g) : ∃ σ, M.mem σ Z := by
  have heω := num_mem_l hZF.1 game.setup.omega (show Num_d 0 p.e from game.setup.empty)
  have heX := v_transitive_l I game.setup.rank p.ω
    (ZF.v_ordinal_mem_l I hZF game.setup.rank game.setup.above) p.e heω
  obtain ⟨σ, fn, _⟩ := ZF.exists_constantFunction hZF I (source := F) heX
  exact ⟨σ, (game.strategies σ).mpr fn⟩

/-- 每个内部时刻实际读出唯一轮号、阶段与责任玩家，无外部标准性前提。 -/
theorem Td_game_d.stage_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g i : M.Domain}
    (game : Td_game_d hZFC p X F L G J B W O Z g) (hi : M.mem i p.ω) :
    ∃ n r, M.mem n p.ω ∧ M.IsOrdinalDivision I i p.c n r ∧ (r = p.e ∨ r = p.a ∨ r = p.b) ∧
      (M.mem i J ↔ r = p.a ∨ r = p.b ∧ Gm_even_d I p.ω n) ∧
      (∀ h v, Td_step_d hZF p i h v ↔
        (r = p.e ∧ Td_aux_d hZF p n h v) ∨ (r = p.a ∧ Td_answer_d hZF p n h v) ∨
          (r = p.b ∧ M.mem v p.A)) ∧
      ∀ n' r', M.IsOrdinalDivision I i p.c n' r' → n' = n ∧ r' = r := by
  obtain ⟨hc,n,r,hn,div,phase,unique⟩ := tg_clock_l hZF game.setup.omega game.setup.empty
    game.setup.one game.setup.two game.setup.three hi
  have ord := game.setup.omega.members_areOrdinals (ZF.modelsKP hZF)
  exact ⟨n,r,hn,div,phase,game.owner.read_l hZF (game.setup.omega.isOrdinal (ZF.modelsKP hZF)) (ord p.c hc)
    ⟨p.b,game.setup.three.predecessor_mem⟩ hi hn div,
    fun _ _ => td_step_read_l hZF (ord i hi) (ord p.c hc) ⟨p.b,game.setup.three.predecessor_mem⟩ hn div,unique⟩

/-- 任一实际胜策产生其合法有限历史控制集；控制对象没有预先假设。 -/
theorem Td_game_d.control_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g σ : M.Domain} {b : Bool}
    (game : Td_game_d hZFC p X F L G J B W O Z g) (win : Cg_win_d I b p.ω X F J B W σ) :
    ∃ H, Cg_control_d I b p.ω p.e X F L G J σ H :=
  cg_control_l hZF game.setup.omega game.setup.empty game.histories.1 game.legal
    (game.empty_l hZFC) game.runs game.payoff win

/-- 闭游戏决定性返回原策略空间中的实际胜策。 -/
theorem Td_game_d.determined_l {p : Tg_params_d M.Domain} {X F L G J B W O Z g : M.Domain}
    (game : Td_game_d hZFC p X F L G J B W O Z g) :
    ∃ b : Bool, ∃ σ, M.mem σ Z ∧ Cg_win_d I b p.ω X F J B W σ := by
  have heω := num_mem_l hZF.1 game.setup.omega (show Num_d 0 p.e from game.setup.empty)
  have heX := v_transitive_l I game.setup.rank p.ω
    (ZF.v_ordinal_mem_l I hZF game.setup.rank game.setup.above) p.e heω
  have sub : M.MemberSubset W B := by
    obtain ⟨_,_,_,_,body⟩ := game.payoff
    exact fun f hf => ((body f).mp hf).1
  rcases cg_closed_det_l hZFC game.setup.omega game.histories.1 game.runs heX sub game.complement game.closed with
    ⟨σ,win⟩ | ⟨σ,win⟩
  · exact ⟨true,σ,(game.strategies σ).mpr (fn0_function_l (ZF.modelsKP hZF) win.1),win⟩
  · exact ⟨false,σ,(game.strategies σ).mpr (fn0_function_l (ZF.modelsKP hZF) win.1),win⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原 demanding 游戏的最弱历史规则证书

三阶段推进只读取自然数时钟、实际末步检查和归属集合。
武丁性、秩层与局部不可分辨参数不作为这些有限历史推理的前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

structure Td_rules_d (hZF : M.Models ZF) (p : Tg_params_d M.Domain) (X F L J : M.Domain) : Prop where
  omega : M.IsOmega p.ω
  empty : ∀ x, ¬ M.mem x p.e
  one : M.SuccessorOf p.a p.e
  two : M.SuccessorOf p.b p.a
  three : M.SuccessorOf p.c p.b
  checks : ∀ h, M.mem h L ↔ M.mem h F ∧ Td_check_d hZF p X h
  owner : Tg_owner_d hZF p.ω p.c p.a p.b J

def td_rules_m {d} (p : Tg_params_d (Term d)) (X F L J : Term d) : Formula 1 d :=
  set[d] ⟪⌜Formula.isOmega⌝ₚ(⌜p.ω⌝ₛ) ∧ ⌜Formula.isEmpty⌝ₚ(⌜p.e⌝ₛ) ∧
    ⌜Formula.isSuccessor⌝ₚ(⌜p.a⌝ₛ,⌜p.e⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜p.b⌝ₛ,⌜p.a⌝ₛ) ∧
    ⌜Formula.isSuccessor⌝ₚ(⌜p.c⌝ₛ,⌜p.b⌝ₛ) ∧
    (∀ h, h ∈ ⌜L⌝ₛ ↔ h ∈ ⌜F⌝ₛ ∧ ⌜fun h => td_check_m (p.map_l Term.weaken) X.weaken h⌝ₚ(h)) ∧
    (∀ i, i ∈ ⌜J⌝ₛ ↔ i ∈ ⌜p.ω⌝ₛ ∧ (∃ n r, n ∈ ⌜p.ω⌝ₛ ∧
      ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(i,⌜p.c⌝ₛ,n,r) ∧
      (r = ⌜p.a⌝ₛ ∨ r = ⌜p.b⌝ₛ ∧ ⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p.ω⌝ₛ,n))))⟫

@[simp] theorem td_rules_closed_l {d} (p : Tg_params_d (Term d)) (X F L J : Term d)
    (hp : p.closed_l) (hX : X.freeSupport = []) (hF : F.freeSupport = [])
    (hL : L.freeSupport = []) (hJ : J.freeSupport = []) : (td_rules_m p X F L J).FreeClosed := by
  have hc := td_check_closed_l (p.map_l Term.weaken) X.weaken .newest (p.weaken_closed_l hp)
    (by simpa using hX) rfl
  rcases hp with ⟨hw,he,ha,hb,hc',_⟩
  simp -implicitDefEqProofs [td_rules_m,Definitional.Formula.FreeClosed,hw,he,ha,hb,hc',hF,hL,hJ,hc]

theorem td_rules_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X F L J : Term d) :
    Formula.satisfies ρ (td_rules_m p X F L J) ↔ Td_rules_d hZF (p.map_l (fun t => t.eval ρ))
      (X.eval ρ) (F.eval ρ) (L.eval ρ) (J.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [td_rules_m,Formula.satisfies_conj_iff,Formula.satisfies_isOmega_iff,
    Formula.satisfies_isEmpty_iff,Formula.satisfies_isSuccessor_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,td_check_sat_l hZF,Formula.satisfies_exists_iff,
    Formula.satisfies_isOrdinalDivision_iff I hZF.1,Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,gm_even_sat_l I hZF.1,
    Tg_params_d.map_l,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d,e,f,g⟩ => ⟨a,b,c,d,e,f,g⟩,
    fun h => ⟨h.omega,h.empty,h.one,h.two,h.three,h.checks,h.owner⟩⟩

theorem Td_game_d.rules_l (hZFC : M.Models ZFC)
    {p : Tg_params_d M.Domain} {X F L G J B W O Z g : M.Domain}
    (game : Td_game_d hZFC p X F L G J B W O Z g) :
    Td_rules_d (ZFC.models_zf_l hZFC) p X F L J :=
  ⟨game.setup.omega,game.setup.empty,game.setup.one,game.setup.two,game.setup.three,
    game.histories.2,game.owner⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原回答实际追加到 II 胜策的同一历史

回答属于走法域由原固定查询行的完整池与秩界自动给出。
随后只用时钟、末步检查与实际控制集完成追加，不向历史推理输入武丁性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

section Member
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_setup_d.answer_member_l {p : Tg_params_d M.Domain} {X n h v : M.Domain}
    (setup : Td_setup_d hZFC p X) (answer : Td_answer_d hZF p n h v) : M.mem v X := by
  obtain ⟨a,ℓ,k,κ,u,τ,w,d,q,N,m,B,U,E,g₀,g₁,g₂,g₃,C,V,Du,Dw,pn,pm,pp,pb,ph,b,z,
    s₀,s₁,s₂,s₃,s₄,s₅,s₆,_,_,pair,_,_,below,request,query,_,reply⟩ := answer
  obtain ⟨d',q',n',m',arity,rank,constants,_,pool,_⟩ := setup.queries.read_l hZFC below request query
  obtain ⟨d₀,q₀,n₀,m₀,arity₀,_,_,_,hm⟩ := td_arity_exists_l hZF setup.omega request.2.1
  have em := (arity₀.unique_l hZF arity).2.2.2
  have hV := tt_constants_rank_l hZF setup.rank setup.limit below rank constants
  have hDw := pool.rank_mem_l (ZF.modelsKP hZF) setup.omega setup.rank setup.limit
    (ZF.v_ordinal_mem_l I hZF setup.rank setup.above) (em ▸ hm) hV
  have hw := v_subset_mem_l I setup.rank hDw reply.1
  obtain ⟨v',hv,cp⟩ := (sc_v_algebra_l hZFC setup.limit setup.rank).kpair_l
    (ZF.v_ordinal_mem_l I hZF setup.rank below) hw
  exact kpair_unique_l M hZF.1 cp pair ▸ hv
end Member

section Step
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_rules_d.answer_l {p : Tg_params_d M.Domain} {X F L G J σ R i n h v : M.Domain}
    (rules : Td_rules_d hZF p X F L J)
    (control : Cg_control_d I false p.ω p.e X F L G J σ R)
    (hi : M.mem i p.ω) (hn : M.mem n p.ω) (hh : M.mem h R) (fh : Fn0_d i X h)
    (div : M.IsOrdinalDivision I i p.c n p.a) (answer : Td_answer_d hZF p n h v) (hv : M.mem v X) :
    ∃ t j, Fseq_end_d I p.ω t h v ∧ M.mem j p.ω ∧ M.SuccessorOf j i ∧ Fn0_d j X t ∧ M.mem t R ∧
      M.IsOrdinalDivision I j p.c n p.b ∧ Tg_event_d I p.c n p.a t v := by
  obtain ⟨hc, _⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three hi
  have oc := rules.omega.members_areOrdinals (ZF.modelsKP hZF) p.c hc
  obtain ⟨j, t, hj, ft, endt⟩ := ZF.fseq_end_exists_l I hZF rules.omega hi (fn0_function_l (ZF.modelsKP hZF) fh) hv
  have fn := fn0_of_function_l (ZF.modelsKP hZF) ft
  obtain ⟨m, k, d⟩ := endt
  have ej := d.source.2.2.2.eq hZF.1 ft.2.1
  have ei := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  have succ : M.SuccessorOf j i := ej ▸ ei ▸ d.length_successor
  have endt : Fseq_end_d I p.ω t h v := ⟨m, k, d⟩
  have check := td_check_end_l hZF hj succ fn fh endt ⟨n, p.a, hn, div, Or.inr (Or.inl ⟨rfl, answer⟩)⟩
  have legal := (rules.checks t).mpr ⟨(control.space t).mpr ⟨j, hj, ft⟩, check⟩
  have turn := (rules.owner.read_l hZF (rules.omega.isOrdinal (ZF.modelsKP hZF)) oc ⟨p.b, rules.three.predecessor_mem⟩ hi hn div).mpr (Or.inl rfl)
  exact ⟨t, j, endt, hj, succ, fn, control.step i h v t hi hh hv fh endt (Or.inl ⟨turn, legal⟩),
    tg_division_next_l hZF oc div rules.two succ rules.three.predecessor_mem, i, div, ei ▸ d.last_value⟩

end Step

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def td_answer_control_m {d} (p : Tg_params_d (Term d)) (X R : Term d) : Formula 1 d :=
  let q := p.map_l (fun t => t.weaken.weaken.weaken.weaken)
  set[d] ⟪∀ i ∈ ⌜p.ω⌝ₛ, ∀ n ∈ ⌜p.ω⌝ₛ, ∀ h ∈ ⌜R⌝ₛ, ∀ v,
    ⌜fn0_m⌝ₚ(i, ⌜X⌝ₛ, h) → ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(i, ⌜p.c⌝ₛ, n, ⌜p.a⌝ₛ) →
    ⌜fun n h v => td_answer_m q n h v⌝ₚ(n, h, v) → ∃ t j,
      ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p.ω⌝ₛ, t, h, v) ∧ j ∈ ⌜p.ω⌝ₛ ∧
      ⌜Formula.isSuccessor⌝ₚ(j, i) ∧ ⌜fn0_m⌝ₚ(j, ⌜X⌝ₛ, t) ∧ t ∈ ⌜R⌝ₛ ∧
      ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(j, ⌜p.c⌝ₛ, n, ⌜p.b⌝ₛ) ∧
      ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ, n, ⌜p.a⌝ₛ, t, v)⟫

@[simp] theorem td_answer_control_closed_l {d} (p : Tg_params_d (Term d)) (X R : Term d)
    (hp : p.closed_l) (hX : X.freeSupport = []) (hR : R.freeSupport = []) :
    (td_answer_control_m p X R).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using hp
  have closed := td_answer_closed_l _ (.bound 2) (.bound 1) (.bound 0) hp' rfl rfl rfl
  rcases hp with ⟨hw, _, ha, hb, hc, _⟩
  simp -implicitDefEqProofs [td_answer_control_m, Definitional.Formula.FreeClosed, hw, ha, hb, hc, hX, hR]
  exact closed

theorem td_answer_control_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X F L G J σ R : Term d)
    (setup : Td_setup_d hZFC (p.map_l (fun t => t.eval ρ)) (X.eval ρ))
    (rules : Td_rules_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (F.eval ρ) (L.eval ρ) (J.eval ρ))
    (control : Cg_control_d I false (p.ω.eval ρ) (p.e.eval ρ) (X.eval ρ) (F.eval ρ) (L.eval ρ) (G.eval ρ)
      (J.eval ρ) (σ.eval ρ) (R.eval ρ)) : Formula.satisfies ρ (td_answer_control_m p X R) := by
  simp only [td_answer_control_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, fn0_sat_l hZF.1, Formula.satisfies_isOrdinalDivision_iff I hZF.1,
    td_answer_sat_l hZF, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fseq_end_sat_l I hZF.1, Formula.satisfies_mem_iff, Formula.satisfies_isSuccessor_iff,
    tg_event_sat_l I hZF.1, Tg_params_d.map_l, Definitional.Term.eval_weaken]
  intro i hi n hn h hh v fn div answer
  exact rules.answer_l hZF control hi hn hh fn div answer (setup.answer_member_l hZFC answer)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原 II 胜策实际产生下一 demanding 请求

同一策略在辅助阶段给出实际值，控制集合保证其合法性。
随后从原 Td_check 读取完整两图规则，并保存同一追加历史和时钟。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

theorem Td_rules_d.aux_l (hZF : M.Models ZF) {p : Tg_params_d M.Domain} {X F L G J σ R i n h : M.Domain}
    (rules : Td_rules_d hZF p X F L J) (control : Cg_control_d (kp_pair_l (ZF.modelsKP hZF)) false p.ω p.e X F L G J σ R)
    (hi : M.mem i p.ω) (hn : M.mem n p.ω) (hh : M.mem h R) (fh : Fn0_d i X h)
    (div : M.IsOrdinalDivision (kp_pair_l (ZF.modelsKP hZF)) i p.c n p.e) :
    ∃ a t j, M.mem a X ∧ Rd_entry_d h a σ ∧ Fseq_end_d (kp_pair_l (ZF.modelsKP hZF)) p.ω t h a ∧
      M.mem j p.ω ∧ M.SuccessorOf j i ∧ Fn0_d j X t ∧ M.mem t R ∧
      M.IsOrdinalDivision (kp_pair_l (ZF.modelsKP hZF)) j p.c n p.a ∧ Td_aux_d hZF p n h a ∧
      Tg_event_d (kp_pair_l (ZF.modelsKP hZF)) p.c n p.e t a := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨hc, _⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three hi
  have oc := rules.omega.members_areOrdinals (ZF.modelsKP hZF) p.c hc
  have ne₁ : p.e ≠ p.a := fun eq => rules.empty p.e (eq.symm ▸ rules.one.predecessor_mem)
  have ne₂ : p.e ≠ p.b := fun eq => rules.empty p.a (eq.symm ▸ rules.two.predecessor_mem)
  have turn : ¬ M.mem i J := fun h => ((rules.owner.read_l hZF (rules.omega.isOrdinal (ZF.modelsKP hZF))
    oc ⟨p.b, rules.three.predecessor_mem⟩ hi hn div).mp h).elim ne₁ (fun h => ne₂ h.1)
  have hG := ((control.positions h).mp hh).1
  obtain ⟨a, ha, value⟩ := control.strategy.2.1 h ((control.legal h).mp hG).1
  obtain ⟨j, t, hj, ft, endt⟩ := ZF.fseq_end_exists_l I hZF rules.omega hi (fn0_function_l (ZF.modelsKP hZF) fh) ha
  have next := control.step i h a t hi hh ha fh endt (Or.inr ⟨turn, value⟩)
  have check := ((rules.checks t).mp (control.legal.current_l ((control.positions t).mp next).1)).2
  have step := (td_step_read_l hZF (rules.omega.members_areOrdinals (ZF.modelsKP hZF) i hi)
    oc ⟨p.b, rules.three.predecessor_mem⟩ hn div).mp (check.end_l hZF fh endt)
  have aux := step.elim And.right (fun h => h.elim (fun h => (ne₁ h.1).elim) (fun h => (ne₂ h.1).elim))
  obtain ⟨m, k, d⟩ := endt
  have ej := d.source.2.2.2.eq hZF.1 ft.2.1
  have ei := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  have succ : M.SuccessorOf j i := ej ▸ ei ▸ d.length_successor
  exact ⟨a, t, j, ha, value, ⟨m, k, d⟩, hj, succ,
    fn0_of_function_l (ZF.modelsKP hZF) ft, next,
    tg_division_next_l hZF oc div rules.one succ (oc.transitive p.b rules.three.predecessor_mem p.a rules.two.predecessor_mem),
    aux, i, div, ei ▸ d.last_value⟩

def td_aux_control_m {d} (p : Tg_params_d (Term d)) (X σ R : Term d) : Formula 1 d :=
  let q := p.map_l (fun t => t.weaken.weaken.weaken.weaken.weaken.weaken)
  set[d] ⟪∀ i ∈ ⌜p.ω⌝ₛ, ∀ n ∈ ⌜p.ω⌝ₛ, ∀ h ∈ ⌜R⌝ₛ,
    ⌜fn0_m⌝ₚ(i, ⌜X⌝ₛ, h) → ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(i, ⌜p.c⌝ₛ, n, ⌜p.e⌝ₛ) →
    ∃ a t j, a ∈ ⌜X⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(h, a, ⌜σ⌝ₛ) ∧
      ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p.ω⌝ₛ, t, h, a) ∧ j ∈ ⌜p.ω⌝ₛ ∧
      ⌜Formula.isSuccessor⌝ₚ(j, i) ∧ ⌜fn0_m⌝ₚ(j, ⌜X⌝ₛ, t) ∧ t ∈ ⌜R⌝ₛ ∧
      ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(j, ⌜p.c⌝ₛ, n, ⌜p.a⌝ₛ) ∧
      ⌜fun n h a => td_aux_m q n h a⌝ₚ(n, h, a) ∧ ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ, n, ⌜p.e⌝ₛ, t, a)⟫

@[simp] theorem td_aux_control_closed_l {d} (p : Tg_params_d (Term d)) (X σ R : Term d)
    (hp : p.closed_l) (hX : X.freeSupport = []) (hσ : σ.freeSupport = []) (hR : R.freeSupport = []) :
    (td_aux_control_m p X σ R).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken.weaken.weaken.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using hp
  have hc := td_aux_closed_l _ (.bound 4) (.bound 3) (.bound 2) hp' rfl rfl rfl
  rcases hp with ⟨hw, he, h₁, _, h₃, _⟩
  simp -implicitDefEqProofs [td_aux_control_m, Definitional.Formula.FreeClosed, hw, he, h₁, h₃, hX, hσ, hR]
  exact hc

theorem td_aux_control_l (hZF : M.Models ZF) {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X F L G J σ R : Term d)
    (rules : Td_rules_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (F.eval ρ) (L.eval ρ) (J.eval ρ))
    (control : Cg_control_d (kp_pair_l (ZF.modelsKP hZF)) false (p.ω.eval ρ) (p.e.eval ρ)
      (X.eval ρ) (F.eval ρ) (L.eval ρ) (G.eval ρ) (J.eval ρ) (σ.eval ρ) (R.eval ρ)) :
    Formula.satisfies ρ (td_aux_control_m p X σ R) := by
  simp only [td_aux_control_m, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    fn0_sat_l hZF.1, Formula.satisfies_isOrdinalDivision_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    rd_entry0_sat_l hZF.1, fseq_end_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Formula.satisfies_isSuccessor_iff, td_aux_sat_l hZF, tg_event_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Tg_params_d.map_l, Definitional.Term.eval_weaken]
  intro i hi n hn h hh fn div
  exact rules.aux_l hZF control hi hn hh fn div


end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原 II 策略的实际零轮重置请求

零轮没有可回指的旧轮，故同一策略给出的首个合法请求必有k=0。
首历史、请求、归属和实际四元组一起进入有限公式，供原根反射直接读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

/-- 零轮不可能引用较早轮，因此原策略的首个合法辅助走法必为重置。 -/
theorem Td_rules_d.start_l (hZF : M.Models ZF) {p : Tg_params_d M.Domain} {X F L G J σ R : M.Domain}
    (rules : Td_rules_d hZF p X F L J) (control : Cg_control_d (kp_pair_l (ZF.modelsKP hZF)) false p.ω p.e X F L G J σ R) :
    ∃ a h j, M.mem a X ∧ Rd_entry_d p.e a σ ∧ Fseq_end_d (kp_pair_l (ZF.modelsKP hZF)) p.ω h p.e a ∧
      M.mem j p.ω ∧ M.SuccessorOf j p.e ∧ Fn0_d j X h ∧ M.mem h R ∧
      M.IsOrdinalDivision (kp_pair_l (ZF.modelsKP hZF)) j p.c p.e p.a ∧ Td_aux_d hZF p p.e p.e a ∧
      Tg_event_d (kp_pair_l (ZF.modelsKP hZF)) p.c p.e p.e h a ∧
      ∃ ℓ κ u, Td_move_d a ℓ p.e κ u := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have he := num_mem_l hZF.1 rules.omega (show Num_d 0 p.e from rules.empty)
  obtain ⟨hc, _⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three he
  have oc := rules.omega.members_areOrdinals (ZF.modelsKP hZF) p.c hc
  have ec := oc.transitive p.b rules.three.predecessor_mem p.e
    ((oc.mem rules.three.predecessor_mem).transitive p.a rules.two.predecessor_mem p.e rules.one.predecessor_mem)
  have div : M.IsOrdinalDivision I p.e p.c p.e p.e :=
    ⟨rules.omega.members_areOrdinals (ZF.modelsKP hZF) p.e he, ec, p.e,
      (ZF.ordinalMultiplication_zero_iff hZF I oc rules.empty).mpr rules.empty,
      (ZF.ordinalAddition_zero_iff hZF I rules.empty).mpr rfl⟩
  have fe : Fn0_d p.e X p.e := ⟨fun x hx => (rules.empty x hx).elim,
    fun x hx => (rules.empty x hx).elim, fun x hx => (rules.empty x hx).elim⟩
  obtain ⟨a, h, j, ha, value, endt, hj, succ, fn, next, clock, aux, event⟩ := rules.aux_l hZF control he he control.root fe div
  refine ⟨a, h, j, ha, value, endt, hj, succ, fn, next, clock, aux, event, ?_⟩
  obtain ⟨ℓ,k,κ,u,d,q,N,m,x,s,B,U,Du,Dw,pn,pm,pp,pb,ph,C,V,E,g₀,g₁,g₂,g₃,
    data,_,_,_,_,_,_,_,_,_,_,_,_,branch⟩ := aux
  rcases branch with ⟨eq,_⟩ | ⟨_,old⟩
  · exact ⟨ℓ,κ,u,eq ▸ data⟩
  · exact (rules.empty ℓ old.1).elim

def td_start_control_m {d} (p : Tg_params_d (Term d)) (X σ R : Term d) : Formula 1 d :=
  let q := p.map_l (fun t => t.weaken.weaken.weaken)
  set[d] ⟪∃ a h j, a ∈ ⌜X⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(⌜p.e⌝ₛ,a,⌜σ⌝ₛ) ∧
    ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p.ω⌝ₛ,h,⌜p.e⌝ₛ,a) ∧ j ∈ ⌜p.ω⌝ₛ ∧
    ⌜Formula.isSuccessor⌝ₚ(j,⌜p.e⌝ₛ) ∧ ⌜fn0_m⌝ₚ(j,⌜X⌝ₛ,h) ∧ h ∈ ⌜R⌝ₛ ∧
    ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(j,⌜p.c⌝ₛ,⌜p.e⌝ₛ,⌜p.a⌝ₛ) ∧
    ⌜fun e a => td_aux_m q e e a⌝ₚ(⌜p.e⌝ₛ,a) ∧
    ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ,⌜p.e⌝ₛ,⌜p.e⌝ₛ,h,a) ∧
    (∃ ℓ κ u, ⌜td_move_m⌝ₚ(a,ℓ,⌜p.e⌝ₛ,κ,u))⟫

@[simp] theorem td_start_control_closed_l {d} (p : Tg_params_d (Term d)) (X σ R : Term d)
    (hp : p.closed_l) (hX : X.freeSupport = []) (hσ : σ.freeSupport = []) (hR : R.freeSupport = []) :
    (td_start_control_m p X σ R).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l,Tg_params_d.map_l,Definitional.Term.freeSupport_weaken] using hp
  have he : p.e.weaken.weaken.weaken.freeSupport = [] := by simpa using hp.2.1
  rcases hp with ⟨hw,h₀,h₁,_,h₃,_⟩
  simp -implicitDefEqProofs [td_start_control_m,Definitional.Formula.FreeClosed,hw,h₀,h₁,h₃,hX,hσ,hR]
  exact td_aux_closed_l _ _ _ _ hp' he he rfl

theorem td_start_control_l (hZF : M.Models ZF) {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X F L G J σ R : Term d)
    (rules : Td_rules_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (F.eval ρ) (L.eval ρ) (J.eval ρ))
    (control : Cg_control_d (kp_pair_l (ZF.modelsKP hZF)) false (p.ω.eval ρ) (p.e.eval ρ)
      (X.eval ρ) (F.eval ρ) (L.eval ρ) (G.eval ρ) (J.eval ρ) (σ.eval ρ) (R.eval ρ)) :
    Formula.satisfies ρ (td_start_control_m p X σ R) := by
  simp only [td_start_control_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    rd_entry0_sat_l hZF.1,fseq_end_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Formula.satisfies_isSuccessor_iff,fn0_sat_l hZF.1,td_aux_sat_l hZF,
    Formula.satisfies_isOrdinalDivision_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    tg_event_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,td_move_sat_l hZF.1,
    Tg_params_d.map_l,Definitional.Term.eval_weaken]
  exact rules.start_l hZF control

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从实际游戏回答读取原类型的严格下降

所有查询和程序都由同一开局表恢复。先对齐实际辅助走法、回答和元数，
再删除原 u 的高度槽；原回答的任意排列由既有恢复证明处理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_setup_d.level_reply_l
    {p : Tg_params_d M.Domain}
    {X n h h₁ v v₁ ℓ k κ u d₀ q N m α a b η Y c R B U P r U₁ U₂ ζ : M.Domain}
    (setup : Td_setup_d hZFC p X) (hn : M.mem n p.ω) (fh₁ : M.IsSetFunction I h₁)
    (event : Tg_event_d I p.c n p.e h₁ v)
    (aux : Td_aux_d hZF p n h v) (answer : Td_answer_d hZF p n h₁ v₁)
    (data : Td_move_d v ℓ k κ u) (arity : Td_arity_d I k d₀ q N m)
    (rank : V_d I η Y) (height : M.SuccessorOf η α) (model : Smem_d I c Y R)
    (parameters : V_d I κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (type : Tt_realized_d I p.ω c Y R N r p.δ U P u)
    (root : Rd_entry_d p.e p.S r) (groups : Td_groups_d I p.ω p.e q r a b)
    (fa : Fn0_d k U₁ a) (fb : Fn0_d k U₂ b)
    (tree : Td_tree_d I p.ω p.A p.S) (alphabet : Td_alphabet_d p.S U₁ U₂) (chosen : M.mem ζ U₁) :
    ∃ τ C V W w ν Z c' H s t β r₀ ψ,
      KPair_d M v₁ τ w ∧ M.mem τ p.δ ∧ M.IsLimitOrdinal τ ∧ V_d I τ C ∧
      (∀ x, M.mem x V ↔ M.mem x C ∨ x = τ) ∧ Tt_pool_d I p.ω m V W ∧
      M.mem ν η ∧ V_d I ν Z ∧ Smem_d I c' Z H ∧ Tt_realized_d I p.ω c' Z H m s p.δ V W w ∧
      Rd_entry_d p.e p.S s ∧ Rd_entry_d q t s ∧ Rd_entry_d N β s ∧
      Td_pending_d I p.ω p.A k p.S t ∧ Tg_bound_d I p.δ p.S β ∧ Tg_height_d β ν ∧ M.mem β α ∧
      Td_record_d I p.ω p.e k Z p.S a b t β d₀ q N m r₀ ∧
      M.IsSetBijectionFromTo I ψ m m ∧
      (∀ i j x, Rd_entry_d i j ψ → (Rd_entry_d i x s ↔ Rd_entry_d j x r₀)) := by
  obtain ⟨hc,_⟩ := tg_clock_l hZF setup.omega setup.empty setup.one setup.two setup.three hn
  obtain ⟨ℓ₀,k₀,κ₀,u₀,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,
    parsed,_,hκ,_,_,_,requestκ,_⟩ := aux
  obtain ⟨el,ek,ec,eu⟩ := parsed.unique_l data
  subst ℓ₀ k₀ κ₀ u₀
  obtain ⟨v',ℓ',k',κ',u',τ,w,d',q',N',m',B',U',E,g₀,g₁,g₂,g₃,C,V,Du,W,pn,pm,pp,pb,ph,
    b₀,z,s₀,s₁,s₂,s₃,s₄,s₅,s₆,event',parsed,pair,arity',ee,hτ,request,query,code,reply⟩ := answer
  have ev := event'.unique_l hZF (setup.omega.members_areOrdinals (ZF.modelsKP hZF) p.c hc) fh₁ event
  subst v'
  obtain ⟨el,ek,ec,eu⟩ := parsed.unique_l data
  subst ℓ' k' κ' u'
  obtain ⟨ed,eq,en,em⟩ := arity'.unique_l hZF arity
  subst d' q' N' m'
  have hq := setup.omega.transitive (ZF.modelsKP hZF) N type.finite q arity.2.2.1.predecessor_mem
  have source := setup.elastic.elim fun _ table => table.read_l hZFC hκ hq requestκ.1 ee
  have eb := ZF.v_unique_l I hZF parameters source.rank
  subst B'
  have eu := hZF.1.eq_of_same_members U' U (fun x => (source.constants x).trans (constants x).symm)
  subst U'
  obtain ⟨d',q',N',m',targetArity,hC,cv,_,pool,pendingNode,max,pendingQuery,boundQuery,heightQuery,_⟩ :=
    setup.queries.read_l hZFC hτ request query
  obtain ⟨ed,eq,en,em⟩ := targetArity.unique_l hZF arity
  subst d' q' N' m'
  obtain ⟨_,_,programs,_⟩ := setup.programs
  obtain ⟨a₀,program⟩ := programs.read_l hZFC code
  obtain ⟨sub,t,drop,subtype,qp,qb,qh⟩ := reply
  obtain ⟨r',t',cut,drop',prefixType⟩ := type.dcp_l hZF setup.omega arity.2.2.1 source.pool
  have et := drop'.unique_l I hZF.1 drop
  subst t'
  have old i x (hi : M.mem i q) : Rd_entry_d i x r' ↔ Rd_entry_d i x r :=
    (cut.2 i x).trans ⟨And.right,fun h => ⟨hi,h⟩⟩
  have groups' : Td_groups_d I p.ω p.e q r' a b := by
    constructor
    · intro x
      exact (groups.1 x).trans
        ⟨fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(old i x hi).mpr point⟩,
          fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(old i x hi).mp point⟩⟩
    · intro x
      exact (groups.2 x).trans
        ⟨fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(old i x hi).mpr point⟩,
          fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(old i x hi).mp point⟩⟩
  have heq := (setup.omega.members_areOrdinals (ZF.modelsKP hZF) q hq).empty_mem_of_nonempty
    (ZF.modelsKP hZF) ⟨d₀,arity.2.1.predecessor_mem⟩ setup.empty
  obtain ⟨t₀,pair₀⟩ := (I).total k ζ
  have start : Td_pending_d I p.ω p.A k p.S t₀ := ⟨tree,ζ,pair₀,(alphabet.1 ζ).mp chosen⟩
  obtain ⟨m₀,sm₀,hm₀⟩ := setup.omega.1.2 N type.finite
  have hm : M.mem m p.ω := sm₀.eq hZF.1 arity.2.2.2 ▸ hm₀
  have fna := fn0_function_l (ZF.modelsKP hZF) fa
  have fnb := fn0_function_l (ZF.modelsKP hZF) fb
  obtain ⟨ν,Z,c',H,s,pending,β,r₀,ψ,hν,hZ,lower,actual,rs,rp,rβ,pend,bound,gap,lt,record,perm,points⟩ :=
    td_reply_descend_l hZF setup.omega setup.empty program rank model prefixType height source.limit request.1 hm
      source.rank source.constants hC cv pool sub subtype arity.1 arity.2.1 arity.2.2.1 arity.2.2.2
      ((old p.e p.S heq).mpr root) groups' ⟨fna.1,fna.2.1⟩ ⟨fnb.1,fnb.2.1⟩
      (start.root_l hZF setup.omega setup.empty) ((alphabet.1 ζ).mp chosen)
      pendingQuery boundQuery heightQuery qp qb qh
  exact ⟨τ,C,V,W,w,ν,Z,c',H,s,pending,β,r₀,ψ,pair,hτ,request.1,hC,cv,pool,
    hν,hZ,lower,actual,rs,rp,rβ,pend,bound,gap,lt,record,perm,points⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 以实际不交树开局的 demanding 游戏

先重编码原树，再为同一重编码树构造规范低点和全部游戏表。
树分支由实际解码双射保持，实数坐标不变。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_separated_game_l {ω δ A S X : M.Domain} (hw : M.IsOmega ω)
    (hδ : M.IsLimitOrdinal δ) (hwδ : M.mem ω δ) (rank : V_d I δ X) (hA : M.mem A X)
    (tree : Td_tree_d I ω A S) :
    ∃ e o Y F Y' F' f T U V, ∃ p : Tg_params_d M.Domain, ∃ H L G J B W O Z g,
      e ≠ o ∧ Fseq_space_d I ω Y F ∧ Tree_d F S ∧
      Fseq_space_d I ω Y' F' ∧ Tree_d F' T ∧ M.IsSetBijectionFromTo I f Y' Y ∧
      (∀ x y, Rd_entry_d x y f ↔ M.mem x Y' ∧ Td_tag_d e o x y) ∧
      Td_tree_d I ω A T ∧ Td_separated_d T ∧ Td_alphabet_d T U V ∧
      (∀ z, M.mem z U → ¬ M.mem z V) ∧
      p.ω = ω ∧ p.δ = δ ∧ p.A = A ∧ p.S = T ∧ Td_game_d hZFC p X H L G J B W O Z g ∧
      ∀ a b, M.IsSetFunctionFromTo I a ω Y' → Fseq_recode_d I f a b →
        (Branch_d F' T a ↔ Branch_d F S b) := by
  obtain ⟨e,o,U₀,V₀,T,U,V,ne,_,tree',sep,alphabet,⟨retag⟩⟩ := tree.separate_l hZF hw
  obtain ⟨p,H,L,G,J,B,W,O,Z,g,ew,ed,eA,eT,game⟩ := td_game_l hZFC (S := T) hw hδ hwδ rank hA
  exact ⟨e,o,retag.Y,retag.F,retag.Y',retag.F',retag.f,T,U,V,p,H,L,G,J,B,W,O,Z,g,
    ne,retag.space,retag.source,retag.space',retag.tree_l hZF,retag.map,retag.decode,
    tree',sep,alphabet,sep.alphabet_l alphabet,ew,ed,eA,eT,game,
    fun a b fa ab => retag.branch_l hZF hw fa ab⟩

end YesMetaZFC.SetTheory.LargeCardinal
