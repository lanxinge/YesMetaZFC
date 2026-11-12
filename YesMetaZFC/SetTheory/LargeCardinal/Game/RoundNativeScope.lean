import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReply
import YesMetaZFC.SetTheory.Descriptive.Game.ClosedDeterminacy
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.LocalTypeTransportTuple
import YesMetaZFC.SetTheory.Descriptive.Game.FirstViolationMonotone
import YesMetaZFC.SetTheory.LargeCardinal.Types.Renewal
import YesMetaZFC.Model.SetTheory.Game.Graph
import YesMetaZFC.SetTheory.LargeCardinal.Types.OneStepDropImage
import YesMetaZFC.SetTheory.LargeCardinal.Types.ImageSyntax
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.SetTheory.LargeCardinal.Types.PoolRead
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.SetTheory.CumulativeRelativeRestriction

/-! # 全部内部有限历史上的逐步检查

三阶段依原时序组合七条规则。空历史通过检查；非空历史只检查最后一步，
此前是否首次违规由独立的有限证据层判断，因而第二方违规后不会重新开局。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_step_d (p : Tg_params_d M.Domain) (i h v : M.Domain) : Prop := ∃ n r,
  M.mem n p.ω ∧ M.IsOrdinalDivision I i p.c n r ∧
    ((r = p.e ∧ Tg_aux_d hZF p n h v) ∨ (r = p.a ∧ Tg_answer_d hZF p n h v) ∨ (r = p.b ∧ M.mem v p.A))

def tg_step_m {d} (p : Tg_params_d (Term d)) (i h v : Term d) : Formula 1 d :=
  .existsE (.existsE (.conj (.mem (.bound 1) p.ω.weaken.weaken) (.conj
    (Formula.isOrdinalDivision kpair_convention_l i.weaken.weaken p.c.weaken.weaken (.bound 1) .newest)
    (.disj (.conj (Formula.extensionalEq .newest p.e.weaken.weaken)
      (tg_aux_m (p.map_l (fun t => t.weaken.weaken)) (.bound 1) h.weaken.weaken v.weaken.weaken))
    (.disj (.conj (Formula.extensionalEq .newest p.a.weaken.weaken)
      (tg_answer_m (p.map_l (fun t => t.weaken.weaken)) (.bound 1) h.weaken.weaken v.weaken.weaken))
      (.conj (Formula.extensionalEq .newest p.b.weaken.weaken) (.mem v.weaken.weaken p.A.weaken.weaken)))))))

@[simp] theorem tg_step_closed_l {d} (p : Tg_params_d (Term d)) (i h v : Term d)
    (hp : p.closed_l) (hi : i.freeSupport = []) (hh : h.freeSupport = []) (hv : v.freeSupport = []) :
    (tg_step_m p i h v).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using hp
  rcases hp with ⟨hω, he, ha, hb, hc, _, hA, _⟩
  simp -implicitDefEqProofs [tg_step_m, Definitional.Formula.FreeClosed, hω, he, ha, hb, hc, hA, hi, hh, hv, hp']

theorem tg_step_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (i h v : Term d) :
    Formula.satisfies ρ (tg_step_m p i h v) ↔ Tg_step_d hZF (p.map_l (fun t => t.eval ρ)) (i.eval ρ) (h.eval ρ) (v.eval ρ) := by
  simp only [tg_step_m, Tg_step_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isOrdinalDivision_iff I hZF.1, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1, tg_aux_sat_l hZF, tg_answer_sat_l hZF,
    Tg_params_d.map_l, Definitional.Term.eval_weaken]
  rfl

theorem tg_step_read_l {p : Tg_params_d M.Domain} {i n r h v : M.Domain}
    (hi : M.IsOrdinal i) (hc : M.IsOrdinal p.c) (nonzero : ∃ x, M.mem x p.c)
    (hn : M.mem n p.ω) (div : M.IsOrdinalDivision I i p.c n r) :
    Tg_step_d hZF p i h v ↔
      (r = p.e ∧ Tg_aux_d hZF p n h v) ∨ (r = p.a ∧ Tg_answer_d hZF p n h v) ∨ (r = p.b ∧ M.mem v p.A) := by
  obtain ⟨q, s, _, unique⟩ := ZF.ordinalDivision_existsUnique_pair hZF I hi hc nonzero
  obtain ⟨en, er⟩ := unique n r div
  refine ⟨?_, fun h => ⟨n, r, hn, div, h⟩⟩
  rintro ⟨n', r', _, d', rule⟩
  obtain ⟨en', er'⟩ := unique n' r' d'
  exact (en'.trans en.symm) ▸ (er'.trans er.symm) ▸ rule

def Tg_check_d (p : Tg_params_d M.Domain) (X f : M.Domain) : Prop := (∀ v, ¬ M.mem v f) ∨
  ∃ i j h v, M.mem j p.ω ∧ M.SuccessorOf j i ∧ Fn0_d j X f ∧ M.IsRestrictionOf I h f i ∧
    Rd_entry_d i v f ∧ Tg_step_d hZF p i h v

def tg_check_m {d} (p : Tg_params_d (Term d)) (X f : Term d) : Formula 1 d :=
  .disj (Formula.forallMem f .falsum) (.existsE (.existsE (.existsE (.existsE
    (.conj (.mem (.bound 2) p.ω.weaken.weaken.weaken.weaken) (.conj (Formula.isSuccessor (.bound 2) (.bound 3))
      (.conj (fn0_m (.bound 2) X.weaken.weaken.weaken.weaken f.weaken.weaken.weaken.weaken)
        (.conj (Formula.isRestriction kpair_convention_l (.bound 1) f.weaken.weaken.weaken.weaken (.bound 3))
          (.conj (rd_entry0_m (.bound 3) .newest f.weaken.weaken.weaken.weaken)
            (tg_step_m (p.map_l (fun t => t.weaken.weaken.weaken.weaken)) (.bound 3) (.bound 1) .newest))))))))))

@[simp] theorem tg_check_closed_l {d} (p : Tg_params_d (Term d)) (X f : Term d)
    (hp : p.closed_l) (hX : X.freeSupport = []) (hf : f.freeSupport = []) : (tg_check_m p X f).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using hp
  simp -implicitDefEqProofs [tg_check_m, Definitional.Formula.FreeClosed, hp.1, hX, hf, hp']

theorem tg_check_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X f : Term d) :
    Formula.satisfies ρ (tg_check_m p X f) ↔ Tg_check_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (f.eval ρ) := by
  simp only [tg_check_m, Tg_check_d, Formula.satisfies_disj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_falsum_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isSuccessor_iff, fn0_sat_l hZF.1,
    Formula.satisfies_isRestriction_iff I, rd_entry0_sat_l hZF.1, tg_step_sat_l hZF,
    Tg_params_d.map_l, Definitional.Term.eval_weaken]
  rfl

/-- 最后一步检查的存在证书由实际追加图唯一确定。 -/
theorem Tg_check_d.end_l {p : Tg_params_d M.Domain} {X i h t a : M.Domain}
    (check : Tg_check_d hZF p X t) (fn : Fn0_d i X h) (endt : Fseq_end_d I p.ω t h a) :
    Tg_step_d hZF p i h a := by
  obtain ⟨m, i', d⟩ := endt
  have eq := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fn).2.1
  subst i'
  rcases check with empty | ⟨k, j, h', a', _, succ, ft, rest, value, step⟩
  · exact (d.last_value.elim fun q hq => empty q hq.2).elim
  · have eq := d.source.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) ft).2.1
    subst m
    have eq := d.length_successor.predecessor_eq hZF.1 d.prefix_sequence.2.1 succ
    subst k
    have eh := rest.eq hZF.1 d.prefix_restriction
    have ea := d.source.2.2.1.2 i a' a value d.last_value
    exact eh ▸ ea ▸ step

theorem tg_check_end_l {p : Tg_params_d M.Domain} {X i j h t a : M.Domain}
    (hj : M.mem j p.ω) (succ : M.SuccessorOf j i) (fn : Fn0_d j X t)
    (fh : Fn0_d i X h) (endt : Fseq_end_d I p.ω t h a) (step : Tg_step_d hZF p i h a) :
    Tg_check_d hZF p X t := by
  obtain ⟨m, i', d⟩ := endt
  have eq := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  subst i'
  exact Or.inr ⟨i, j, h, a, hj, succ, fn, d.prefix_restriction, d.last_value, step⟩

def Tg_histories_d (p : Tg_params_d M.Domain) (X F L : M.Domain) : Prop :=
  Fseq_space_d I p.ω X F ∧ ∀ f, M.mem f L ↔ M.mem f F ∧ Tg_check_d hZF p X f

/-- 全体历史与逐步合法集合均存在于原模型中；原公式只使用十二个固定参数。 -/
theorem tg_histories_l (p : Tg_params_d M.Domain) {X : M.Domain} (hω : M.IsOmega p.ω) :
    ∃ F L, Tg_histories_d hZF p X F L := by
  obtain ⟨F, space⟩ := ZF.fseq_space_exists_l I hZF hω X
  let ρ : Env M 13 := ⟨Fin.cases X (Fin.cases p.Q (Fin.cases p.P (Fin.cases p.E (Fin.cases p.ν
    (Fin.cases p.S (Fin.cases p.A (Fin.cases p.δ (Fin.cases p.c (Fin.cases p.b (Fin.cases p.a
      (Fin.cases p.e (fun _ => p.ω)))))))))))), fun _ => p.ω⟩
  let q : Tg_params_d (Term 14) := ⟨.bound 13, .bound 12, .bound 11, .bound 10, .bound 9, .bound 8,
    .bound 7, .bound 6, .bound 5, .bound 4, .bound 3, .bound 2⟩
  let φ : UnarySchema 13 := {
    body := tg_check_m q (.bound 1) .newest
    freeClosed := by
      exact tg_check_closed_l q _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl }
  obtain ⟨L, sep⟩ := ZF.separation_exists_d hZF φ ρ F
  refine ⟨F, L, space, fun f => (sep f).trans (and_congr Iff.rfl ?_)⟩
  exact tg_check_sat_l hZF (ρ.push f) q (.bound 1) .newest

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原游戏固定参数的自动构造

重置高度取相对于 max(δ,rank(S)) 的原最小局部不可分辨对的第一坐标。
三张代码表和内部 0、1、2、3 同时构造；输入不包含任何查询或编译谕示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_low_d (hZF : M.Models ZF) (ω e δ S ν : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ ρ θ γ U D μ, Rk_d I S ρ ∧ M.IsOrdinal θ ∧ M.IsUnionOfTwo θ δ ρ ∧
    M.IsOrdinalAddition I γ θ ω ∧ V_d I γ U ∧ Tt_pool_d I ω e U D ∧ Li_least_d I ω e U D θ ν μ

theorem tg_low_l (hZF : M.Models ZF) {ω δ : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsOrdinal δ) (S : M.Domain) :
    ∃ e ν, (∀ x, ¬ M.mem x e) ∧ M.mem e ω ∧ Tg_low_d hZF ω e δ S ν := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ρ, rank⟩ := ZF.rk_exists_l I hZF S
  obtain ⟨P, pair⟩ := KP.exists_pair (ZF.modelsKP hZF) δ ρ
  obtain ⟨θ, union⟩ := KP.exists_union (ZF.modelsKP hZF) P
  have ordinal : M.IsOrdinal θ := .of_union (ZF.modelsKP hZF) union (fun x hx =>
    ((pair x).mp hx).elim (fun eq => eq.symm ▸ hδ) (fun eq => eq.symm ▸ rank.ordinal I))
  have max : M.IsUnionOfTwo θ δ ρ := by
    intro x
    refine (union x).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy, hx⟩
      exact ((pair y).mp hy).elim (fun eq => Or.inl (eq ▸ hx)) (fun eq => Or.inr (eq ▸ hx))
    · intro hx
      exact hx.elim (fun h => ⟨δ, (pair δ).mpr (Or.inl rfl), h⟩) (fun h => ⟨ρ, (pair ρ).mpr (Or.inr rfl), h⟩)
  obtain ⟨e, γ, U, D, ν, μ, he, heω, sum, hU, pool, least⟩ := li_canonical_l I hZF hω ordinal
  exact ⟨e, ν, he, heω, ρ, θ, γ, U, D, μ, rank, ordinal, max, sum, hU, pool, least⟩

theorem Tg_low_d.read_l (hZF : M.Models ZF) {ω e δ S ν : M.Domain} (hδ : M.IsOrdinal δ)
    (low : Tg_low_d hZF ω e δ S ν) : M.mem δ ν ∧ ∃ Y, V_d (kp_pair_l (ZF.modelsKP hZF)) ν Y ∧ M.mem S Y := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ρ, θ, _, _, _, _, rank, _, max, _, _, _, least⟩ := low
  have oν := least.2.1.1
  have below (α : M.Domain) (hα : M.IsOrdinal α) (sub : M.MemberSubset α θ) : M.mem α ν :=
    ordinal_down_l (ZF.modelsKP hZF) hα oν sub least.1
  obtain ⟨Y, hY⟩ := ZF.v_exists_l I hZF oν
  exact ⟨below δ hδ (fun x hx => (max x).mpr (Or.inl hx)), Y, hY,
    (ZF.rk_mem_l I hZF rank hY).mpr (below ρ (rank.ordinal I) (fun x hx => (max x).mpr (Or.inr hx)))⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Tg_setup_d (p : Tg_params_d M.Domain) (X : M.Domain) : Prop where
  omega : M.IsOmega p.ω
  empty : ∀ x, ¬ M.mem x p.e
  one : M.SuccessorOf p.a p.e
  two : M.SuccessorOf p.b p.a
  three : M.SuccessorOf p.c p.b
  limit : M.IsLimitOrdinal p.δ
  above : M.mem p.ω p.δ
  rank : V_d I p.δ X
  letters : M.mem p.A X
  elastic : ∃ D, Ee_catalog_d hZFC p.ω p.δ X D p.E
  programs : ∃ H, V_d I p.ω H ∧ Tg_program_catalog_d hZFC p.ω H p.P ∧ M.MemberSubset p.P H
  queries : Tg_query_catalog_d hZFC p.ω p.e p.δ X p.Q
  elastic_bound : M.MemberSubset p.E X
  query_bound : M.MemberSubset p.Q X
  low : Tg_low_d hZF p.ω p.e p.δ p.S p.ν

/-- 从原数学输入一次构造全部参数；代码表的选择只发生于开局之前。 -/
theorem tg_setup_l {ω δ A S X : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hwδ : M.mem ω δ) (hX : V_d I δ X) (hA : M.mem A X) :
    ∃ p : Tg_params_d M.Domain, p.ω = ω ∧ p.δ = δ ∧ p.A = A ∧ p.S = S ∧ Tg_setup_d hZFC p X := by
  obtain ⟨e, ν, he, heω, low⟩ := tg_low_l hZF hω hδ.1 S
  obtain ⟨a, ha, haω⟩ := hω.1.2 e heω
  obtain ⟨b, hb, hbω⟩ := hω.1.2 a haω
  obtain ⟨c, hc, _⟩ := hω.1.2 b hbω
  obtain ⟨D, E, elastic, eBound⟩ := ee_catalog_l hZFC hω hδ hwδ hX
  obtain ⟨H, P, hH, programs, pBound⟩ := tg_program_catalog_l hZFC hω
  obtain ⟨Q, queries, qBound⟩ := tg_query_catalog_l hZFC hω he hδ hwδ hX
  exact ⟨⟨ω, e, a, b, c, δ, A, S, ν, E, P, Q⟩, rfl, rfl, rfl, rfl,
    hω, he, ha, hb, hc, hδ, hwδ, hX, hA, ⟨D, elastic⟩, ⟨H, hH, programs, pBound⟩, queries, eBound, qBound, low⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## Neeman 5.13 的完整辅助闭博弈

由原数学输入构造固定语言、全部内部有限历史、七条规则、三阶段归属和
闭收益集合。返回的四元组是模型内的游戏码；策略空间也由模型内幂集构造。
本层装配游戏；决定性见 TypeGameDeterminacy，5.15 的 II 策略转移见 TypeGameTransfer。
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
  game.payoff.ii_first_l (ZF.modelsKP hZF) (game.setup.omega.isOrdinal (ZF.modelsKP hZF)) ((game.runs f).mp hf).1 hf hh sub first turn

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
  have heX := v_transitive_l I game.setup.rank p.ω
    (ZF.v_ordinal_mem_l I hZF game.setup.rank game.setup.above) p.e heω
  obtain ⟨σ, fn, _⟩ := ZF.exists_constantFunction hZF I (source := F) heX
  exact ⟨σ, (game.strategies σ).mpr fn⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 两种类型游戏共用的原低点句法

低点仍是原最小局部不可分辨对的首坐标。语义证明只有一份，
普通与 demanding 更新句子直接引用同一定义。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_low0_m : Formula 1 5 :=
  let ω := Term.bound 0; let e := Term.bound 1; let δ := Term.bound 2
  let S := Term.bound 3; let ν := Term.bound 4
  set[5] ⟪∃ ρ θ γ U D μ,
  ⌜rk_m (𝒞 := kpair_convention_l)⌝ₚ(⌜S⌝ₛ, ρ) ∧ ⌜Formula.isOrdinal⌝ₚ(θ) ∧
  (∀ x, x ∈ θ ↔ x ∈ ⌜δ⌝ₛ ∨ x ∈ ρ) ∧ ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(γ, θ, ⌜ω⌝ₛ) ∧
  ⌜v_m kpair_convention_l⌝ₚ(γ, U) ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, U, D) ∧
  ⌜li_least_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, U, D, θ, ⌜ν⌝ₛ, μ)⟫
@[simp] theorem tg_low0_closed_l : tg_low0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_low0_m, Definitional.Formula.FreeClosed]

def tg_low_m {d} (ω e δ S ν : Term d) : Formula 1 d :=
  tg_low0_m.bind (fun i => [ω, e, δ, S, ν].get i)

@[simp] theorem tg_low_closed_l {d} (ω e δ S ν : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (hd : δ.freeSupport = [])
    (hS : S.freeSupport = []) (hν : ν.freeSupport = []) : (tg_low_m ω e δ S ν).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_low0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, he, hd, hS, hν, fun i => Fin.elim0 i⟩

theorem tg_low_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω e δ S ν : Term d) :
    Formula.satisfies ρ (tg_low_m ω e δ S ν) ↔
      Tg_low_d hZF (ω.eval ρ) (e.eval ρ) (δ.eval ρ) (S.eval ρ) (ν.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [tg_low_m, Formula.satisfies_bind, tg_low0_m, Tg_low_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rk_sat_l I hZF.1, Formula.satisfies_isOrdinal_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isOrdinalAddition_iff I hZF.1, v_sat_l I hZF.1, tt_pool_sat_l I (ZF.modelsKP hZF),
    li_least_sat_l I (ZF.modelsKP hZF), Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 完整博弈的自动阶段读取

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
  have ord := game.setup.omega.members_areOrdinals (ZF.modelsKP hZF)
  exact ⟨n, r, hn, div, phase, game.owner.read_l hZF (game.setup.omega.isOrdinal (ZF.modelsKP hZF)) (ord p.c hc)
    ⟨p.b, game.setup.three.predecessor_mem⟩ hi hn div,
    fun _ _ => tg_step_read_l hZF (ord i hi) (ord p.c hc) ⟨p.b, game.setup.three.predecessor_mem⟩ hn div, unique⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 完整辅助闭博弈的决定性

直接对已经装配的三阶段游戏应用闭博弈定理，返回原策略空间中的获胜策略。
本结论确定有一方获胜；TypeGameTransfer 已完成 5.15 从辅助博弈到原博弈的 II 策略转移。
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
  have heX := v_transitive_l I game.setup.rank p.ω
    (ZF.v_ordinal_mem_l I hZF game.setup.rank game.setup.above) p.e heω
  have sub : M.MemberSubset W B := by
    obtain ⟨_, _, _, _, body⟩ := game.payoff
    exact fun f hf => ((body f).mp hf).1
  rcases cg_closed_det_l hZFC game.setup.omega game.histories.1 game.runs heX sub game.complement game.closed with
    ⟨σ, win⟩ | ⟨σ, win⟩
  · exact ⟨true, σ, (game.strategies σ).mpr (fn0_function_l (ZF.modelsKP hZF) win.1), win⟩
  · exact ⟨false, σ, (game.strategies σ).mpr (fn0_function_l (ZF.modelsKP hZF) win.1), win⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从原游戏节点自动构造每轮弹性回答

局部不可分辨参数带由游戏的原最小对给出。树的实际节点保证全部旧标签
属于该参数带；根与序数末位的区别由空根和配对编码保证，无须额外排列假设。
回答同时保留原节点，满足规则 (7) 的三条查询，并给出实际一步扩展器。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem Tg_low_d.band_l (hZF : M.Models ZF) {ω e δ S ν : M.Domain}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (hδ : M.IsOrdinal δ) (hwδ : M.mem ω δ) (low : Tg_low_d hZF ω e δ S ν) :
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ γ W F μ, M.IsLimitOrdinal γ ∧ V_d I γ W ∧ M.mem ω W ∧ M.mem δ W ∧ M.mem S W ∧
      Tt_pool_d I ω e W F ∧ Li_pair_d I ω e W F ν μ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ρ, θ, γ, W, F, μ, rank, ho, max, sum, hW, pool, least⟩ := low
  have limit := (ZF.ordinalAddition_isNormalOrdinalFunction hZF I ho).limit_value (hω.isLimitOrdinal (ZF.modelsKP hZF)) sum
  have lt : M.mem θ γ := (ZF.ordinalAddition_mem_iff hZF I (hω.isOrdinal (ZF.modelsKP hZF)) sum).mpr
    (Or.inr ⟨e, heω, (ZF.ordinalAddition_zero_iff hZF I he).mpr rfl⟩)
  have dγ := ordinal_down_l (ZF.modelsKP hZF) hδ limit.1 (fun x hx => (max x).mpr (Or.inl hx)) lt
  have rγ := ordinal_down_l (ZF.modelsKP hZF) (rank.ordinal I) limit.1
    (fun x hx => (max x).mpr (Or.inr hx)) lt
  exact ⟨γ, W, F, μ, limit, hW, ZF.v_ordinal_mem_l I hZF hW (limit.1.transitive δ dγ ω hwδ),
    ZF.v_ordinal_mem_l I hZF hW dγ, (ZF.rk_mem_l I hZF rank hW).mpr rγ, pool, least.2.1⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_low_d.renew_l {ω e δ S ν κ k l n α A c R r B U D P u v b a z χ s t g : M.Domain}
    {σ : Fin 7 → M.Domain} {q : Ee_queries_d M}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (hd : Woodin_d I δ) (low : Tg_low_d hZF ω e δ S ν) (root : M.mem e S)
    (hκδ : M.mem κ δ) (succ : M.SuccessorOf n l)
    (height : M.SuccessorOf α ν) (hA : V_d I α A) (model : Smem_d I c A R)
    (type : Tt_realized_d I ω c A R n r δ U P u)
    (language : Ee_language_d hZF ω κ l B U D q) (drop : Td_dcp_d I l n D u v)
    (elastic : Ee_elastic_d q v) (first : Rd_entry_d e S r) (last : Rd_entry_d l ν r)
    (set : Sg_set_d I e l r g) (node : Tg_node_d I k S s t g)
    (prog : Ts_program_d hZF ω l b σ a z) (hχ : M.mem χ δ) :
    ∃ τ C V Q w η Y d H, ∃ q' : Ee_queries_d M, ∃ p : Tg_reply_queries_d M,
      M.mem χ τ ∧ M.mem κ τ ∧ M.mem τ δ ∧ Tg_height_d ν η ∧ V_d I η Y ∧ Smem_d I d Y H ∧
      Ee_language_d hZF ω τ n C V Q q' ∧ Tt_realized_d I ω d Y H n r δ V Q w ∧ Ee_elastic_d q' w ∧
      Tg_reply_language_d hZF ω e l n τ C V Q p ∧ M.mem p.root w ∧ M.mem p.bound w ∧ M.mem p.height w ∧
      Tx_exceeds_d hZF ω δ κ l U D v τ n V Q w ∧ Ee_one_step_d hZF ω κ δ l v τ n w b σ z := by
  have woodin := hd
  obtain ⟨ω₀, _, hw₀, hwδ, regular, _⟩ := woodin
  have eq := hZF.1.eq_of_same_members ω₀ ω (fun x => ⟨hw₀.2 ω hω.1 x, hω.2 ω₀ hw₀.1 x⟩)
  subst ω₀
  obtain ⟨hδν, A₀, hA₀, hS₀⟩ := low.read_l hZF regular.isCardinal.1
  obtain ⟨γ, W, F, μ, hγ, hW, hwW, hδW, hSW, pool, pair⟩ := low.band_l hZF hω he heω regular.isCardinal.1 hwδ
  have labels := node.labels_mem_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
    (v_transitive_l I hW) hSW (sc_v_pair_l (ZF.modelsKP hZF) hγ hW)
  have values i x (hi : M.mem i l) (hx : Rd_entry_d i x r) : M.mem x W ∧ x ≠ ν := by
    by_cases eq : i = e
    · have same := type.tuple.2.2 e ((type.tuple.bound_l first).1) x (type.tuple.bound_l hx).2 S
        (type.tuple.bound_l first).2 (eq ▸ hx) first
      subst x
      exact ⟨hSW, fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) ν
        (ZF.v_ordinal_height_l hZF hA₀ pair.1 (eq ▸ hS₀))⟩
    · have gx := (set x).mpr ⟨i, hi, eq, hx⟩
      obtain ⟨j, y, cp⟩ := node.2.2.1.1.1 x gx
      exact ⟨labels x gx, fun eq => cp.not_transitive_l M (KP.mem_irrefl_d (ZF.modelsKP hZF)) (eq.symm ▸ pair.1.transitive)⟩
  obtain ⟨τ, C, V, Q, w, η, Y, d, H, q', hχτ, hκτ, hτδ, level, hY, mdl, lang, real, el, exceeds, step⟩ :=
    tg_renew_l hZFC hω he heω hd hγ hW hwW hδW pool pair hδν hκδ succ height hA model type language
      drop elastic last values prog hχ
  obtain ⟨C', V', Q', p, target⟩ := tg_reply_language_l hZF hω he type.finite
    (type.tuple.bound_l first).1 succ.predecessor_mem lang.limit
  have eqC := ZF.v_unique_l I hZF target.rank lang.rank
  subst C'
  have eqV := hZF.1.eq_of_same_members V' V (fun x => (target.constants x).trans (lang.constants x).symm)
  subst V'
  have eqQ := target.pool.unique_l hZF.1 I lang.pool
  subst Q'
  exact ⟨τ, C, V, Q, w, η, Y, d, H, q', p, hχτ, hκτ, hτδ, level, hY, mdl, lang, real, el, target,
    (target.root.2 d Y H r δ w S mdl (v_transitive_l I hY) real first).mpr root,
    (target.bound.2 η Y d H r δ w S ν hY mdl real first last).mpr ⟨pair.1, hδν, A₀, hA₀, hS₀⟩,
    (target.height.2 η Y d H r δ w ν hY mdl real last).mpr level, exceeds, step⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 每轮回答在同一实际超幂中的规则 (7)

先由原游戏的不可分辨点与完整节点生成回答和扩展器，再施加该扩展器。
dcp 与像交换、子类型查询更换定义域均已证明，故输出实际像 u 的完整回答。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_low_d.step_l {ω e δ S ν κ k l n α A c R r B U D P u v b a z χ s t g : M.Domain}
    {σ : Fin 7 → M.Domain} {q : Ee_queries_d M}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (hd : Woodin_d I δ) (low : Tg_low_d hZF ω e δ S ν) (root : M.mem e S)
    (hκδ : M.mem κ δ) (succ : M.SuccessorOf n l)
    (height : M.SuccessorOf α ν) (hA : V_d I α A) (model : Smem_d I c A R)
    (type : Tt_realized_d I ω c A R n r δ U P u)
    (language : Ee_language_d hZF ω κ l B U D q) (drop : Td_dcp_d I l n D u v)
    (elastic : Ee_elastic_d q v) (first : Rd_entry_d e S r) (last : Rd_entry_d l ν r)
    (set : Sg_set_d I e l r g) (node : Tg_node_d I k S s t g)
    (prog : Ts_program_d hZF ω l b σ a z) (hχ : M.mem χ δ) :
    ∃ τ C V Q w η Z d H, ∃ q' : Ee_queries_d M, ∃ p : Tg_reply_queries_d M,
    ∃ X K T L F c₀ d₀ Y T' j κ' U' D' u',
      M.mem χ τ ∧ M.mem κ τ ∧ M.mem τ δ ∧ Tg_height_d ν η ∧ V_d I η Z ∧ Smem_d I d Z H ∧
      Ee_language_d hZF ω τ n C V Q q' ∧ Tt_realized_d I ω d Z H n r δ V Q w ∧ Ee_elastic_d q' w ∧
      Tg_reply_language_d hZF ω e l n τ C V Q p ∧
      V_d I δ X ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X T ∧ M.mem L δ ∧ M.mem κ L ∧ M.mem τ L ∧
      It_local_d I ω X T κ L F ∧ Sc_inaccessible_d ω X L ∧ Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F ∧
      Smem_d I c₀ X T ∧ Smem_d I d₀ Y T' ∧ It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c₀ d₀ j ∧
      Wd_crit_d I X j κ κ' ∧ M.MemberSubset L κ' ∧ M.IsLimitOrdinal κ' ∧
      Rd_entry_d U U' j ∧ Rd_entry_d D D' j ∧ Rd_entry_d u u' j ∧ Tt_pool_d I ω l U' D' ∧
      Tg_reply_d I ω l n κ' τ U' D' Q u' w b σ z p := by
  obtain ⟨τ, C, V, Q, w, η, Z, d, H, q', p, hχτ, hκτ, hτδ, level, hZ, mdl, lang, real, el,
    target, qr, qb, qh, _, step⟩ := low.renew_l hZFC hω he heω hd root hκδ succ height hA model type language
      drop elastic first last set node prog hχ
  have woodin := hd
  obtain ⟨_, _, _, _, regular, _⟩ := woodin
  obtain ⟨X, K, T, L, F, c₀, d₀, Y, T', j, κ', U', D', u', v', hX, source, hLδ, hκL, hτL, _, loc, inacc, strength,
    mx, my, ultra, critical, bound, κlimit, hU, hD, hu, pool, drop', subtype⟩ :=
    step.dcp_image_l hZF hω regular.isLimitOrdinal prog language hA model type succ drop lang.limit type.finite hχ
  exact ⟨τ, C, V, Q, w, η, Z, d, H, q', p, X, K, T, L, F, c₀, d₀, Y, T', j, κ', U', D', u',
    hχτ, hκτ, hτδ, level, hZ, mdl, lang, real, el, target, hX, source, hLδ, hκL, hτL,
    loc, inacc, strength, mx, my, ultra, critical, bound, κlimit, hU, hD, hu, pool,
    ⟨fun x hx => ((real.truth x).mp hx).1, v', drop', subtype, qr, qb, qh⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 一轮回答的实际超幂证书公式

证书包含原秩段、所属扩展器、同一超幂及完整规则 (7)。将它单独编码，
使反射句子只绑定游戏输入，而后继读取能直接消费这一份存在证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_image_m {d} (ω κ δ l n U D u τ Q w b z r q h : Term d) (σ : Fin 7 → Term d) : Formula 1 d := set[d] ⟪
  ∃ X K R L F c d Y T j κ' U' D' u',
    ⌜ti_image_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜δ⌝ₛ, ⌜τ⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ, X, K, R, L, F, c, d, Y, T, j, κ', U', D', u') ∧
    (∃ W, ⌜v_sigma_m⌝ₚ(L, W) ∧ ⌜Q⌝ₛ ∈ W) ∧
    ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜l⌝ₛ, U', D') ∧
    ⌜fun ω l n κ τ U D Q u w b z r q h s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_reply_m ω l n κ τ U D Q u w b z r q h
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜ω⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, κ', ⌜τ⌝ₛ, U', D', ⌜Q⌝ₛ, u', ⌜w⌝ₛ, ⌜b⌝ₛ, ⌜z⌝ₛ, ⌜r⌝ₛ, ⌜q⌝ₛ, ⌜h⌝ₛ,
        ⌜σ 0⌝ₛ, ⌜σ 1⌝ₛ, ⌜σ 2⌝ₛ, ⌜σ 3⌝ₛ, ⌜σ 4⌝ₛ, ⌜σ 5⌝ₛ, ⌜σ 6⌝ₛ)⟫

@[simp] theorem tg_image_closed_l {d} (ω κ δ l n U D u τ Q w b z r q h : Term d) (σ : Fin 7 → Term d)
    (hω : ω.freeSupport = []) (hκ : κ.freeSupport = []) (hδ : δ.freeSupport = [])
    (hl : l.freeSupport = []) (hn : n.freeSupport = []) (hU : U.freeSupport = []) (hD : D.freeSupport = [])
    (hu : u.freeSupport = []) (hτ : τ.freeSupport = []) (hQ : Q.freeSupport = []) (hw : w.freeSupport = [])
    (hb : b.freeSupport = []) (hz : z.freeSupport = []) (hr : r.freeSupport = []) (hq : q.freeSupport = [])
    (hh : h.freeSupport = []) (hσ : ∀ i, (σ i).freeSupport = []) :
    (tg_image_m ω κ δ l n U D u τ Q w b z r q h σ).FreeClosed := by
  simp -implicitDefEqProofs [tg_image_m, Definitional.Formula.FreeClosed, hω, hκ, hδ, hl, hn, hU, hD, hu,
    hτ, hQ, hw, hb, hz, hr, hq, hh, hσ, Fin.forall_fin_succ]

variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

/-- 固定本次支撑、源、扩展器及完整超幂，后继构造直接消费规则 (7) 的同一批见证。 -/
def Tg_image_at_d (ω κ δ l n U D u τ Q w b : M.Domain) (σ : Fin 7 → M.Domain)
    (z : M.Domain) (p : Tg_reply_queries_d M) (L W X K R F c d Y T j κ' U' D' u' : M.Domain) : Prop :=
    V_d I δ X ∧ Ep_source_d I ω κ K X R ∧ M.mem L δ ∧ M.mem κ L ∧ M.mem τ L ∧
    V_d I L W ∧ M.mem Q W ∧
    It_local_d I ω X R κ L F ∧ Sc_inaccessible_d ω X L ∧ Ex_strength_d I ω κ L X F ∧
    Smem_d I c X R ∧ Smem_d I d Y T ∧ It_ultra_d I ω κ L F c d j ∧ Wd_crit_d I X j κ κ' ∧
    M.MemberSubset L κ' ∧ M.IsLimitOrdinal κ' ∧
    Rd_entry_d U U' j ∧ Rd_entry_d D D' j ∧ Rd_entry_d u u' j ∧ Tt_pool_d I ω l U' D' ∧
    Tg_reply_d I ω l n κ' τ U' D' Q u' w b σ z p

theorem tg_image_sat_l {d} (ρ : Env M d) (ω κ δ l n U D u τ Q w b z r q h : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (tg_image_m ω κ δ l n U D u τ Q w b z r q h σ) ↔
    ∃ X K R L F c d Y T j κ' U' D' u',
      V_d I (δ.eval ρ) X ∧ Ep_source_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) K X R ∧
      M.mem L (δ.eval ρ) ∧ M.mem (κ.eval ρ) L ∧ M.mem (τ.eval ρ) L ∧
      (∃ W, V_d I L W ∧ M.mem (Q.eval ρ) W) ∧
      It_local_d I (ω.eval ρ) X R (κ.eval ρ) L F ∧ Sc_inaccessible_d (ω.eval ρ) X L ∧
      Ex_strength_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) L X F ∧ Smem_d I c X R ∧ Smem_d I d Y T ∧
      It_ultra_d (kp_pair_l hKP) (ω.eval ρ) (κ.eval ρ) L F c d j ∧ Wd_crit_d I X j (κ.eval ρ) κ' ∧
      M.MemberSubset L κ' ∧ M.IsLimitOrdinal κ' ∧ Rd_entry_d (U.eval ρ) U' j ∧
      Rd_entry_d (D.eval ρ) D' j ∧ Rd_entry_d (u.eval ρ) u' j ∧ Tt_pool_d I (ω.eval ρ) (l.eval ρ) U' D' ∧
      Tg_reply_d I (ω.eval ρ) (l.eval ρ) (n.eval ρ) κ' (τ.eval ρ) U' D' (Q.eval ρ) u' (w.eval ρ)
        (b.eval ρ) (fun i => (σ i).eval ρ) (z.eval ρ) ⟨r.eval ρ, q.eval ρ, h.eval ρ⟩ := by
  have eta (f : Fin 7 → M.Domain) :
      (Fin.cases (f 0) (Fin.cases (f 1) (Fin.cases (f 2) (Fin.cases (f 3)
        (Fin.cases (f 4) (Fin.cases (f 5) (fun _ => f 6))))))) = f := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  simp only [tg_image_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ti_image_sat_l hKP, v_sigma_sat_l hKP, Formula.satisfies_mem_iff,
    tt_pool_sat_l I hKP, tg_reply_sat_l hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, tt_eval_cases_l, eta (fun i => (σ i).eval ρ)]
  constructor
  · rintro ⟨X, K, R, L, F, c, d, Y, T, j, κ', U', D', u', core, queryRank, pool, reply⟩
    obtain ⟨rank, source, hL, hk, ht, loc, card, strong, mx, my, ultra, critical, bound, limit, hU, hD, hu⟩ := core
    exact ⟨X, K, R, L, F, c, d, Y, T, j, κ', U', D', u', rank, source, hL, hk, ht, queryRank,
      loc, card, strong, mx, my, ultra, critical, bound, limit, hU, hD, hu, pool, reply⟩
  · rintro ⟨X, K, R, L, F, c, d, Y, T, j, κ', U', D', u', rank, source, hL, hk, ht, queryRank,
      loc, card, strong, mx, my, ultra, critical, bound, limit, hU, hD, hu, pool, reply⟩
    exact ⟨X, K, R, L, F, c, d, Y, T, j, κ', U', D', u',
      ⟨rank, source, hL, hk, ht, loc, card, strong, mx, my, ultra, critical, bound, limit, hU, hD, hu⟩,
      queryRank, pool, reply⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原档案支撑的不可数共尾性

只保存严格极限切片所需的原生共尾度及其高于 ω 的事实，不保存整份
不可达性。实际回答的秩源向上读取后，以同一个支撑 L 作为共尾度见证。
后续读取仍在原关系模型中进行，不要求该模型具有传递隶属呈示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tg_raw_cofinal_d (w X R L : M.Domain) : Prop :=
  ∃ ν, Rd_entry_d w ν R ∧
    Rr_truth_d I X R (Formula.isCofinality kpair_convention_l (.bound 0) (.bound 1))
      (Fin.cases ν (fun _ : Fin 1 => L))

private theorem tgr_entry_l (hE : Extensional M) (x y R : M.Domain) :
    Rd_entry_d x y R ↔ M.PairMember I x y R := by
  let ρ : Env M 3 := ⟨fun i => [x,y,R].get i,fun _ => x⟩
  exact (rd_entry_sat_l hE ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
    (Formula.satisfies_orderedPairMem_iff I ρ (.bound 0) (.bound 1) (.bound 2))

/-- 实际秩段中的不可达支撑生产较弱的档案共尾度，两类游戏共用。 -/
theorem it_support_cofinal_l (hE : Extensional M) {N R : M.Domain} (nx : ∃ x, M.mem x N)
    (hN : (smdl_structure_l I (R := R) nx).Models KP)
    {w δ L X : (smdl_structure_l I (R := R) nx).Domain}
    (card : Sc_inaccessible_d w X L) (rank : V_d (kp_pair_l hN) δ X)
    (height : (smdl_structure_l I (R := R) nx).IsLimitOrdinal δ) :
    Tg_raw_cofinal_d I w.val N R L.val := by
  let Nn := smdl_structure_l I (R := R) nx
  let φ : Formula 1 2 := Formula.isCofinality kpair_convention_l (.bound 0) (.bound 1)
  let v : Fin 2 → Nn.Domain := Fin.cases L (fun _ : Fin 1 => L)
  let vs : Fin 2 → M.Domain := Fin.cases L.val (fun _ : Fin 1 => L.val)
  let ρ : Env Nn 2 := ⟨v,fun _ => v 0⟩
  obtain ⟨above,regular,_⟩ := sc_v_inaccessible_up_l hN height rank card
  refine ⟨L.val,(tgr_entry_l I hE w.val L.val R).mpr above,?_⟩
  have sat : Formula.satisfies ρ φ :=
    (Formula.satisfies_isCofinality_iff (kp_pair_l hN) hN.1 ρ (.bound 0) (.bound 1)).mpr regular
  have truth : Rr_truth_d I N R φ (fun i => (v i).val) :=
    (rr_truth_native_l I nx φ (by simp -implicitDefEqProofs [φ]) v).mpr sat
  have values : (fun i => (v i).val) = vs := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  exact Eq.mp (congrArg (Rr_truth_d I N R φ) values) truth

/-- 共尾度的原对象码直接读取；此方向只需外延性和配对解释。 -/
theorem Tg_raw_cofinal_d.native_l (hE : Extensional M) {X R : M.Domain} (nx : ∃ x, M.mem x X)
    (J : kpair_convention_l.Interpretation (smdl_structure_l I (R := R) nx))
    (ext : Extensional (smdl_structure_l I (R := R) nx))
    (w L : (smdl_structure_l I (R := R) nx).Domain)
    (h : Tg_raw_cofinal_d I w.val X R L.val) :
    ∃ ν : (smdl_structure_l I (R := R) nx).Domain,
      (smdl_structure_l I (R := R) nx).IsCofinality J ν L ∧
      (smdl_structure_l I (R := R) nx).mem w ν := by
  let Xn := smdl_structure_l I (R := R) nx
  let φ : Formula 1 2 := Formula.isCofinality kpair_convention_l (.bound 0) (.bound 1)
  obtain ⟨ν,above,truth⟩ := h
  let νn : Xn.Domain := ⟨ν,truth.1 0⟩
  let v : Fin 2 → Xn.Domain := Fin.cases νn (fun _ : Fin 1 => L)
  let vs : Fin 2 → M.Domain := Fin.cases ν (fun _ : Fin 1 => L.val)
  let ρ : Env Xn 2 := ⟨v,fun _ => v 0⟩
  have values : (fun i => (v i).val) = vs := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have read : Formula.satisfies ρ φ :=
    (rr_truth_native_l I nx φ (by simp -implicitDefEqProofs [φ]) v).mp
      (Eq.mpr (congrArg (Rr_truth_d I X R φ) values) truth)
  exact ⟨νn,(Formula.satisfies_isCofinality_iff J ext ρ (.bound 0) (.bound 1)).mp read,
    (tgr_entry_l I hE w.val ν R).mp above⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 每轮更新的有限反射句子

这是已证更新定理的同一个原语言句子。全部对象、原查询及程序槽位都由
集合量词绑定；输出仍包含实际扩展器及其超幂，不量化外部构造器或语义谕示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 更新输入保存完整实现、原 dcp 弹性、实际树节点及标签图的自然数值域。 -/
def tg_seed_m {d} (ω e δ S ν κ k l n α A c R r B U D P u v b a z χ s t g
    g₀ g₁ g₂ g₃ σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOmega⌝ₚ(⌜ω⌝ₛ) ∧ ⌜Formula.isEmpty⌝ₚ(⌜e⌝ₛ) ∧ ⌜e⌝ₛ ∈ ⌜ω⌝ₛ ∧
  ⌜woodin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜δ⌝ₛ) ∧ ⌜tg_low_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜δ⌝ₛ, ⌜S⌝ₛ, ⌜ν⌝ₛ) ∧
  ⌜e⌝ₛ ∈ ⌜S⌝ₛ ∧ ⌜κ⌝ₛ ∈ ⌜δ⌝ₛ ∧ ⌜Formula.isSuccessor⌝ₚ(⌜l⌝ₛ, ⌜k⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜n⌝ₛ, ⌜l⌝ₛ) ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜α⌝ₛ, ⌜ν⌝ₛ) ∧ ⌜v_m kpair_convention_l⌝ₚ(⌜α⌝ₛ, ⌜A⌝ₛ) ∧
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, ⌜A⌝ₛ, ⌜R⌝ₛ) ∧
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, ⌜A⌝ₛ, ⌜R⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, ⌜δ⌝ₛ, ⌜U⌝ₛ, ⌜P⌝ₛ, ⌜u⌝ₛ) ∧
  ⌜ee_language_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜l⌝ₛ, ⌜B⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜g₀⌝ₛ, ⌜g₁⌝ₛ, ⌜g₂⌝ₛ, ⌜g₃⌝ₛ) ∧
  ⌜td_dcp_m⌝ₚ(⌜l⌝ₛ, ⌜n⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ, ⌜v⌝ₛ) ∧ ⌜ee_elastic_m⌝ₚ(⌜g₀⌝ₛ, ⌜g₁⌝ₛ, ⌜g₂⌝ₛ, ⌜g₃⌝ₛ, ⌜v⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, ⌜S⌝ₛ, ⌜r⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, ⌜ν⌝ₛ, ⌜r⌝ₛ) ∧
  ⌜sg_set_m (𝒞 := kpair_convention_l)⌝ₚ(⌜e⌝ₛ, ⌜l⌝ₛ, ⌜r⌝ₛ, ⌜g⌝ₛ) ∧ ⌜tg_node_m⌝ₚ(⌜k⌝ₛ, ⌜S⌝ₛ, ⌜s⌝ₛ, ⌜t⌝ₛ, ⌜g⌝ₛ) ∧
  ⌜fun ω l b a z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => ts_program_m ω l b a z
    (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
    (⌜ω⌝ₛ, ⌜l⌝ₛ, ⌜b⌝ₛ, ⌜a⌝ₛ, ⌜z⌝ₛ, ⌜σ₀⌝ₛ, ⌜σ₁⌝ₛ, ⌜σ₂⌝ₛ, ⌜σ₃⌝ₛ, ⌜σ₄⌝ₛ, ⌜σ₅⌝ₛ, ⌜σ₆⌝ₛ) ∧ ⌜χ⌝ₛ ∈ ⌜δ⌝ₛ ∧
    ⌜tg_bound_raw_m⌝ₚ(⌜δ⌝ₛ, ⌜S⌝ₛ, ⌜ν⌝ₛ) ∧ ⌜fn0_m⌝ₚ(⌜k⌝ₛ, ⌜ω⌝ₛ, ⌜t⌝ₛ)⟫


/-- 一轮的同一组见证同时保存完整实现、弹性和回答超幂。 -/
def tg_round_m {d} (ω e δ ν κ l n r U D u b z χ σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆
    τ C V Q w η Z a H f₀ f₁ f₂ f₃ q₀ q₁ q₂ : Term d) : Formula 1 d := set[d] ⟪
    ⌜χ⌝ₛ ∈ ⌜τ⌝ₛ ∧ ⌜κ⌝ₛ ∈ ⌜τ⌝ₛ ∧ ⌜τ⌝ₛ ∈ ⌜δ⌝ₛ ∧
    (∃ ξ ζ, ⌜Formula.isSuccessor⌝ₚ(ξ, ⌜ν⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(ζ, ξ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜η⌝ₛ, ζ)) ∧
    ⌜v_sigma_m⌝ₚ(⌜η⌝ₛ, ⌜Z⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜a⌝ₛ, ⌜Z⌝ₛ, ⌜H⌝ₛ) ∧
    ⌜ee_language_m⌝ₚ(⌜ω⌝ₛ, ⌜τ⌝ₛ, ⌜n⌝ₛ, ⌜C⌝ₛ, ⌜V⌝ₛ, ⌜Q⌝ₛ, ⌜f₀⌝ₛ, ⌜f₁⌝ₛ, ⌜f₂⌝ₛ, ⌜f₃⌝ₛ) ∧
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜Z⌝ₛ, ⌜H⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, ⌜δ⌝ₛ, ⌜V⌝ₛ, ⌜Q⌝ₛ, ⌜w⌝ₛ) ∧
    ⌜ee_elastic_m⌝ₚ(⌜f₀⌝ₛ, ⌜f₁⌝ₛ, ⌜f₂⌝ₛ, ⌜f₃⌝ₛ, ⌜w⌝ₛ) ∧
    ⌜tg_reply_language_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, ⌜τ⌝ₛ, ⌜C⌝ₛ, ⌜V⌝ₛ, ⌜Q⌝ₛ, ⌜q₀⌝ₛ, ⌜q₁⌝ₛ, ⌜q₂⌝ₛ) ∧
    ⌜q₀⌝ₛ ∈ ⌜w⌝ₛ ∧ ⌜q₁⌝ₛ ∈ ⌜w⌝ₛ ∧ ⌜q₂⌝ₛ ∈ ⌜w⌝ₛ ∧
    ⌜b⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜z⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜σ₀⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜σ₁⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜σ₂⌝ₛ ∈ ⌜ω⌝ₛ ∧
    ⌜σ₃⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜σ₄⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜σ₅⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜σ₆⌝ₛ ∈ ⌜ω⌝ₛ ∧
    ⌜fun ω κ δ l n U D u τ Q w b z r q h s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_image_m ω κ δ l n U D u τ Q w b z r q h
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜δ⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ, ⌜τ⌝ₛ, ⌜Q⌝ₛ, ⌜w⌝ₛ, ⌜b⌝ₛ, ⌜z⌝ₛ, ⌜q₀⌝ₛ, ⌜q₁⌝ₛ, ⌜q₂⌝ₛ,
        ⌜σ₀⌝ₛ, ⌜σ₁⌝ₛ, ⌜σ₂⌝ₛ, ⌜σ₃⌝ₛ, ⌜σ₄⌝ₛ, ⌜σ₅⌝ₛ, ⌜σ₆⌝ₛ)⟫

/-- 更新仅存在量化这一组共同见证，不重新选择其中的类型或查询。 -/
def tg_successor_m {d} (ω e δ ν κ l n r U D u b z χ σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ : Term d) : Formula 1 d := set[d] ⟪
  ∃ τ C V Q w η Z a H f₀ f₁ f₂ f₃ q₀ q₁ q₂,
    ⌜tg_round_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜δ⌝ₛ, ⌜ν⌝ₛ, ⌜κ⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ,
      ⌜b⌝ₛ, ⌜z⌝ₛ, ⌜χ⌝ₛ, ⌜σ₀⌝ₛ, ⌜σ₁⌝ₛ, ⌜σ₂⌝ₛ, ⌜σ₃⌝ₛ, ⌜σ₄⌝ₛ, ⌜σ₅⌝ₛ, ⌜σ₆⌝ₛ,
      τ, C, V, Q, w, η, Z, a, H, f₀, f₁, f₂, f₃, q₀, q₁, q₂)⟫

-- 绑定位置依次为原输入 ω,e,δ,S,ν,κ,k,l,n,α,A,c,R,r,B,U,D,P,u,v,b,a,z,χ,s,t,g，
-- 再接四个弹性查询与七个程序槽位。所有参数都在原模型中，不使用宿主自然数游戏。
def tg_seed0_m : Formula 1 38 := tg_seed_m
  (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8)
  (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14) (.bound 15) (.bound 16) (.bound 17)
  (.bound 18) (.bound 19) (.bound 20) (.bound 21) (.bound 22) (.bound 23) (.bound 24) (.bound 25) (.bound 26)
  (.bound 27) (.bound 28) (.bound 29) (.bound 30) (.bound 31) (.bound 32) (.bound 33) (.bound 34)
  (.bound 35) (.bound 36) (.bound 37)

def tg_successor0_m : Formula 1 38 := tg_successor_m
  (.bound 0) (.bound 1) (.bound 2) (.bound 4) (.bound 5) (.bound 7) (.bound 8) (.bound 13) (.bound 15)
  (.bound 16) (.bound 18) (.bound 20) (.bound 22) (.bound 23) (.bound 31) (.bound 32) (.bound 33)
  (.bound 34) (.bound 35) (.bound 36) (.bound 37)

-- 前十六个位置按量词栈次序保存新见证，后面逐项保留原三十八个输入。
def tg_witness0_m : Formula 1 54 := tg_round_m
  (.bound 16) (.bound 17) (.bound 18) (.bound 20) (.bound 21) (.bound 23) (.bound 24) (.bound 29) (.bound 31)
  (.bound 32) (.bound 34) (.bound 36) (.bound 38) (.bound 39) (.bound 47) (.bound 48) (.bound 49)
  (.bound 50) (.bound 51) (.bound 52) (.bound 53)
  (.bound 15) (.bound 14) (.bound 13) (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8)
  (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)

/-- 一轮状态同时保存原树、元组和节点事实，避免搬运实现时遗失这些联系。 -/
def tg_round0_m : Formula 1 54 := .conj
  (tg_seed0_m.rename (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  tg_witness0_m

@[simp] theorem tg_seed0_closed_l : tg_seed0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_seed0_m, tg_seed_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ]
@[simp] theorem tg_successor0_closed_l : tg_successor0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_successor0_m, tg_successor_m, tg_round_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ]
@[simp] theorem tg_witness0_closed_l : tg_witness0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_witness0_m, tg_round_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ]
@[simp] theorem tg_round0_closed_l : tg_round0_m.FreeClosed :=
  ⟨(Definitional.Formula.freeClosed_rename _ _).mpr tg_seed0_closed_l, tg_witness0_closed_l⟩

def tg_renewal_m : Formula 1 0 := Formula.forallClosure 38 (.imp tg_seed0_m tg_successor0_m)

theorem tg_renewal_closed_l : tg_renewal_m.FreeClosed := 
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨tg_seed0_closed_l, tg_successor0_closed_l⟩

/-- 原句子的真实实例来自已经完成的每轮更新证明。 -/
theorem tg_renewal_true_l (hZFC : M.Models ZFC) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0, ε⟩ : Env M 0) tg_renewal_m := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  simp only [tg_seed0_m, tg_successor0_m, tg_seed_m, tg_successor_m, tg_round_m, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_mem_iff, woodin_sat_l I hZF.1, tg_low_sat_l hZF, Formula.satisfies_isSuccessor_iff,
    v_sat_l I hZF.1, smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF), ee_language_sat_l hZFC,
    td_dcp_sat_l I hZF.1, ee_elastic_sat_l, rd_entry0_sat_l hZF.1, sg_set_sat_l I hZF.1,
    tg_node_sat_l I hZF.1, ts_program_sat_l hZF, Formula.satisfies_exists_iff,
    tg_reply_language_sat_l hZF, v_sigma_sat_l (ZF.modelsKP hZF), tg_image_sat_l (ZF.modelsKP hZF),
    Definitional.Term.eval_weaken, tt_eval_cases_l]
  rintro ⟨hω, he, heω, hd, low, root, hκδ, _, succ, height, hA, model, type, language, drop,
    elastic, first, last, set, node, prog, hχ, _⟩
  obtain ⟨τ, C, V, Q, w, η, Z, d, H, q', p, X, K, R₀, L, F, c₀, d₀, Y, T, j, κ', U', D', u',
    hχτ, hκτ, hτδ, level, hZ, model', lang, real, el, target, hX, source, hLδ, hκL, hτL,
    loc, inacc, strength, mx, my, ultra, critical, bound, κlimit, hU, hD, hu, pool, reply⟩ :=
    low.step_l hZFC hω he heω hd root hκδ succ height hA model type language drop elastic first last set node prog hχ
  have limit := inacc.limit_l (ZF.modelsKP hZF) source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair
  obtain ⟨W, rank⟩ := ZF.v_exists_l I hZF limit.1
  have hwL := ordinal_down_l (ZF.modelsKP hZF) (hω.isOrdinal (ZF.modelsKP hZF)) limit.1 source.below hκL
  have hVW := tt_constants_rank_l hZF rank limit hτL lang.rank lang.constants
  have hQW := lang.pool.rank_mem_l (ZF.modelsKP hZF) hω rank limit (ZF.v_ordinal_mem_l I hZF rank hwL) real.finite hVW
  have hs i := hω.transitive (ZF.modelsKP hZF) _ prog.length _ (prog.slots i)
  have seen : M.mem p.root w ∧ M.mem p.bound w ∧ M.mem p.height w := by
    obtain ⟨_, _, _, _, hr, hb, hh⟩ := reply
    exact ⟨hr, hb, hh⟩
  exact ⟨τ, C, V, Q, w, η, Z, d, H, q'.largest, q'.domain, q'.inaccessible, q'.stretch, p.root, p.bound, p.height,
    hχτ, hκτ, hτδ, level, hZ, model', lang, real, el, target, seen.1, seen.2.1, seen.2.2,
    prog.length, prog.natural, hs 0, hs 1, hs 2, hs 3, hs 4, hs 5, hs 6,
    X, K, R₀, L, F, c₀, d₀, Y, T, j, κ', U', D', u',
    hX, source, hLδ, hκL, hτL, ⟨W, rank, hQW⟩, loc, inacc, strength, mx, my, ultra, critical, bound, κlimit, hU, hD, hu, pool, reply⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 完整原回答在所属模型内的严格秩界

包含新临界点的极限秩层容纳原常量域、查询域及完整类型。
这些界和全部自然数程序参数直接取自本轮的语言、实现与回答公式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_round_members_l {ω η C α B : M.Domain} (hω : M.IsOmega ω)
    (rankC : V_d I η C) (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 54) (hw : (ρ.bound 16).val = ω)
    (rank : V_d I α B) (limit : M.IsLimitOrdinal α) (member : M.mem (ρ.bound 21).val B)
    (valid : Formula.satisfies ρ tg_round0_m) :
    M.mem (ρ.bound 31).val B ∧ M.mem (ρ.bound 32).val B ∧ M.mem (ρ.bound 34).val B ∧
      M.mem (ρ.bound 23).val ω ∧ M.mem (ρ.bound 24).val ω ∧
      M.mem (ρ.bound 22).val ω ∧ Fn0_d (ρ.bound 22).val ω (ρ.bound 41).val ∧ M.mem (ρ.bound 41).val B ∧
      ∀ i : Fin 9, M.mem (ρ.bound ([36,38,47,48,49,50,51,52,53].get i)).val ω := by
  obtain ⟨seed, answer⟩ := (Formula.satisfies_conj_iff ..).mp valid
  have seed := (Formula.satisfies_rename ..).mp seed
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff] at seed
  obtain ⟨_, _, _, _, _, _, _, first, successor, _, _, _, realized, language,
    _, _, _, _, _, _, _, _, _, labels⟩ := seed
  simp only [ee_language_m, Formula.satisfies_bind, ee_language0_m,
    Formula.satisfies_conj_iff] at language
  obtain ⟨domain, hκ, base, constants, _⟩ := language
  have hκ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ρ.bound 21)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp hκ)
  have hκα := ZF.v_ordinal_height_l hZF rank hκ.1 member
  obtain ⟨A, rA⟩ := ZF.v_exists_l I hZF hκ.1
  have hA := ZF.v_mem_l I hZF rA rankC
    (ZF.v_ordinal_height_l hZF rankC hκ.1 (ρ.bound 21).property)
  have base : Vr_d C (ρ.bound 21).val (ρ.bound 30).val :=
    (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc _ _ _).mp base
  have eq := vr_agree_l hZF fs.transitive (ρ.bound 30).property rA (fs.transitive A hA) base
  have full : V_d I (ρ.bound 21).val (ρ.bound 30).val := by rw [eq]; exact rA
  have constants := (tt_constants0_sat_l hZF.1 ..).mp
    ((rt_model_delta_l fs.transitive nc (tt_constants0_delta_l ..) _).mp constants)
  have hU : M.mem (ρ.bound 31).val B := tt_constants_rank_l hZF rank limit hκα full constants
  have hwB : M.mem ω B := v_subset_mem_l I rank member
    (hω.subset_limitOrdinal (ZF.modelsKP hZF) hκ)
  simp only [tt_realized_m, Formula.satisfies_bind, tt_realized0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at realized
  obtain ⟨_, hn, _, _, _, pool, truth⟩ := realized
  have hn : M.mem (ρ.bound 24).val ω := hw ▸ hn
  obtain ⟨A₀, E, _, _, names, seq, product⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc _ _ _ _ _ (by exact hw)).mp pool
  have actual : Tt_pool_d I ω (ρ.bound 24).val (ρ.bound 31).val (ρ.bound 33).val :=
    ⟨A₀, E, names, seq, product⟩
  have hP := actual.rank_mem_l (ZF.modelsKP hZF) hω rank limit hwB hn hU
  simp only [ee_domain_pack_m, Formula.satisfies_bind, ee_domain_pack0_m,
    Formula.satisfies_conj_iff] at domain
  obtain ⟨A₁, E₁, _, _, names₁, seq₁, product₁⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc _ _ _ _ _ (by exact hw)).mp domain.2.1
  have small : Tt_pool_d I ω (ρ.bound 23).val (ρ.bound 31).val (ρ.bound 32).val :=
    ⟨A₁, E₁, names₁, seq₁, product₁⟩
  -- dcp 的后继关系把旧元数放回同一个内部 ω。
  have successor : (rt_model_l C nc).SuccessorOf (ρ.bound 24) (ρ.bound 23) :=
    (Formula.satisfies_isSuccessor_iff ..).mp successor
  have hl := hω.transitive (ZF.modelsKP hZF) _ hn _ successor.predecessor_mem
  have first : (rt_model_l C nc).SuccessorOf (ρ.bound 23) (ρ.bound 22) :=
    (Formula.satisfies_isSuccessor_iff ..).mp first
  have hk := hω.transitive (ZF.modelsKP hZF) _ hl _ first.predecessor_mem
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have labels : Fn0_d (ρ.bound 22) (ρ.bound 16) (ρ.bound 41) := (fn0_sat_l ext ..).mp labels
  let ζ : Env (rt_model_l C nc) 3 := ⟨fun i => [ρ.bound 22,ρ.bound 16,ρ.bound 41].get i,ρ.free⟩
  have labels : Fn0_d (M := M) (ρ.bound 22).val ω (ρ.bound 41).val := hw ▸
    (fn0_sat_l hZF.1 _ (.bound 0) (.bound 1) (.bound 2)).mp
      ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2)) ζ).mp
        ((fn0_sat_l ext ζ (.bound 0) (.bound 1) (.bound 2)).mpr labels))
  have ht : M.mem (ρ.bound 41).val B := v_relation_mem_l I rank limit hwB (fun p hp => by
    obtain ⟨i,hi,v,hv,pair⟩ := labels.1 p hp
    exact ⟨i,hω.transitive (ZF.modelsKP hZF) _ hk i hi,v,hv,pair⟩)
  have hD := small.rank_mem_l (ZF.modelsKP hZF) hω rank limit hwB hl hU
  simp only [tt_truth_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at truth
  have sub : M.MemberSubset (ρ.bound 34).val (ρ.bound 33).val := fun x hx =>
    ((truth ⟨x, fs.transitive _ (ρ.bound 34).property x hx⟩).mp hx).1
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff] at answer
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hb, hz, h₀, h₁, h₂, h₃, h₄, h₅, h₆, _⟩ := answer
  exact ⟨hU, hD, v_subset_mem_l I rank hP sub, hl, hn, hk, labels, ht, Fin.cases (hw ▸ hb)
    (Fin.cases (hw ▸ hz) (Fin.cases (hw ▸ h₀) (Fin.cases (hw ▸ h₁) (Fin.cases (hw ▸ h₂)
      (Fin.cases (hw ▸ h₃) (Fin.cases (hw ▸ h₄) (Fin.cases (hw ▸ h₅)
        (Fin.cases (hw ▸ h₆) (fun i => Fin.elim0 i)))))))))⟩

end YesMetaZFC.SetTheory.LargeCardinal
