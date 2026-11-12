import YesMetaZFC.SetTheory.Descriptive.Game.GameShift
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.SetTheory.Descriptive.Game.ClosedDeterminacy

/-! # 只在本方回合定义的实际策略

本方有限历史由原有限空间分离得到。已有全历史策略限制到该域后，
服从条件不变；空字母表没有 II 回合历史，空图便是实际 II 策略。
最后的策略构造只在元层保留任意对局性质，不把该性质用于分离。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

/-- 策略的定义域恰为该玩家负责的全部内部有限历史。 -/
def Gm_turns_d (I : kpair_convention_l.Interpretation M) (b : Bool)
    (ω A F O : M.Domain) : Prop :=
  ∀ s, M.mem s O ↔ M.mem s F ∧ ∃ n, M.mem n ω ∧ Fn0_d n A s ∧ Gm_turn_d I b ω n

def Gm_strategy_d (I : kpair_convention_l.Interpretation M) (b : Bool)
    (ω A F σ : M.Domain) : Prop := ∃ O, Gm_turns_d I b ω A F O ∧ Fn0_d O A σ

/-- 分离只读取有限历史的实际长度和回合，不涉及任何收益性质。 -/
theorem gm_turns_l (hZF : M.Models ZF) (b : Bool) (ω A F : M.Domain) :
    ∃ O, Gm_turns_d (kp_pair_l (ZF.modelsKP hZF)) b ω A F O := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 2 := ⟨fun i => [ω,A].get i,fun _ => ω⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪∃ n,
    n ∈ ⌜(.bound 1 : Term 3)⌝ₛ ∧ ⌜fn0_m⌝ₚ(n,⌜(.bound 2 : Term 3)⌝ₛ,⌜(.newest : Term 3)⌝ₛ) ∧
      ⌜(gm_turn_m (𝒞 := kpair_convention_l) b)⌝ₚ(⌜(.bound 1 : Term 3)⌝ₛ,n)⟫ }
  have sat s : φ.denote ρ s ↔ ∃ n, M.mem n ω ∧ Fn0_d n A s ∧ Gm_turn_d I b ω n := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff,fn0_sat_l hZF.1,gm_turn_sat_l I hZF.1 b,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨O,read⟩ := ZF.separation_exists_d hZF φ ρ F
  exact ⟨O,fun s => (read s).trans (and_congr_right fun _ => sat s)⟩

/-- 实际全策略的本方限制只需 KP 的有界图分离。 -/
theorem Gm_turns_d.restrict_l (hKP : M.Models KP)
    {b : Bool} {ω A F O σ : M.Domain}
    (turns : Gm_turns_d (kp_pair_l hKP) b ω A F O) (full : Fn0_d F A σ) :
    ∃ τ, Fn0_d O A τ ∧ M.IsRestrictionOf (kp_pair_l hKP) τ σ O := by
  obtain ⟨τ,read⟩ := res0_exists_l hKP σ O A
  have cut := res0_restriction_l hKP full read
  exact ⟨τ,fn0_of_function_l hKP (cut.isSetFunctionFromTo (fn0_function_l hKP full)
    (fun s hs => ((turns s).mp hs).1)),cut⟩

/-- 对实际无限对局，删去非本方回合的策略值完全不改变服从条件。 -/
theorem Gm_turns_d.follows_l (hKP : M.Models KP)
    {b : Bool} {ω A F O σ τ f : M.Domain}
    (turns : Gm_turns_d (kp_pair_l hKP) b ω A F O) (hw : M.IsOmega ω)
    (space : Fseq_space_d (kp_pair_l hKP) ω A F) (input : Fn0_d ω A f)
    (cut : M.IsRestrictionOf (kp_pair_l hKP) τ σ O) :
    Gm_follows_d (kp_pair_l hKP) b ω τ f ↔ Gm_follows_d (kp_pair_l hKP) b ω σ f := by
  constructor
  · intro follows n hn own s rest a point
    exact ((cut.2 s a).mp (follows n hn own s rest a point)).2
  · intro follows n hn own s rest a point
    have finite := rest.isSetFunctionFromTo (fn0_function_l hKP input) (hw.transitive hKP n hn)
    have hs : M.mem s O := (turns s).mpr
      ⟨(space s).mpr ⟨n,hn,finite⟩,n,hn,fn0_of_function_l hKP finite,own⟩
    exact (cut.2 s a).mpr ⟨hs,follows n hn own s rest a point⟩

/-- 空字母表的有限历史只能有空长度，因而没有 II 负责的回合。 -/
theorem Gm_turns_d.empty_l (hZF : M.Models ZF) {ω A F e : M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ a, ¬ M.mem a A) (he : ∀ s, ¬ M.mem s e) :
    Gm_turns_d (kp_pair_l (ZF.modelsKP hZF)) false ω A F e := by
  intro s
  refine ⟨fun hs => (he s hs).elim,?_⟩
  rintro ⟨_,n,_,fn,odd⟩
  have hn : ∀ i, ¬ M.mem i n := by
    intro i hi
    obtain ⟨a,ha,_⟩ := fn.2.1 i hi
    exact empty a ha
  exact (odd (gm_even_zero_l (kp_pair_l (ZF.modelsKP hZF)) hZF hw hn)).elim

/-- 空图在空本方域上是实际 II 策略，且不存在字母取值的无限输入。 -/
theorem gm_ii_empty_l (hZF : M.Models ZF) {ω A F : M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ a, ¬ M.mem a A) :
    ∃ σ, Gm_strategy_d (kp_pair_l (ZF.modelsKP hZF)) false ω A F σ ∧
      ∀ f, ¬ Fn0_d ω A f := by
  obtain ⟨e,he,heω⟩ := hw.1.1
  have fn : Fn0_d e A e := ⟨fun p hp => (he p hp).elim,
    fun s hs => (he s hs).elim,fun s hs => (he s hs).elim⟩
  refine ⟨e,⟨e,Gm_turns_d.empty_l hZF hw empty he,fn⟩,?_⟩
  intro f input
  obtain ⟨a,ha,_⟩ := input.2.1 e heω
  exact empty a ha

/-- 实际非空总策略构造自动给出任意字母表上的 II 策略，空集分支无需备用字母。 -/
theorem gm_ii_strategy_l (hZF : M.Models ZF) {ω A F : M.Domain} {P : M.Domain → Prop}
    (hw : M.IsOmega ω) (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω A F)
    (produce : ∀ a, M.mem a A → ∃ σ, Fn0_d F A σ ∧
      ∀ f, Fn0_d ω A f → Gm_follows_d (kp_pair_l (ZF.modelsKP hZF)) false ω σ f → P f) :
    ∃ σ, Gm_strategy_d (kp_pair_l (ZF.modelsKP hZF)) false ω A F σ ∧
      ∀ f, Fn0_d ω A f → Gm_follows_d (kp_pair_l (ZF.modelsKP hZF)) false ω σ f → P f := by
  classical
  by_cases inhabited : ∃ a, M.mem a A
  · obtain ⟨a,ha⟩ := inhabited
    obtain ⟨σ,full,property⟩ := produce a ha
    obtain ⟨O,turns⟩ := gm_turns_l hZF false ω A F
    obtain ⟨τ,fn,cut⟩ := turns.restrict_l (ZF.modelsKP hZF) full
    exact ⟨τ,⟨O,turns,fn⟩,fun f input follows => property f input
      ((turns.follows_l (ZF.modelsKP hZF) hw space input cut).mp follows)⟩
  · obtain ⟨σ,strategy,none⟩ := gm_ii_empty_l (F := F) hZF hw (fun a ha => inhabited ⟨a,ha⟩)
    exact ⟨σ,strategy,fun f input _ => (none f input).elim⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 只定义在本方回合的策略全域化

`Gm_strategy_d` 的函数图只覆盖本方负责的有限历史。这里在其余历史上
填入一个固定字母，得到 scheduled game 所需的全域函数，并保留原图上的值。
-/
namespace YesMetaZFC.SetTheory.Descriptive

open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem Gm_strategy_d.totalize_l
    (hZF : M.Models ZF)
    {A F O σ a : M.Domain}
    (part : Fn0_d O A σ) (ha : M.mem a A) :
    ∃ τ, Fn0_d F A τ ∧
      ∀ h v, Rd_entry_d h v τ ↔ M.mem h F ∧
        ((M.mem h O ∧ Rd_entry_d h v σ) ∨ (¬ M.mem h O ∧ v = a)) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 3 := ⟨fun i => [a, σ, O].get i, fun _ => O⟩
  let φ : BinarySchema 3 := {
    body := .disj
      (.conj (.mem (.bound 1) (.bound 4))
        (rd_entry0_m (.bound 1) .newest (.bound 3)))
      (.conj (.neg (.mem (.bound 1) (.bound 4)))
        (Formula.extensionalEq .newest (.bound 2))) }
  have sat h v : φ.denote ρ h v ↔
      (M.mem h O ∧ Rd_entry_d h v σ) ∨ (¬ M.mem h O ∧ v = a) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
      rd_entry0_sat_l hZF.1, Definitional.Term.eval_newest,
      Term.eval_bound_one_push, Term.eval_bound_zero_push,
      Term.eval_bound_two_push, Term.eval_bound_three_push,
      Term.eval_bound_four_push]
    simp [ρ]
  have total h (hh : M.mem h F) : ∃ v, φ.denote ρ h v := by
    by_cases ho : M.mem h O
    · obtain ⟨v, hv, hσ⟩ := (part.2.1 h ho)
      exact ⟨v, (sat h v).mpr (Or.inl ⟨ho, hσ⟩)⟩
    · exact ⟨a, (sat h a).mpr (Or.inr ⟨ho, rfl⟩)⟩
  have unique h (hh : M.mem h F) v w (hv : φ.denote ρ h v)
      (hw : φ.denote ρ h w) : v = w := by
    rcases (sat h v).mp hv with ⟨hp, hv⟩ | ⟨hn, rfl⟩
    · rcases (sat h w).mp hw with ⟨_, hw⟩ | ⟨hn', _⟩
      · exact (fn0_function_l (ZF.modelsKP hZF) part).1.2 h v w hv hw
      · exact (hn' hp).elim
    · rcases (sat h w).mp hw with ⟨hp, _⟩ | ⟨_, rfl⟩
      · exact (hn hp).elim
      · rfl
  obtain ⟨τ, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (fun h hh => total h hh)
    (fun h hh v w hv hw => unique h hh v w hv hw)
    (by
      intro h v _ hv
      rcases (sat h v).mp hv with ⟨ho, hσ⟩ | ⟨_, rfl⟩
      · exact (part.bound_l hσ).2
      · exact ha)
  refine ⟨τ, fn0_of_function_l (ZF.modelsKP hZF) fn, fun h v => ?_⟩
  exact (graph h v).trans (and_congr_right fun _ => sat h v)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 本方回合策略到固定时序策略

将只在本方回合定义的 `Gm_strategy_d` 全域化，并在奇数时序上恢复同一服从关系。
该接口只处理策略域，不对收益集合作任何特殊假设。
-/
namespace YesMetaZFC.SetTheory.Descriptive

open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem Gm_strategy_d.to_cg_win_l
    (hZF : M.Models ZF)
    {ω A F J B W σ a : M.Domain}
    {P : M.Domain → Prop}
    (hw : M.IsOmega ω)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω A F)
    (functions : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) B ω A)
    (turns : ∀ n, M.mem n J ↔
      M.mem n ω ∧ Gm_even_d (kp_pair_l (ZF.modelsKP hZF)) ω n)
    (payoff : ∀ f, M.mem f W ↔ M.mem f B ∧ P f)
    (strategy : Gm_strategy_d (kp_pair_l (ZF.modelsKP hZF)) false ω A F σ)
    (produce : ∀ f, Fn0_d ω A f →
      Gm_follows_d (kp_pair_l (ZF.modelsKP hZF)) false ω σ f → ¬ P f)
    (ha : M.mem a A) :
    ∃ τ, Cg_win_d (kp_pair_l (ZF.modelsKP hZF)) false ω A F J B W τ := by
  obtain ⟨O, turnsO, part⟩ := strategy
  obtain ⟨τ, full, spec⟩ := Gm_strategy_d.totalize_l hZF part ha
  refine ⟨τ, full, ?_⟩
  intro f hf follows
  have input := fn0_of_function_l (ZF.modelsKP hZF) ((functions f).mp hf)
  have follow_eq :
      Cg_follows_d (kp_pair_l (ZF.modelsKP hZF)) false ω J τ f ↔
        Gm_follows_d (kp_pair_l (ZF.modelsKP hZF)) false ω σ f := by
    constructor
    · intro hg n hn hown s cut v point
      have finite := cut.isSetFunctionFromTo
        (fn0_function_l (ZF.modelsKP hZF) input)
        (hw.transitive (ZF.modelsKP hZF) n hn)
      have hsF := (space s).mpr ⟨n, hn, finite⟩
      have hodd : ¬ M.mem n J := by
        intro hnJ
        exact hown ((turns n).mp hnJ).2
      have hsO : M.mem s O := (turnsO s).mpr
        ⟨hsF, ⟨n, hn, fn0_of_function_l (ZF.modelsKP hZF) finite, hown⟩⟩
      have hτ : Rd_entry_d s v τ := hg n hn hodd s cut v point
      rcases (spec s v).mp hτ with ⟨_, hσ | hdefault⟩
      · exact hσ.2
      · exact (hdefault.1 hsO).elim
    · intro hc n hn hodd s cut v point
      have finite := cut.isSetFunctionFromTo
        (fn0_function_l (ZF.modelsKP hZF) input)
        (hw.transitive (ZF.modelsKP hZF) n hn)
      have hsF := (space s).mpr ⟨n, hn, finite⟩
      have hodd' : ¬ M.mem n J := by
        simpa only [Bool.false_eq_true, ↓reduceIte] using hodd
      have own : Gm_turn_d (kp_pair_l (ZF.modelsKP hZF)) false ω n := by
        change ¬ Gm_even_d (kp_pair_l (ZF.modelsKP hZF)) ω n
        intro even
        exact hodd' ((turns n).mpr ⟨hn, even⟩)
      have hsO : M.mem s O := (turnsO s).mpr
        ⟨hsF, ⟨n, hn, fn0_of_function_l (ZF.modelsKP hZF) finite, own⟩⟩
      have hσ : Rd_entry_d s v σ := hc n hn own s cut v point
      exact (spec s v).mpr ⟨hsF, Or.inl ⟨hsO, hσ⟩⟩
  intro hW
  exact (produce f input (follow_eq.mp follows)) ((payoff f).mp hW).2

end YesMetaZFC.SetTheory.Descriptive
