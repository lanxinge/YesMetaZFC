import YesMetaZFC.Model.SetTheory.Internal.TypeGameNode
import YesMetaZFC.SetTheory.Descriptive.ScheduledGame
import YesMetaZFC.SetTheory.Descriptive.Game

/-! # 三坐标树的投影博弈

两条策略转移共用同一个实际收益集合：树体第一投影的补集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_projection_d (ω Y T S x : M.Domain) : Prop := ∃ q t u,
  Fn0_d ω Y q ∧ Branch_d T S q ∧ Tg_graph_d I ω t ∧ Tg_graph_d I ω u ∧ Tg_join_d I ω x t u q

def tg_projection_m {d} (ω Y T S x : Term d) : Formula 1 d := set[d] ⟪∃ q t u,
  ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜Y⌝ₛ,q) ∧ ⌜branch_m⌝ₚ(⌜T⌝ₛ,⌜S⌝ₛ,q) ∧
  ⌜tg_graph_m⌝ₚ(⌜ω⌝ₛ,t) ∧ ⌜tg_graph_m⌝ₚ(⌜ω⌝ₛ,u) ∧ ⌜tg_join_m⌝ₚ(⌜ω⌝ₛ,⌜x⌝ₛ,t,u,q)⟫
derive_free_closed tg_projection_m

theorem tg_projection_sat_l {d} (ρ : Env M d) (ω Y T S x : Term d) :
    Formula.satisfies ρ (tg_projection_m ω Y T S x) ↔
      Tg_projection_d hZF (ω.eval ρ) (Y.eval ρ) (T.eval ρ) (S.eval ρ) (x.eval ρ) := by
  simp only [tg_projection_m, Tg_projection_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hZF.1, branch_sat_l, tg_graph_sat_l I hZF.1, tg_join_sat_l I hZF.1, Definitional.Term.eval_weaken]; rfl

def Tg_projection_win_d (b : Bool) (ω A Y T S : M.Domain) : Prop :=
  ∃ F J B W σ, Fseq_space_d I ω A F ∧ M.IsFunctionSpace I B ω A ∧
    (∀ n, M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n) ∧
    (∀ f, M.mem f W ↔ M.mem f B ∧ ¬ Tg_projection_d hZF ω Y T S f) ∧ Cg_win_d I b ω A F J B W σ

theorem tg_projection_game_l {ω : M.Domain} (hw : M.IsOmega ω) (A Y T S : M.Domain) :
    ∃ F J B W, Fseq_space_d I ω A F ∧ M.IsFunctionSpace I B ω A ∧
      (∀ n, M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n) ∧
      ∀ f, M.mem f W ↔ M.mem f B ∧ ¬ Tg_projection_d hZF ω Y T S f := by
  obtain ⟨F, finite⟩ := ZF.fseq_space_exists_l I hZF hw A
  obtain ⟨B, bs⟩ := ZF.exists_functionSpace hZF I ω A
  let η : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  let even : UnarySchema 1 := { body := gm_even_m (𝒞 := kpair_convention_l) (.bound 1) .newest }
  obtain ⟨J, js⟩ := ZF.separation_exists_d hZF even η ω
  have turns n : M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n :=
    (js n).trans (and_congr_right fun _ => gm_even_sat_l I hZF.1 (η.push n) (.bound 1) .newest)
  let ρ : Env M 4 := ⟨fun i => [ω, Y, T, S].get i, fun _ => ω⟩
  let φ : UnarySchema 4 := { body := .neg (tg_projection_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) .newest) }
  obtain ⟨W, ws⟩ := ZF.separation_exists_d hZF φ ρ B
  exact ⟨F, J, B, W, finite, bs, turns, fun f =>
    (ws f).trans (and_congr_right fun _ => (Formula.satisfies_neg_iff ..).trans (not_congr (tg_projection_sat_l hZF ..)))⟩

/-- 缺少空根时没有分支，实际常值策略已经获胜；不额外假设树非空。 -/
theorem tg_projection_no_root_l {ω A Y T S e a : M.Domain} (hw : M.IsOmega ω)
    (he : ∀ x, ¬ M.mem x e) (ha : M.mem a A) (space : Fseq_space_d I ω Y T) (root : ¬ M.mem e S) :
    Tg_projection_win_d hZF true ω A Y T S := by
  obtain ⟨F, J, B, W, finite, bs, turns, payoff⟩ := tg_projection_game_l hZF hw A Y T S
  obtain ⟨σ, fn, _⟩ := ZF.exists_constantFunction hZF I (source := F) ha
  refine ⟨F, J, B, W, σ, finite, bs, turns, payoff, fn0_of_function_l (ZF.modelsKP hZF) fn, fun f hf _ =>
    (payoff f).mpr ⟨hf, ?_⟩⟩
  rintro ⟨q, _, _, _, branch, _⟩
  have empty := tg_graph_empty_l I he
  exact root (branch e ((space e).mpr ⟨e, num_mem_l hZF.1 hw (show Num_d 0 e from he),
    empty.1, empty.2, fun i hi => (he i hi).elim⟩) (fun x hx => (he x hx).elim))

end YesMetaZFC.SetTheory.LargeCardinal
