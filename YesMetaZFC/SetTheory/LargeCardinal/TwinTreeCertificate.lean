import YesMetaZFC.SetTheory.LargeCardinal.TwinTreeGround
import YesMetaZFC.SetTheory.LargeCardinal.TwinTreeRank

/-! # 双树决定性的赢家与可持久验证证书

输出的策略既赢得原正树投影，又带有反方反例树的实际序数秩。
两树地面互斥只用于从地面赢家导出反例树无枝；秩界无需小于 Woodin。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Td_winner_d (b : Bool) (ω A Y F T Z G S H J B W σ : M.Domain) : Prop where
  finite : Fseq_space_d I ω A H
  runs : M.IsFunctionSpace I B ω A
  turns : ∀ n, M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n
  payoff : ∀ x, M.mem x W ↔ M.mem x B ∧ Tp_projection_d I ω A Y F T x
  win : Cg_win_d I b ω A H J B W σ
  certificate : Tp_certificate_d hZF b ω A (if b then Z else Y) (if b then G else F)
    (if b then S else T) H J σ

theorem tp_payoff_l (ω A Y F T B : M.Domain) :
    ∃ W, ∀ x, M.mem x W ↔ M.mem x B ∧ Tp_projection_d I ω A Y F T x := by
  let ρ : Env M 5 := ⟨fun i => [ω, A, Y, F, T].get i, fun _ => ω⟩
  let φ : UnarySchema 5 := { body := tp_projection_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) .newest }
  obtain ⟨W, read⟩ := ZF.separation_exists_d hZF φ ρ B
  exact ⟨W, fun x => (read x).trans (and_congr_right fun _ => tp_projection_sat_l I hZF.1 ..)⟩

theorem td_winner_l {ω A Γ Y F T Λ Z G S : M.Domain} (hw : M.IsOmega ω) (dc : Dc_d I ω)
    (pair : M.IsCartesianProduct I Y A Γ) (space : Fseq_space_d I ω Y F) (tree : Tree_d F T)
    (pair' : M.IsCartesianProduct I Z A Λ) (space' : Fseq_space_d I ω Z G) (tree' : Tree_d G S)
    (disjoint : ∀ x, Tp_projection_d I ω A Y F T x → ¬ Tp_projection_d I ω A Z G S x)
    (winning : Tp_win_d hZF true true ω A Y F T ∨ Tp_win_d hZF false false ω A Z G S) :
    ∃ b H J B W σ, Td_winner_d hZF b ω A Y F T Z G S H J B W σ := by
  rcases winning with ⟨H, J, B, W, σ, hist, runs, turns, payoff, win⟩ |
    ⟨H, J, B, V, σ, hist, runs, turns, payoff, win⟩
  · have avoid x (fx : M.IsSetFunctionFromTo I x ω A) (follow : Cg_follows_d I true ω J σ x) :
        ¬ Tp_projection_d I ω A Z G S x :=
      disjoint x ((payoff x).mp (win.2 x ((runs x).mpr fx) follow)).2
    exact ⟨true, H, J, B, W, σ, hist, runs, turns, payoff, win,
      tp_certificate_l hZF hw dc pair' space' tree' hist win.1 avoid⟩
  · have avoid x (fx : M.IsSetFunctionFromTo I x ω A) (follow : Cg_follows_d I false ω J σ x) :
        ¬ Tp_projection_d I ω A Y F T x := by
      intro yes
      have enters : Tp_projection_d I ω A Z G S x := Classical.byContradiction
        (fun no => win.2 x ((runs x).mpr fx) follow ((payoff x).mpr ⟨(runs x).mpr fx, no⟩))
      exact disjoint x yes enters
    obtain ⟨W, payoff'⟩ := tp_payoff_l hZF ω A Y F T B
    exact ⟨false, H, J, B, W, σ, hist, runs, turns, payoff',
      ⟨win.1, fun x hx follow yes => avoid x ((runs x).mp hx) follow ((payoff' x).mp yes).2⟩,
      tp_certificate_l hZF hw dc pair space tree hist win.1 avoid⟩

variable (hZFC : M.Models ZFC)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hM)

/-- 优化稿 2.3：一次原坍缩的强迫穷尽给出地面互补、实际赢家及反方树秩。 -/
theorem td_determinacy_l {ω δ A X a Γ Y F T Λ Z G S C Q p : M.Domain}
    (hw : M.IsOmega ω) (hd : Woodin_d K δ) (rank : V_d K δ X) (hA : M.mem A X) (ha : M.mem a A)
    (pair : M.IsCartesianProduct K Y A Γ) (space : Fseq_space_d K ω Y F) (tree : Tree_d F T)
    (pair' : M.IsCartesianProduct K Z A Λ) (space' : Fseq_space_d K ω Z G) (tree' : Tree_d G S)
    (disjoint : ∀ x, Tp_projection_d K ω A Y F T x → ¬ Tp_projection_d K ω A Z G S x)
    (collapse : Fseq_space_d K ω δ C)
    (order : ∀ r s, Entry_d M r s Q ↔ M.mem r C ∧ M.mem s C ∧ M.MemberSubset s r)
    (hp : M.mem p C) (hn : p ≠ C) (η : Env M 8)
    (checks : ∀ i, Check_d M p ([ω, A, Y, F, T, Z, G, S].get i) (η.bound i))
    (force : Forces_d M C Q C td_cover0_m η p) :
    (∀ x, M.IsSetFunctionFromTo K x ω A →
      (Tp_projection_d K ω A Y F T x ↔ ¬ Tp_projection_d K ω A Z G S x)) ∧
    ∃ b H J B W σ, Td_winner_d hM b ω A Y F T Z G S H J B W σ := by
  obtain ⟨cover, winning⟩ := td_ground_l hZFC hw hd rank hA ha pair space tree pair' space' tree'
    collapse order hp hn η checks force
  exact ⟨fun x fx => ⟨disjoint x, fun no => (cover x fx).elim id (fun yes => (no yes).elim)⟩,
    td_winner_l hM hw (ZFC.dc_l K hZFC hw) pair space tree pair' space' tree' disjoint winning⟩

end YesMetaZFC.SetTheory.LargeCardinal
