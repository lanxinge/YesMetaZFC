import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakPublic
import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakWinning

/-! # 公开策略给出的正是合法运行中的原共尾枝 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Wi_play_d (ω a A S F R α ξ B : M.Domain) : Prop := ∃ H t s β T Q G P,
  M.IsRestrictionOf I H R α ∧ Rd_entry_d ξ t F ∧ Rd_entry_d α s R ∧ Rd_quad_d s T Q G P ∧
    M.SuccessorOf β α ∧ Wi_state_d hZF ω β T Q G a A S P ∧ Wi_success_d hZF ω α t B Q G

theorem Wi_strategy_d.play_l {ω a A S o s₀ Ψ Ω Λ Z D Γ F R α ξ F' B : M.Domain}
    (strategy : Wi_strategy_d hZF o Ψ Ω Z D Γ) (hΨ : M.IsSetFunction I Ψ)
    (ho : ∀ x, ¬ M.mem x o) (moves : Fn0_d Λ Z F) (run : Wi_run_d hZF o Ψ F Λ Z R)
    (wins : ∀ i s, Rd_entry_d i s R → Wi_reply_d hZF ω a A S o s₀ Ψ F R i s)
    (hα : M.mem α Λ) (succ : M.SuccessorOf α ξ) (rf : M.IsRestrictionOf I F' F α)
    (chosen : Rd_entry_d F' B Γ) : Wi_play_d hZF ω a A S F R α ξ B := by
  obtain ⟨β, η, H, t, r, u, v, hβ, ff, play, ht, pack, edge, pair⟩ := ((strategy.2.2 F' B).mp chosen).2
  have fn := fn0_of_function_l (ZF.modelsKP hZF)
    (rf.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) moves) (run.1.1.transitive α hα))
  have eq := ff.domain_eq_l hZF.1 fn
  subst β
  have eq := Structure.SuccessorOf.predecessor_eq hZF.1 (play.1.1.mem hβ.predecessor_mem) hβ succ
  subst η
  obtain ⟨K, rk⟩ := ZF.exists_restriction hZF I R α
  have eq := (run.restrict_moves_l hZF hα rk rf).unique_l hZF (fn0_function_l (ZF.modelsKP hZF) ff).1 hΨ play
  have rh : M.IsRestrictionOf I H R α := eq ▸ rk
  have move := ((rf.2 ξ t).mp ht).2
  obtain ⟨s, _, hs⟩ := run.1.2.2.2 α hα
  obtain ⟨J, t', r', u', C, rj, input, pack', edge', pair', answer⟩ := wins α s hs
  have eq := rj.eq hZF.1 rh
  subst J
  have eq := input.unique_l (ZF.modelsKP hZF) play.1.1 (fn0_function_l (ZF.modelsKP hZF) moves).1 (Or.inl ⟨ξ, succ, move⟩)
  subst t'
  obtain ⟨p, pp, pr⟩ := pack
  obtain ⟨q, pq, qr⟩ := pack'
  have eq := kpair_unique_l M hZF.1 pq pp
  subst q
  have eq := kpair_unique_l M hZF.1 qr pr
  subst r'
  have eq := hΨ.2 r u' u edge' edge
  subst u'
  have eq := (kpair_injective_l M pair' pair).1
  subst C
  obtain ⟨β, T, Q, G, P, hb, ps, state, _, cases⟩ := answer
  refine ⟨H, t, s, β, T, Q, G, P, rh, move, hs, ps, hb, state, ?_⟩
  rcases cases with ⟨eq, _⟩ | step | ⟨limit, _⟩
  · exact (ho ξ (eq ▸ succ.predecessor_mem)).elim
  · exact step
  · obtain ⟨j, hj, hξj⟩ := limit.2.2 ξ succ.predecessor_mem
    rcases (succ j).mp hj with hj | eq
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ξ ((limit.1.mem succ.predecessor_mem).transitive j hj ξ hξj)).elim
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ξ (hZF.1.eq_of_same_members j ξ eq ▸ hξj)).elim

end YesMetaZFC.SetTheory.LargeCardinal
