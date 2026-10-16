import YesMetaZFC.SetTheory.LargeCardinal.TreeProjectionTransfer

/-! # 双树胜策的反方反例树秩

反例树由原树和服从原策略的历史树实际构造；证书含原策略图和一个
严格下降的有界序数秩。证书验证及向外保持仅需 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tp_certificate_d (b : Bool) (ω A Y F T H J σ : M.Domain) : Prop :=
  Fn0_d H A σ ∧ ∃ d K C α R, Tp_left_d I Y A d ∧
    (∀ s, M.mem s K ↔ M.mem s H ∧ Cg_follows_d I b ω J σ s) ∧
    Tp_filter_d I d F T K C ∧ Cg_rank_d ω Y C α R

theorem tp_certificate_l {b : Bool} {ω A Γ Y F T H J σ : M.Domain} (hw : M.IsOmega ω)
    (dc : Dc_d I ω) (pair : M.IsCartesianProduct I Y A Γ)
    (space : Fseq_space_d I ω Y F) (tree : Tree_d F T) (hist : Fseq_space_d I ω A H)
    (strategy : Fn0_d H A σ)
    (avoid : ∀ x, M.IsSetFunctionFromTo I x ω A → Cg_follows_d I b ω J σ x → ¬ Tp_projection_d I ω A Y F T x) :
    Tp_certificate_d hZF b ω A Y F T H J σ := by
  obtain ⟨d, left⟩ := tp_left_l I hZF pair
  obtain ⟨K, control⟩ := hg_strategy_exists_l hZF b ω H J σ
  obtain ⟨C, filter⟩ := tp_filter_l I hZF d F T K
  have treeC := filter.tree_l I hZF left space hist tree (hg_strategy_tree_l hZF hw hist control)
  obtain ⟨α, R, rank⟩ := tree_rank_l hZF hw dc space treeC (by
    intro q fq branch
    obtain ⟨x, fx, qx⟩ := ZF.fseq_compose_l I hZF left.1 fq
    have proj := (left.projection_l I hZF fq).mp qx
    obtain ⟨bt, bk⟩ := (filter.branch_l I hZF hw left space hist fq proj).mp branch
    exact avoid x fx ((hg_strategy_branch_l hZF hw hist control fx).mp bk) ⟨q, fq, bt, proj⟩)
  exact ⟨strategy, d, K, C, α, R, left, control, filter, rank⟩

theorem Tp_certificate_d.avoid_l {b : Bool} {ω A Y F T H J σ x : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω Y F) (tree : Tree_d F T) (hist : Fseq_space_d I ω A H)
    (cert : Tp_certificate_d hZF b ω A Y F T H J σ)
    (fx : M.IsSetFunctionFromTo I x ω A) (follows : Cg_follows_d I b ω J σ x) :
    ¬ Tp_projection_d I ω A Y F T x := by
  obtain ⟨_, d, K, C, α, R, left, control, filter, rank⟩ := cert
  rintro ⟨q, fq, branch, proj⟩
  have treeC := filter.tree_l I hZF left space hist tree (hg_strategy_tree_l hZF hw hist control)
  exact rank.no_branch_l hZF hw space treeC fq ((filter.branch_l I hZF hw left space hist fq proj).mpr
    ⟨branch, (hg_strategy_branch_l hZF hw hist control fx).mpr follows⟩)

variable {N : Structure.{v}} (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
include hi he

theorem Tp_certificate_d.image_l {b : Bool} {ω A Y F T H J σ : M.Domain}
    (space : Fseq_space_d I ω Y F) (hist : Fseq_space_d I ω A H)
    (cert : Tp_certificate_d hZF b ω A Y F T H J σ) :
    Tp_certificate_d hN b (e ω) (e A) (e Y) (e F) (e T) (e H) (e J) (e σ) := by
  obtain ⟨strategy, d, K, C, α, R, left, control, filter, rank⟩ := cert
  exact ⟨fn0_of_function_l (ZF.modelsKP hN)
    (image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he
      (fn0_function_l (ZF.modelsKP hZF) strategy)),
    e d, e K, e C, e α, e R, left.image_l hZF hN e hi he,
    image_hg_strategy_l hZF hN e hi he hist control, filter.image_l hZF hN e hi he left space,
    image_tree_rank_l hZF hN e hi he rank⟩

end YesMetaZFC.SetTheory.LargeCardinal
