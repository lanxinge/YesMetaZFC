import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakSyntax

/-! # 原弱迭代应答的精确公式

公式只陈述所选枝、实际极限及历史保持；不把应答存在性加入合法性定义。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def wi_tree_m {d} (t T Q G E L : Term d) : Formula 1 d := set[d] ⟪
  ∃ p, ⌜kpair0_m⌝ₚ(p, ⌜E⌝ₛ, ⌜L⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(⌜t⌝ₛ, ⌜T⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, p)⟫
derive_free_closed wi_tree_m
theorem wi_tree_sat_l (hE : Extensional M) {d} (η : Env M d) (t T Q G E L : Term d) :
    Formula.satisfies η (wi_tree_m t T Q G E L) ↔
      Wi_tree_d (t.eval η) (T.eval η) (Q.eval η) (G.eval η) (E.eval η) (L.eval η) := by
  simp only [wi_tree_m, Wi_tree_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, rd_quad_sat_l hE, Definitional.Term.eval_weaken]; rfl

def wi_success_m {d} (ω α t B Q G : Term d) : Formula 1 d := set[d] ⟪
  ∃ ξ T₀ Q₀ G₀ E₀ L₀ c N W F j, ⌜KP.succ0_m⌝ₚ(⌜α⌝ₛ, ξ) ∧ ⌜wi_tree_m⌝ₚ(⌜t⌝ₛ, T₀, Q₀, G₀, E₀, L₀) ∧
    ⌜rd_entry0_m⌝ₚ(⌜α⌝ₛ, c, ⌜Q⌝ₛ) ∧ ⌜it_branch_m⌝ₚ(⌜ω⌝ₛ, T₀, ⌜B⌝ₛ) ∧
    ⌜wi_limit_m⌝ₚ(⌜ω⌝ₛ, ⌜B⌝ₛ, Q₀, G₀, c, N, W, F) ∧ ⌜it_map_m⌝ₚ(⌜G⌝ₛ, ξ, ⌜α⌝ₛ, j) ∧
    (∀ o, ⌜Formula.isEmpty⌝ₚ(o) → ⌜rd_entry0_m⌝ₚ(o, j, F))⟫
derive_free_closed wi_success_m
theorem wi_success_sat_l {d} (η : Env M d) (ω α t B Q G : Term d) :
    Formula.satisfies η (wi_success_m ω α t B Q G) ↔
      Wi_success_d hZF (ω.eval η) (α.eval η) (t.eval η) (B.eval η) (Q.eval η) (G.eval η) := by
  simp only [wi_success_m, Wi_success_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_isEmpty_iff,
    KP.succ0_sat_l hZF.1, wi_tree_sat_l hZF.1, rd_entry0_sat_l hZF.1, it_branch_sat_l hZF.1,
    wi_limit_sat_l hZF, it_map_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl

def wi_continuous_m {d} (ω a A S α H Q' G' : Term d) : Formula 1 d := set[d] ⟪
  ∃ T Q G P c N W F, ⌜wi_state_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, T, Q, G, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, P) ∧
    ⌜wi_past_m⌝ₚ(⌜H⌝ₛ, Q, G, P) ∧ ⌜rd_entry0_m⌝ₚ(⌜α⌝ₛ, c, ⌜Q'⌝ₛ) ∧
    ⌜wi_limit_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, Q, G, c, N, W, F) ∧
    (∀ i j, i ∈ ⌜α⌝ₛ → (⌜it_map_m⌝ₚ(⌜G'⌝ₛ, i, ⌜α⌝ₛ, j) ↔ ⌜rd_entry0_m⌝ₚ(i, j, F)))⟫
derive_free_closed wi_continuous_m
theorem wi_continuous_sat_l {d} (η : Env M d) (ω a A S α H Q' G' : Term d) :
    Formula.satisfies η (wi_continuous_m ω a A S α H Q' G') ↔
      Wi_continuous_d hZF (ω.eval η) (a.eval η) (A.eval η) (S.eval η) (α.eval η) (H.eval η) (Q'.eval η) (G'.eval η) := by
  simp only [wi_continuous_m, Wi_continuous_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_iff_iff,
    wi_state_sat_l hZF, wi_past_sat_l hZF.1, rd_entry0_sat_l hZF.1, wi_limit_sat_l hZF,
    it_map_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl

def wi_answer_m {d} (ω a A S o s₀ α H t B s : Term d) : Formula 1 d := set[d] ⟪
  ∃ β T Q G P, ⌜KP.succ0_m⌝ₚ(β, ⌜α⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(⌜s⌝ₛ, T, Q, G, P) ∧
    ⌜wi_state_m⌝ₚ(⌜ω⌝ₛ, β, T, Q, G, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, P) ∧ ⌜wi_past_m⌝ₚ(⌜H⌝ₛ, Q, G, P) ∧
    ((⌜α⌝ₛ = ⌜o⌝ₛ ∧ ⌜B⌝ₛ = ⌜o⌝ₛ ∧ ⌜s⌝ₛ = ⌜s₀⌝ₛ) ∨ ⌜wi_success_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, ⌜t⌝ₛ, ⌜B⌝ₛ, Q, G) ∨
      (⌜Formula.isLimitOrdinal⌝ₚ(⌜α⌝ₛ) ∧ ⌜B⌝ₛ = ⌜o⌝ₛ ∧ ⌜wi_continuous_m⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, ⌜α⌝ₛ, ⌜H⌝ₛ, Q, G)))⟫
derive_free_closed wi_answer_m
theorem wi_answer_sat_l {d} (η : Env M d) (ω a A S o s₀ α H t B s : Term d) :
    Formula.satisfies η (wi_answer_m ω a A S o s₀ α H t B s) ↔ Wi_answer_d hZF
      (ω.eval η) (a.eval η) (A.eval η) (S.eval η) (o.eval η) (s₀.eval η) (α.eval η) (H.eval η) (t.eval η) (B.eval η) (s.eval η) := by
  simp only [wi_answer_m, Wi_answer_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_isLimitOrdinal_iff,
    KP.succ0_sat_l hZF.1, rd_quad_sat_l hZF.1, wi_state_sat_l hZF, wi_past_sat_l hZF.1,
    wi_success_sat_l hZF, wi_continuous_sat_l hZF, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
