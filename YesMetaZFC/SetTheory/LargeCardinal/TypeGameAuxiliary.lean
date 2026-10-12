import YesMetaZFC.SetTheory.LargeCardinal.TypeGameHistoryRules

/-! # 第二方辅助走法：原规则 (2)–(6)

节点常量取自已经落下的实数前缀。dcp 弹性和节点条件均检查固定查询的
字面成员性；末位最大序数没有作为新规则加入，而留给原刚性引理推导。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_aux_d (p : Tg_params_d M.Domain) (n h v : M.Domain) : Prop :=
  ∃ ℓ t κ u k l N x s B U D r m b q f C V W g₀ g₁ g₂ g₃,
    Tg_aux_data_d v ℓ t κ u ∧ M.mem κ p.δ ∧ Fn0_d k p.ω t ∧ M.SuccessorOf l k ∧ M.SuccessorOf N l ∧
    Tg_digits_d hZF p.c p.b n p.A h x ∧ M.IsRestrictionOf I s x k ∧ Tg_query_request_d hZF p.ω κ k s t ∧
    Tg_query_data_d p.Q κ k s t B U D r m b q f ∧ M.MemberSubset u D ∧
    Tg_ee_data_d p.E κ l C V W ⟨g₀, g₁, g₂, g₃⟩ ∧ Tg_elastic_d I l N W ⟨g₀, g₁, g₂, g₃⟩ u ∧ M.mem f u ∧
    Tg_growth_d hZF p.e p.c p.A n h κ B ∧
    ((t = p.e ∧ Tg_reset_d hZF p.ω p.e p.δ p.S p.ν l N U D u) ∨
      (t ≠ p.e ∧ Tg_continue_d hZF p.ω p.e p.a p.c p.δ n h ℓ t κ k N U D u))

def tg_aux0_m : Formula 1 15 :=
  let p : Tg_params_d (Term 15) := ⟨.bound 0, .bound 1, .bound 2, .bound 3, .bound 4, .bound 5,
    .bound 6, .bound 7, .bound 8, .bound 9, .bound 10, .bound 11⟩
  let n : Term 15 := .bound 12; let h : Term 15 := .bound 13; let v : Term 15 := .bound 14
  set[15] ⟪
  ∃ ℓ t κ u k l N x s B U D r m b q f C V W g₀ g₁ g₂ g₃,
  ⌜tg_aux_data_m⌝ₚ(⌜v⌝ₛ, ℓ, t, κ, u) ∧ κ ∈ ⌜p.δ⌝ₛ ∧ ⌜fn0_m⌝ₚ(k, ⌜p.ω⌝ₛ, t) ∧
  ⌜Formula.isSuccessor⌝ₚ(l, k) ∧ ⌜Formula.isSuccessor⌝ₚ(N, l) ∧
  ⌜tg_digits_m⌝ₚ(⌜p.c⌝ₛ, ⌜p.b⌝ₛ, ⌜n⌝ₛ, ⌜p.A⌝ₛ, ⌜h⌝ₛ, x) ∧
  ⌜Formula.isRestriction kpair_convention_l⌝ₚ(s, x, k) ∧ ⌜tg_query_request_m⌝ₚ(⌜p.ω⌝ₛ, κ, k, s, t) ∧
  ⌜tg_query_data_m⌝ₚ(⌜p.Q⌝ₛ, κ, k, s, t, B, U, D, r, m, b, q, f) ∧ u ⊆ D ∧
  ⌜tg_ee_data_m⌝ₚ(⌜p.E⌝ₛ, κ, l, C, V, W, g₀, g₁, g₂, g₃) ∧ ⌜tg_elastic_m⌝ₚ(l, N, W, g₀, g₁, g₂, g₃, u) ∧ f ∈ u ∧
  ⌜tg_growth_m⌝ₚ(⌜p.e⌝ₛ, ⌜p.c⌝ₛ, ⌜p.A⌝ₛ, ⌜n⌝ₛ, ⌜h⌝ₛ, κ, B) ∧
  ((t = ⌜p.e⌝ₛ ∧ ⌜tg_reset_m⌝ₚ(⌜p.ω⌝ₛ, ⌜p.e⌝ₛ, ⌜p.δ⌝ₛ, ⌜p.S⌝ₛ, ⌜p.ν⌝ₛ, l, N, U, D, u)) ∨
    (¬ (t = ⌜p.e⌝ₛ) ∧ ⌜tg_continue_m⌝ₚ(⌜p.ω⌝ₛ, ⌜p.e⌝ₛ, ⌜p.a⌝ₛ, ⌜p.c⌝ₛ, ⌜p.δ⌝ₛ,
      ⌜n⌝ₛ, ⌜h⌝ₛ, ℓ, t, κ, k, N, U, D, u)))⟫

theorem tg_aux0_closed_l : tg_aux0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_aux0_m, Definitional.Formula.FreeClosed]

def tg_aux_m {d} (p : Tg_params_d (Term d)) (n h v : Term d) : Formula 1 d :=
  tg_aux0_m.bind (fun i => [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, n, h, v].get i)

@[simp] theorem tg_aux_closed_l {d} (p : Tg_params_d (Term d)) (n h v : Term d)
    (hp : p.closed_l) (hn : n.freeSupport = []) (hh : h.freeSupport = []) (hv : v.freeSupport = []) :
    (tg_aux_m p n h v).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_aux0_closed_l
  rcases hp with ⟨hω, he, ha, hb, hc, hδ, hA, hS, hν, hE, hP, hQ⟩
  simp only [Fin.forall_fin_succ]
  exact ⟨hω, he, ha, hb, hc, hδ, hA, hS, hν, hE, hP, hQ, hn, hh, hv, fun i => Fin.elim0 i⟩

theorem tg_aux_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (n h v : Term d) :
    Formula.satisfies ρ (tg_aux_m p n h v) ↔ Tg_aux_d hZF (p.map_l (fun t => t.eval ρ)) (n.eval ρ) (h.eval ρ) (v.eval ρ) := by
  simp only [tg_aux_m, Formula.satisfies_bind, tg_aux0_m, Tg_aux_d, Tg_params_d.map_l, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tg_aux_data_sat_l hZF.1, Formula.satisfies_mem_iff, fn0_sat_l hZF.1, Formula.satisfies_isSuccessor_iff,
    tg_digits_sat_l hZF, Formula.satisfies_isRestriction_iff I, tg_query_request_sat_l hZF,
    tg_query_data_sat_l hZF.1, Formula.satisfies_subset_iff, tg_ee_data_sat_l hZF.1, tg_elastic_sat_l I hZF.1,
    tg_growth_sat_l hZF, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    tg_reset_sat_l hZF, Formula.satisfies_neg_iff, tg_continue_sat_l hZF, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal
