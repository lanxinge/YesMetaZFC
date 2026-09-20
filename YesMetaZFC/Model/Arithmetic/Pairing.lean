import YesMetaZFC.Logic.Arithmetic.Pairing
import YesMetaZFC.Model.Arithmetic.Order

/-! # 平方分层配对的模型解释

正向值仅是图公式的宿主接口，不要求标准性；单射／满射另在 PA 中证明。
-/
namespace YesMetaZFC.Model.Arithmetic.Pairing
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}

noncomputable def value_l (m n : num_l ℳ) : num_l ℳ := by
  classical
  exact if lt_l m n then add_l (mul_l n n) m else add_l (add_l (mul_l m m) m) n

theorem graph_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (m n p : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Pairing.graph_m m n p).satisfies η ↔ value_l (m.eval η) (n.eval η) = p.eval η := by
  classical
  simp only [Logic.Arithmetic.Pairing.graph_m, Formula.satisfies, lt_sat_m,
    add_m, mul_m, Term.eval, Arguments.eval]
  change ((lt_l (m.eval η) (n.eval η) ∧ add_l (mul_l (n.eval η) (n.eval η)) (m.eval η) = p.eval η) ∨
    (¬lt_l (m.eval η) (n.eval η) ∧
      add_l (add_l (mul_l (m.eval η) (m.eval η)) (m.eval η)) (n.eval η) = p.eval η)) ↔ _
  by_cases h : lt_l (m.eval η) (n.eval η) <;> simp [value_l, h]

theorem domain_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (m n : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Pairing.domain_m m n).satisfies η ↔ ∃ p, value_l (m.eval η) (n.eval η) = p := by
  simp only [Logic.Arithmetic.Pairing.domain_m, Formula.satisfies, graph_sat_m, Term.eval_weakenBound]
  rfl

theorem range_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (p : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Pairing.range_m p).satisfies η ↔ ∃ m n, value_l m n = p.eval η := by
  simp only [Logic.Arithmetic.Pairing.range_m, Formula.satisfies, graph_sat_m, Term.eval_weakenBound]
  rfl

end YesMetaZFC.Model.Arithmetic.Pairing
