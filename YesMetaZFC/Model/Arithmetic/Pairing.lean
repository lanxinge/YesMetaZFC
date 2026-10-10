import YesMetaZFC.Logic.Arithmetic.Pairing
import YesMetaZFC.Model.Arithmetic.Order

/-! # 平方分层配对的模型解释

直接解释图关系，不从命题判定选择模型数；单射／满射另在 PA 中证明。
-/
namespace YesMetaZFC.Model.Arithmetic.Pairing
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}

def graph_l (m n p : num_l ℳ) : Prop :=
  (lt_l m n ∧ add_l (mul_l n n) m = p) ∨
    (¬lt_l m n ∧ add_l (add_l (mul_l m m) m) n = p)

theorem of_lt_m {m n p : num_l ℳ} (h : lt_l m n) :
    graph_l m n p ↔ add_l (mul_l n n) m = p := by simp [graph_l, h]

theorem of_not_lt_m {m n p : num_l ℳ} (h : ¬lt_l m n) :
    graph_l m n p ↔ add_l (add_l (mul_l m m) m) n = p := by simp [graph_l, h]

theorem total_m (m n : num_l ℳ) : ∃ p, graph_l m n p := by
  classical
  by_cases h : lt_l m n
  · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨_, Or.inr ⟨h, rfl⟩⟩

theorem unique_m {m n p q : num_l ℳ} (hp : graph_l m n p) (hq : graph_l m n q) : p = q := by
  rcases hp with ⟨h, hp⟩ | ⟨h, hp⟩
  · exact hp.symm.trans ((of_lt_m h).mp hq)
  · exact hp.symm.trans ((of_not_lt_m h).mp hq)

theorem graph_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (m n p : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Pairing.graph_m m n p).satisfies η ↔ graph_l (m.eval η) (n.eval η) (p.eval η) := by
  simp only [Logic.Arithmetic.Pairing.graph_m, Formula.satisfies, lt_sat_m,
    add_m, mul_m, Term.eval, Arguments.eval]
  rfl

theorem domain_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (m n : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Pairing.domain_m m n).satisfies η ↔ ∃ p, graph_l (m.eval η) (n.eval η) p := by
  simp only [Logic.Arithmetic.Pairing.domain_m, Formula.satisfies, graph_sat_m, Term.eval_weakenBound]
  rfl

theorem range_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (p : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Pairing.range_m p).satisfies η ↔ ∃ m n, graph_l m n (p.eval η) := by
  simp only [Logic.Arithmetic.Pairing.range_m, Formula.satisfies, graph_sat_m, Term.eval_weakenBound]
  rfl

end YesMetaZFC.Model.Arithmetic.Pairing
