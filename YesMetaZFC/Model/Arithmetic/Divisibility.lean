import YesMetaZFC.Logic.Arithmetic.Divisibility
import YesMetaZFC.Model.Arithmetic.Order

/-! # 整除模板在任意结构中的精确语义 -/
namespace YesMetaZFC.Model.Arithmetic.Divisibility
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u

variable {ℳ : Structure.{0, 0, 0, u} signature_m}

def dvd_l (d n : num_l ℳ) : Prop := ∃ k, mul_l d k = n

def common_l (n c : num_l ℳ) : Prop :=
  lt_l (zero_l ℳ) c ∧ ∀ d, lt_l (zero_l ℳ) d → le_l d n → dvd_l d c

theorem dvd_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (d n : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Divisibility.dvd_m d n).satisfies η ↔ dvd_l (d.eval η) (n.eval η) := by
  simp only [Logic.Arithmetic.Divisibility.dvd_m, Formula.satisfies,
    mul_m, Term.eval, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem common_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (n c : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Divisibility.common_m n c).satisfies η ↔ common_l (n.eval η) (c.eval η) := by
  simp only [Logic.Arithmetic.Divisibility.common_m, Formula.satisfies,
    lt_sat_m, le_sat_m, dvd_sat_m, Term.eval_weakenBound]
  rfl

theorem bounded_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (n b : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Divisibility.bounded_m n b).satisfies η ↔
      ∃ c, lt_l (b.eval η) c ∧ common_l (n.eval η) c := by
  simp only [Logic.Arithmetic.Divisibility.bounded_m, Formula.satisfies,
    lt_sat_m, common_sat_m, Term.eval_weakenBound]
  rfl

end YesMetaZFC.Model.Arithmetic.Divisibility
