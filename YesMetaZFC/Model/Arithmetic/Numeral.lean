import YesMetaZFC.Model.Arithmetic.PA.LinearOrder
import YesMetaZFC.Model.Arithmetic.Pairing
import YesMetaZFC.Logic.Arithmetic.NatPairing

/-! # 任意 PA 模型中的标准数码嵌入

只给定外部自然数产生有限后继链；不声称这些数码穷尽模型数域。
-/
namespace YesMetaZFC.Model.Arithmetic.Numeral
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}

def value_l : Nat → num_l ℳ
  | 0 => zero_l ℳ
  | n + 1 => succ_l (value_l n)

theorem eval_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (n : Nat) :
    (numeral_m n).eval η = value_l n := by
  induction n with
  | zero => rfl
  | succ n h => exact congrArg succ_l h

variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

theorem injective_m {m n : Nat} (h : value_l (ℳ := ℳ) m = value_l n) : m = n := by
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ n => exact False.elim (Q.nonzero_m (PA.q_models_m hPA) _ h.symm)
  | succ m ih =>
      cases n with
      | zero => exact False.elim (Q.nonzero_m (PA.q_models_m hPA) _ h)
      | succ n => exact congrArg Nat.succ (ih (Q.injective_m (PA.q_models_m hPA) h))

theorem add_m (m n : Nat) : add_l (value_l (ℳ := ℳ) m) (value_l n) = value_l (m + n) := by
  induction n with
  | zero => exact Q.add_zero_m (PA.q_models_m hPA) _
  | succ n ih => exact (Q.add_succ_m (PA.q_models_m hPA) _ _).trans (congrArg succ_l ih)

theorem mul_m (m n : Nat) : mul_l (value_l (ℳ := ℳ) m) (value_l n) = value_l (m * n) := by
  induction n with
  | zero => exact Q.mul_zero_m (PA.q_models_m hPA) _
  | succ n ih =>
    exact (Q.mul_succ_m (PA.q_models_m hPA) _ _).trans
      ((congrArg (fun x => add_l x (value_l m)) ih).trans (add_m hPA _ _))

theorem le_of_le_m {m n : Nat} (h : m ≤ n) : le_l (value_l (ℳ := ℳ) m) (value_l n) := by
  refine ⟨value_l (n - m), ?_⟩
  rw [add_m hPA, Nat.add_sub_of_le h]

theorem lt_m (m n : Nat) : lt_l (value_l (ℳ := ℳ) m) (value_l n) ↔ m < n := by
  constructor
  · intro h
    by_cases hmn : m < n
    · exact hmn
    · exact False.elim (PA.not_lt_of_le_m hPA (le_of_le_m hPA (Nat.le_of_not_gt hmn)) h)
  · intro h
    exact le_of_le_m hPA h

theorem pair_m (m n : Nat) : Pairing.value_l (value_l (ℳ := ℳ) m) (value_l n) = value_l (NatPairing.pair_l m n) := by
  classical
  simp only [Pairing.value_l, lt_m hPA, NatPairing.pair_l]
  split <;> simp only [mul_m hPA, add_m hPA]

end YesMetaZFC.Model.Arithmetic.Numeral
