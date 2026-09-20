import YesMetaZFC.Logic.Arithmetic.Q.Derivation
import YesMetaZFC.Logic.Arithmetic.Equality

/-! # Q 中的数码运算与数码区分

由 BMS 二阶算术中的数码证明提取，现降低为任意 Q 扩张。
归纳只在外部给定的数码长度上进行，不向对象 Q 加入归纳模式。
-/
namespace YesMetaZFC.Logic.Arithmetic.Q
open FirstOrder
set_option autoImplicit false

variable {T : Theory signature_m} (hQ : Theory.Extends T theory_m)
variable {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
include hQ

theorem numeral_add_m (m n : Nat) : Derives T Γ
    (.equal (add_m (numeral_m m) (numeral_m n)) (numeral_m (m + n))) := by
  induction n with
  | zero => exact add_zero_m hQ _
  | succ n h => exact Derives.eq_trans (add_succ_m hQ _ _) (succ_congr_m h)

theorem numeral_mul_m (m n : Nat) : Derives T Γ
    (.equal (mul_m (numeral_m m) (numeral_m n)) (numeral_m (m * n))) := by
  induction n with
  | zero => exact mul_zero_m hQ _
  | succ n h =>
    exact Derives.eq_trans (mul_succ_m hQ _ _)
      (Derives.eq_trans (add_left_congr_m _ h) (numeral_add_m hQ _ _))

theorem numeral_ne_m (m n : Nat) (h : m ≠ n) : Derives T Γ
    (.neg (.equal (numeral_m m) (numeral_m n))) := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => exact False.elim (h rfl)
    | succ n =>
      apply Derives.neg_intro
      exact Derives.neg_elim (Derives.eq_symm
        (Derives.assumption List.mem_cons_self)) (nonzero_m hQ _)
  | succ m hᵢ =>
    cases n with
    | zero => exact nonzero_m hQ _
    | succ n =>
      apply Derives.neg_intro
      exact Derives.neg_elim
        (Derives.imp_elim (injective_m hQ _ _) (Derives.assumption List.mem_cons_self))
        (Derives.context_weaken_cons (hᵢ n (fun h₀ => h (congrArg Nat.succ h₀))))

end YesMetaZFC.Logic.Arithmetic.Q
