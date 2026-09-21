import Init.Data.Nat.Sqrt.Lemmas
import Lean.Elab.Tactic.Omega

/-! # 平方分层配对的可计算宿主接口

与算术图使用同一约定；不使用一阶完备性调度中的二进制配对。
-/
namespace YesMetaZFC.Logic.Arithmetic.NatPairing
set_option autoImplicit false

def pair_l (m n : Nat) : Nat := if m < n then n * n + m else m * m + m + n

def unpair_l (n : Nat) : Nat × Nat :=
  let s := n.sqrt
  if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)

theorem pair_unpair_l (n : Nat) : pair_l (unpair_l n).1 (unpair_l n).2 = n := by
  have h₀ := Nat.sqrt_le n
  have h₁ := Nat.lt_succ_sqrt n
  have h₂ : (n.sqrt + 1) * (n.sqrt + 1) = n.sqrt * n.sqrt + n.sqrt + n.sqrt + 1 := by
    simp [Nat.add_mul, Nat.mul_add, Nat.add_assoc]
  change n < (n.sqrt + 1) * (n.sqrt + 1) at h₁
  rw [h₂] at h₁
  by_cases h : n - n.sqrt * n.sqrt < n.sqrt
  · simp only [unpair_l, if_pos h, pair_l]
    omega
  · simp only [unpair_l, if_neg h, pair_l]
    have h₃ : ¬n.sqrt < n - n.sqrt * n.sqrt - n.sqrt := by omega
    rw [if_neg h₃]
    omega

end YesMetaZFC.Logic.Arithmetic.NatPairing
