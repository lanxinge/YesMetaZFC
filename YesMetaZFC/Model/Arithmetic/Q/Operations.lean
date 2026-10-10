import YesMetaZFC.Logic.Arithmetic.Q.Derivation
import YesMetaZFC.Model.Arithmetic.Structure
import YesMetaZFC.Model.FirstOrder.Soundness

/-! # 任意 Q 模型的基本运算

仅解释七条 Q 公理；这些接口不需要 PA 归纳。
-/
namespace YesMetaZFC.Model.Arithmetic.Q
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u

variable {ℳ : Structure.{0, 0, 0, u} signature_m}
variable (hQ : Theory.Models ℳ Logic.Arithmetic.Q.theory_m)
include hQ

private def v₀ {Δ : SortContext signature_m} : Term signature_m [] (.num :: Δ) .num :=
  .fvar .here

private def v₁ {Δ : SortContext signature_m} : Term signature_m [] (.num :: .num :: Δ) .num :=
  .fvar (.there .here)

theorem nonzero_m (n : num_l ℳ) : succ_l n ≠ zero_l ℳ :=
  (Logic.Arithmetic.Q.nonzero_m (fun h => h) (Γ := []) (Δ := [.num]) v₀).sound hQ
    (Env.empty.pushFree n) (by intro φ h; cases h)

theorem injective_m {m n : num_l ℳ} (h : succ_l m = succ_l n) : m = n :=
  (Logic.Arithmetic.Q.injective_m (fun h => h) (Γ := []) (Δ := [.num, .num]) v₁ v₀).sound hQ
    ((Env.empty.pushFree m).pushFree n) (by intro φ h; cases h) h

theorem predecessor_m (n : num_l ℳ) : n = zero_l ℳ ∨ ∃ m, n = succ_l m :=
  (Logic.Arithmetic.Q.predecessor_m (fun h => h) (Γ := []) (Δ := [.num]) v₀).sound hQ
    (Env.empty.pushFree n) (by intro φ h; cases h)

theorem add_zero_m (n : num_l ℳ) : add_l n (zero_l ℳ) = n :=
  (Logic.Arithmetic.Q.add_zero_m (fun h => h) (Γ := []) (Δ := [.num]) v₀).sound hQ
    (Env.empty.pushFree n) (by intro φ h; cases h)

theorem add_succ_m (m n : num_l ℳ) : add_l m (succ_l n) = succ_l (add_l m n) :=
  (Logic.Arithmetic.Q.add_succ_m (fun h => h) (Γ := []) (Δ := [.num, .num]) v₁ v₀).sound hQ
    ((Env.empty.pushFree m).pushFree n) (by intro φ h; cases h)

theorem mul_zero_m (n : num_l ℳ) : mul_l n (zero_l ℳ) = zero_l ℳ :=
  (Logic.Arithmetic.Q.mul_zero_m (fun h => h) (Γ := []) (Δ := [.num]) v₀).sound hQ
    (Env.empty.pushFree n) (by intro φ h; cases h)

theorem mul_succ_m (m n : num_l ℳ) : mul_l m (succ_l n) = add_l (mul_l m n) m :=
  (Logic.Arithmetic.Q.mul_succ_m (fun h => h) (Γ := []) (Δ := [.num, .num]) v₁ v₀).sound hQ
    ((Env.empty.pushFree m).pushFree n) (by intro φ h; cases h)

end YesMetaZFC.Model.Arithmetic.Q
