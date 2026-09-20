import YesMetaZFC.Logic.Arithmetic.PA.Multiplication
import YesMetaZFC.Model.Arithmetic.Structure
import YesMetaZFC.Model.FirstOrder.Soundness

/-! # 任意 PA 模型中的运算规律

本模块只消费对象推导和通用可靠性，不重复进行语义归纳。
量词遍历整个模型数域，包括非标准元素；不要求模型载体同构于 Nat。
-/
namespace YesMetaZFC.Model.Arithmetic.PA
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u

variable {ℳ : Structure.{0, 0, 0, u} signature_m}
variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

private def v₀ {Δ : SortContext signature_m} : Term signature_m [] (.num :: Δ) .num :=
  .fvar .here

private def v₁ {Δ : SortContext signature_m} : Term signature_m [] (.num :: .num :: Δ) .num :=
  .fvar (.there .here)

private def v₂ {Δ : SortContext signature_m} :
    Term signature_m [] (.num :: .num :: .num :: Δ) .num := .fvar (.there (.there .here))

theorem zero_add_m (n : num_l ℳ) : add_l (zero_l ℳ) n = n :=
  (Logic.Arithmetic.PA.zero_add_m (fun h => h) (Γ := []) (Δ := [.num]) v₀).sound hPA
    (Env.empty.pushFree n) (by intro φ h; cases h)

theorem succ_add_m (m n : num_l ℳ) : add_l (succ_l m) n = succ_l (add_l m n) :=
  (Logic.Arithmetic.PA.succ_add_m (fun h => h) (Γ := []) (Δ := [.num, .num]) v₁ v₀).sound hPA
    ((Env.empty.pushFree m).pushFree n) (by intro φ h; cases h)

theorem add_comm_m (m n : num_l ℳ) : add_l m n = add_l n m :=
  (Logic.Arithmetic.PA.add_comm_m (fun h => h) (Γ := []) (Δ := [.num, .num]) v₁ v₀).sound hPA
    ((Env.empty.pushFree m).pushFree n) (by intro φ h; cases h)

theorem add_assoc_m (m n p : num_l ℳ) : add_l (add_l m n) p = add_l m (add_l n p) :=
  (Logic.Arithmetic.PA.add_assoc_m (fun h => h)
    (Γ := []) (Δ := [.num, .num, .num]) v₂ v₁ v₀).sound hPA
    (((Env.empty.pushFree m).pushFree n).pushFree p) (by intro φ h; cases h)

theorem zero_mul_m (n : num_l ℳ) : mul_l (zero_l ℳ) n = zero_l ℳ :=
  (Logic.Arithmetic.PA.zero_mul_m (fun h => h) (Γ := []) (Δ := [.num]) v₀).sound hPA
    (Env.empty.pushFree n) (by intro φ h; cases h)

theorem mul_one_m (n : num_l ℳ) : mul_l n (succ_l (zero_l ℳ)) = n :=
  (Logic.Arithmetic.PA.mul_one_m (fun h => h) (Γ := []) (Δ := [.num]) v₀).sound hPA
    (Env.empty.pushFree n) (by intro φ h; cases h)

theorem one_mul_m (n : num_l ℳ) : mul_l (succ_l (zero_l ℳ)) n = n :=
  (Logic.Arithmetic.PA.one_mul_m (fun h => h) (Γ := []) (Δ := [.num]) v₀).sound hPA
    (Env.empty.pushFree n) (by intro φ h; cases h)

theorem succ_mul_m (m n : num_l ℳ) : mul_l (succ_l m) n = add_l (mul_l m n) n :=
  (Logic.Arithmetic.PA.succ_mul_m (fun h => h) (Γ := []) (Δ := [.num, .num]) v₁ v₀).sound hPA
    ((Env.empty.pushFree m).pushFree n) (by intro φ h; cases h)

theorem mul_comm_m (m n : num_l ℳ) : mul_l m n = mul_l n m :=
  (Logic.Arithmetic.PA.mul_comm_m (fun h => h) (Γ := []) (Δ := [.num, .num]) v₁ v₀).sound hPA
    ((Env.empty.pushFree m).pushFree n) (by intro φ h; cases h)

theorem mul_add_m (m n p : num_l ℳ) : mul_l m (add_l n p) = add_l (mul_l m n) (mul_l m p) :=
  (Logic.Arithmetic.PA.mul_add_m (fun h => h)
    (Γ := []) (Δ := [.num, .num, .num]) v₂ v₁ v₀).sound hPA
    (((Env.empty.pushFree m).pushFree n).pushFree p) (by intro φ h; cases h)

theorem add_mul_m (m n p : num_l ℳ) : mul_l (add_l m n) p = add_l (mul_l m p) (mul_l n p) :=
  (Logic.Arithmetic.PA.add_mul_m (fun h => h)
    (Γ := []) (Δ := [.num, .num, .num]) v₂ v₁ v₀).sound hPA
    (((Env.empty.pushFree m).pushFree n).pushFree p) (by intro φ h; cases h)

theorem mul_assoc_m (m n p : num_l ℳ) : mul_l (mul_l m n) p = mul_l m (mul_l n p) :=
  (Logic.Arithmetic.PA.mul_assoc_m (fun h => h)
    (Γ := []) (Δ := [.num, .num, .num]) v₂ v₁ v₀).sound hPA
    (((Env.empty.pushFree m).pushFree n).pushFree p) (by intro φ h; cases h)

end YesMetaZFC.Model.Arithmetic.PA
