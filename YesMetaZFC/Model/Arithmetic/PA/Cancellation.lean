import YesMetaZFC.Logic.Arithmetic.PA.Cancellation
import YesMetaZFC.Model.Arithmetic.PA.Operations

/-! # 任意 PA 模型中的加法消去

把对象等式假设交给可靠性的局部上下文；不假定模型标准。
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

theorem add_right_cancel_m {m n : num_l ℳ} (p : num_l ℳ)
    (h : add_l m p = add_l n p) : m = n :=
  (Logic.Arithmetic.PA.add_right_cancel_m (fun h => h) (Δ := [.num, .num, .num])
    (Γ := [.equal (add_m v₂ v₀) (add_m v₁ v₀)]) (s := v₂) (t := v₁) v₀
    (Derives.assumption List.mem_cons_self)).sound hPA
    (((Env.empty.pushFree m).pushFree n).pushFree p)
    (by intro φ hφ; rcases List.mem_singleton.mp hφ with rfl; exact h)

theorem add_left_cancel_m (m : num_l ℳ) {n p : num_l ℳ}
    (h : add_l m n = add_l m p) : n = p :=
  add_right_cancel_m hPA m ((add_comm_m hPA n m).trans (h.trans (add_comm_m hPA m p)))

theorem add_eq_zero_left_m {m n : num_l ℳ} (h : add_l m n = zero_l ℳ) : m = zero_l ℳ :=
  (Logic.Arithmetic.PA.add_eq_zero_left_m (fun h => h) (Δ := [.num, .num])
    (Γ := [.equal (add_m v₁ v₀) zero_m]) (s := v₁) (t := v₀)
    (Derives.assumption List.mem_cons_self)).sound hPA ((Env.empty.pushFree m).pushFree n)
    (by intro φ hφ; rcases List.mem_singleton.mp hφ with rfl; exact h)

theorem add_eq_zero_right_m {m n : num_l ℳ} (h : add_l m n = zero_l ℳ) : n = zero_l ℳ :=
  add_eq_zero_left_m hPA ((add_comm_m hPA n m).trans h)

end YesMetaZFC.Model.Arithmetic.PA
