import YesMetaZFC.Logic.Arithmetic.Modular
import YesMetaZFC.Model.Arithmetic.PA.OrderedOperations

/-! # PA 模型中的正模逆与无减法贝祖等式

所有差值通过内部加法见证取得；多项式重排只消费已证加乘规律。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Modular
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}
local infixl:65 " +ₐ " => add_l
local infixl:70 " *ₐ " => mul_l
local notation "𝟙" => succ_l (zero_l ℳ)

def inverse_l (a m : num_l ℳ) : Prop := ∃ u k, a *ₐ u = 𝟙 +ₐ k *ₐ m

theorem inverse_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (a m : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Modular.inverse_m a m).satisfies η ↔ inverse_l (a.eval η) (m.eval η) := by
  simp only [Logic.Arithmetic.Modular.inverse_m, Formula.satisfies,
    add_m, mul_m, Term.eval, Arguments.eval, Term.eval_weakenBound]
  rfl

variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

private theorem add_left_comm_m (a b c : num_l ℳ) : a +ₐ (b +ₐ c) = b +ₐ (a +ₐ c) := by
  rw [← add_assoc_m hPA, add_comm_m hPA a b, add_assoc_m hPA]

private theorem mul_left_comm_m (a b c : num_l ℳ) : a *ₐ (b *ₐ c) = b *ₐ (a *ₐ c) := by
  rw [← mul_assoc_m hPA, mul_comm_m hPA a b, mul_assoc_m hPA]

theorem one_m (m : num_l ℳ) : inverse_l 𝟙 m := by
  refine ⟨𝟙, zero_l ℳ, ?_⟩
  rw [one_mul_m hPA, zero_mul_m hPA, Q.add_zero_m (q_models_m hPA)]

theorem mul_m {a b m : num_l ℳ} (ha : inverse_l a m) (hb : inverse_l b m) :
    inverse_l (a *ₐ b) m := by
  obtain ⟨u, k, hu⟩ := ha
  obtain ⟨v, l, hv⟩ := hb
  refine ⟨u *ₐ v, (k +ₐ l) +ₐ (k *ₐ l) *ₐ m, ?_⟩
  calc
    (a *ₐ b) *ₐ (u *ₐ v) = (a *ₐ u) *ₐ (b *ₐ v) := by
      simp only [mul_assoc_m hPA, mul_left_comm_m hPA]
    _ = (𝟙 +ₐ k *ₐ m) *ₐ (𝟙 +ₐ l *ₐ m) := congr (congrArg mul_l hu) hv
    _ = 𝟙 +ₐ ((k +ₐ l) +ₐ (k *ₐ l) *ₐ m) *ₐ m := by
      simp only [mul_add_m hPA, add_mul_m hPA, one_mul_m hPA, mul_one_m hPA,
        add_assoc_m hPA, add_comm_m hPA, add_left_comm_m hPA,
        mul_assoc_m hPA, mul_comm_m hPA, mul_left_comm_m hPA]

/-- 从 A*a+1=D*m 构造正逆；m>1 保证所需差值存在。 -/
theorem of_bezout_m {a A D m : num_l ℳ}
    (h : A *ₐ a +ₐ 𝟙 = D *ₐ m) (hD : lt_l (zero_l ℳ) D) (hm : lt_l 𝟙 m) :
    inverse_l a m := by
  have hQ := q_models_m hPA
  obtain ⟨s, hs⟩ := lt_le_m hPA hm
  have h₂ : le_l (𝟙 +ₐ 𝟙) m := by
    rw [Q.add_succ_m hQ, Q.add_zero_m hQ]
    exact hm
  have hle : le_l (D +ₐ 𝟙) (D *ₐ m) := by
    apply le_trans_m hPA (add_le_add_left_m hPA D hD)
    have h₁ := mul_le_mul_left_m hPA D h₂
    simpa only [mul_add_m hPA, mul_one_m hPA] using h₁
  obtain ⟨k, hk⟩ := hle
  have ha : a *ₐ A = D +ₐ k := by
    apply add_right_cancel_m hPA 𝟙
    calc
      a *ₐ A +ₐ 𝟙 = D *ₐ m := (congrArg (fun x => x +ₐ 𝟙) (mul_comm_m hPA a A)).trans h
      _ = (D +ₐ k) +ₐ 𝟙 := hk.symm.trans (by
        simp only [add_assoc_m hPA, add_comm_m hPA])
  have hD₁ : 𝟙 +ₐ k = D *ₐ s := by
    apply add_left_cancel_m hPA D
    calc
      D +ₐ (𝟙 +ₐ k) = D *ₐ m := (add_assoc_m hPA D 𝟙 k).symm.trans hk
      _ = D +ₐ D *ₐ s := by rw [← hs, mul_add_m hPA, mul_one_m hPA]
  refine ⟨A *ₐ s, k, ?_⟩
  calc
    a *ₐ (A *ₐ s) = (D +ₐ k) *ₐ s := (mul_assoc_m hPA a A s).symm.trans (congrArg (fun x => x *ₐ s) ha)
    _ = (𝟙 +ₐ k) +ₐ k *ₐ s := by rw [add_mul_m hPA, ← hD₁]
    _ = 𝟙 +ₐ k *ₐ m := by rw [← hs, mul_add_m hPA, mul_one_m hPA, add_assoc_m hPA]

/-- q=p+d 且 c=d*e 时，特殊模数之间的无减法贝祖恒等式。 -/
theorem modulus_identity_m (p d e : num_l ℳ) :
    ((p +ₐ d) *ₐ (p +ₐ d) *ₐ e) *ₐ (𝟙 +ₐ p *ₐ (d *ₐ e)) +ₐ 𝟙 =
      (p *ₐ (p +ₐ d) *ₐ e +ₐ 𝟙) *ₐ (𝟙 +ₐ (p +ₐ d) *ₐ (d *ₐ e)) := by
  simp only [mul_add_m hPA, add_mul_m hPA, one_mul_m hPA, mul_one_m hPA,
    add_assoc_m hPA, add_comm_m hPA, add_left_comm_m hPA,
    mul_assoc_m hPA, mul_comm_m hPA, mul_left_comm_m hPA]

/-- 可逆增量允许指定一个新余数；旧模数若整除 M，则其余数保持不变。 -/
theorem adjust_m {M m : num_l ℳ} (hM : inverse_l M m) (hm : lt_l (zero_l ℳ) m)
    (b a : num_l ℳ) : ∃ t q, q *ₐ m +ₐ a = b +ₐ M *ₐ t := by
  obtain ⟨u, k, hu⟩ := hM
  obtain ⟨s, hs⟩ := hm
  rcases le_total_m hPA b a with hba | hab
  · obtain ⟨w, hw⟩ := hba
    refine ⟨u *ₐ w, k *ₐ w, ?_⟩
    calc
      (k *ₐ w) *ₐ m +ₐ a = b +ₐ (𝟙 +ₐ k *ₐ m) *ₐ w := by
        rw [← hw]
        simp only [add_mul_m hPA, one_mul_m hPA,
          add_assoc_m hPA, add_comm_m hPA,
          mul_assoc_m hPA, mul_comm_m hPA, mul_left_comm_m hPA]
      _ = b +ₐ M *ₐ (u *ₐ w) := by rw [← hu, mul_assoc_m hPA]
  · obtain ⟨w, hw⟩ := hab
    refine ⟨(u *ₐ w) *ₐ s, w +ₐ (k *ₐ w) *ₐ s, ?_⟩
    calc
      (w +ₐ (k *ₐ w) *ₐ s) *ₐ m +ₐ a = (a +ₐ w) +ₐ (𝟙 +ₐ k *ₐ m) *ₐ (w *ₐ s) := by
        rw [← hs]
        simp only [mul_add_m hPA, add_mul_m hPA, one_mul_m hPA, mul_one_m hPA,
          add_assoc_m hPA, add_comm_m hPA, add_left_comm_m hPA,
          mul_assoc_m hPA, mul_comm_m hPA]
      _ = b +ₐ M *ₐ ((u *ₐ w) *ₐ s) := by rw [hw, ← hu]; simp only [mul_assoc_m hPA]

end YesMetaZFC.Model.Arithmetic.PA.Modular
