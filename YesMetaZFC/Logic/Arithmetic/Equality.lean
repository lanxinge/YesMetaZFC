import YesMetaZFC.Logic.Arithmetic.Syntax
import YesMetaZFC.Logic.FirstOrder.Metatheory.Equality.Basic

/-! # 算术项的纯逻辑同余

这里不要求目标理论包含 Q；同余只消费已有的等式推导。
-/
namespace YesMetaZFC.Logic.Arithmetic
open FirstOrder
set_option autoImplicit false

variable {T : Theory signature_m} {Δ : SortContext signature_m}
variable {Γ : Context signature_m Δ}

theorem succ_congr_m {s t : Term signature_m [] Δ .num}
    (h : Derives T Γ (.equal s t)) : Derives T Γ (.equal (succ_m s) (succ_m t)) :=
  Metatheory.Derives.term_context_congr_of_equality (succ_m (.bvar .here)) h

theorem add_left_congr_m {s t : Term signature_m [] Δ .num}
    (u : Term signature_m [] Δ .num) (h : Derives T Γ (.equal s t)) :
    Derives T Γ (.equal (add_m s u) (add_m t u)) := by
  have h₁ := Metatheory.Derives.term_context_congr_of_equality
    (add_m (.bvar .here) (u.weakenBound sort_m.num)) h
  simp only [add_m, Term.instantiateTop_app, Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil, Term.instantiateTop_weakenBound] at h₁
  exact h₁

theorem add_right_congr_m (u : Term signature_m [] Δ .num)
    {s t : Term signature_m [] Δ .num} (h : Derives T Γ (.equal s t)) :
    Derives T Γ (.equal (add_m u s) (add_m u t)) := by
  have h₁ := Metatheory.Derives.term_context_congr_of_equality
    (add_m (u.weakenBound sort_m.num) (.bvar .here)) h
  simp only [add_m, Term.instantiateTop_app, Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil, Term.instantiateTop_weakenBound] at h₁
  exact h₁

theorem mul_left_congr_m {s t : Term signature_m [] Δ .num}
    (u : Term signature_m [] Δ .num) (h : Derives T Γ (.equal s t)) :
    Derives T Γ (.equal (mul_m s u) (mul_m t u)) := by
  have h₁ := Metatheory.Derives.term_context_congr_of_equality
    (mul_m (.bvar .here) (u.weakenBound sort_m.num)) h
  simp only [mul_m, Term.instantiateTop_app, Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil, Term.instantiateTop_weakenBound] at h₁
  exact h₁

theorem mul_right_congr_m (u : Term signature_m [] Δ .num)
    {s t : Term signature_m [] Δ .num} (h : Derives T Γ (.equal s t)) :
    Derives T Γ (.equal (mul_m u s) (mul_m u t)) := by
  have h₁ := Metatheory.Derives.term_context_congr_of_equality
    (mul_m (u.weakenBound sort_m.num) (.bvar .here)) h
  simp only [mul_m, Term.instantiateTop_app, Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil, Term.instantiateTop_weakenBound] at h₁
  exact h₁

end YesMetaZFC.Logic.Arithmetic
