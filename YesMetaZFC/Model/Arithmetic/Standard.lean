import YesMetaZFC.Model.Arithmetic.PA.Induction
import YesMetaZFC.Model.FirstOrder.Soundness

/-! # Q 与 PA 的标准模型

逐条验证实际公理闭句，再由通用可靠性得到 Lean 元层的一致性结论。
这些结论不是 Q 或 PA 在对象层的自一致性证明。
-/
namespace YesMetaZFC.Model.Arithmetic
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false

abbrev standard_m : Structure.{0, 0, 0, 0} signature_m where
  Carrier _ := Nat
  nonempty _ := ⟨0⟩
  funcInterp
    | .zero, .nil => 0
    | .succ, .cons n .nil => n + 1
    | .add, .cons m (.cons n .nil) => m + n
    | .mul, .cons m (.cons n .nil) => m * n
  relInterp r := nomatch r

theorem numeral_eval_m {Γ Δ : SortContext signature_m} (η : Env standard_m Γ Δ)
    (n : Nat) : (numeral_m n).eval η = n := by
  induction n with
  | zero => rfl
  | succ n h => exact congrArg Nat.succ h

theorem q_models_m : Theory.Models standard_m Q.theory_m := by
  intro φ h
  cases h with
  | base k =>
    apply (Automation.ModelClosure.forall_close_iff (Q.template_m k)).mpr
    intro η
    cases k <;> simp only [Q.template_m, Robinson.template_m, Formula.satisfies, zero_m, succ_m,
      add_m, mul_m, Term.eval, Arguments.eval]
    · exact Nat.succ_ne_zero _
    · exact Nat.succ.inj
    · change η.freeVal (.here : Variable [sort_m.num] sort_m.num) = 0 ∨
        ∃ n : Nat, η.freeVal .here = n + 1
      cases η.freeVal (.here : Variable [sort_m.num] sort_m.num) with
      | zero => exact Or.inl rfl
      | succ n => exact Or.inr ⟨n, rfl⟩
    · exact Nat.add_zero _
    · exact Nat.add_succ _ _
    · exact Nat.mul_zero _
    · exact Nat.mul_succ _ _

theorem pa_models_m : Theory.Models standard_m PA.theory_m := by
  intro φ h
  cases h with
  | robinson h => exact q_models_m _ h
  | induction φ =>
    apply (Automation.ModelClosure.forall_close_iff (PA.induction_m φ)).mpr
    intro η
    apply (induction_sat_m φ η).mpr
    intro h n
    exact Nat.rec h.1 (fun n hn => h.2 n hn) n

theorem q_consistent_m : ¬Derives Q.theory_m [] (.falsum : Sentence signature_m) := by
  intro h
  exact h.sound q_models_m Env.empty (by intro φ hφ; cases hφ)

theorem pa_consistent_m : ¬Derives PA.theory_m [] (.falsum : Sentence signature_m) := by
  intro h
  exact h.sound pa_models_m Env.empty (by intro φ hφ; cases hφ)

end YesMetaZFC.Model.Arithmetic
