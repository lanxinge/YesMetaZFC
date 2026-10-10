import YesMetaZFC.Model.Arithmetic.Z2.Comprehension

/-! # Z₂ 的标准全数集模型

使用 Nat 与 Nat → Prop，不依赖 Mathlib 的集合记号。
模型性和可靠性给出 Lean 元层一致性，不是 Z₂ 自证一致性。
-/
namespace YesMetaZFC.Model.Arithmetic.Z2
open Logic FirstOrder Logic.Arithmetic.Z2
set_option autoImplicit false

abbrev standard_m : Structure.{0, 0, 0, 0} signature_m where
  Carrier | .num => Nat | .set => Nat → Prop
  nonempty | .num => ⟨0⟩ | .set => ⟨fun _ => False⟩
  funcInterp
    | .zero, .nil => 0
    | .succ, .cons n .nil => n + 1
    | .add, .cons m (.cons n .nil) => m + n
    | .mul, .cons m (.cons n .nil) => m * n
  relInterp | .mem, .cons n (.cons X .nil) => X n

theorem number_sat_m (k : Logic.Arithmetic.Robinson.base_m) : (number_m k).TrueIn standard_m := by
  apply (Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  cases k <;> simp only [Logic.Arithmetic.Robinson.template_m, Formula.satisfies,
    zero_m, succ_m, add_m, mul_m, Term.eval, Arguments.eval]
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

theorem models_m : Theory.Models standard_m theory_m := by
  intro φ h
  cases h with
  | number k => exact number_sat_m k
  | extensionality =>
    change ∀ X Y : Nat → Prop, (∀ n, X n ↔ Y n) → X = Y
    intro X Y h
    exact funext (fun n => propext (h n))
  | set_induction =>
    rw [Formula.TrueIn, set_induction_m, Formula.satisfies_forallFreeTop]
    intro X
    apply (induction_sat_m _ _).mpr
    intro h n
    exact Nat.rec h.1 (fun n hn => h.2 n hn) n
  | comprehension φ =>
    apply (Automation.ModelClosure.forall_close_iff _).mpr
    intro η
    apply (comprehension_sat_m φ η).mpr
    exact ⟨fun n => Formula.satisfies (η.pushFree n) φ, fun _ => Iff.rfl⟩

theorem consistent_m : ¬Derives theory_m [] (.falsum : Sentence signature_m) := by
  intro h
  exact h.sound models_m Env.empty (by intro φ hφ; cases hφ)

end YesMetaZFC.Model.Arithmetic.Z2
