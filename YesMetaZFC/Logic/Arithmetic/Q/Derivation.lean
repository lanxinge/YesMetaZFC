import YesMetaZFC.Logic.Arithmetic.Q.Axioms

/-! # Q 公理的开放项实例

公开接口只要求目标理论包含 Q，且保留任意自由变量与局部上下文。
全部实例共用一个模板替换规则，不依赖 PA 归纳或模型可靠性。
-/
namespace YesMetaZFC.Logic.Arithmetic.Q
open FirstOrder
set_option autoImplicit false

variable {T : Theory signature_m} (hQ : Theory.Extends T theory_m)
variable {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
include hQ

theorem nonzero_m (t : Term signature_m [] Δ .num) :
    Derives T Γ (.neg (.equal (succ_m t) zero_m)) :=
  derives_m hQ .nonzero (VariableSubstitution.cons t VariableSubstitution.empty)

theorem injective_m (s t : Term signature_m [] Δ .num) :
    Derives T Γ (.imp (.equal (succ_m s) (succ_m t)) (.equal s t)) :=
  derives_m hQ .injective
    (VariableSubstitution.cons s (VariableSubstitution.cons t VariableSubstitution.empty))

theorem predecessor_m (t : Term signature_m [] Δ .num) :
    Derives T Γ (.disj (.equal t zero_m)
      (.existsE .num (.equal (t.weakenBound sort_m.num) (succ_m (.bvar .here))))) :=
  derives_m hQ .predecessor (VariableSubstitution.cons t VariableSubstitution.empty)

theorem add_zero_m (t : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (add_m t zero_m) t) :=
  derives_m hQ .add_zero (VariableSubstitution.cons t VariableSubstitution.empty)

theorem add_succ_m (s t : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (add_m s (succ_m t)) (succ_m (add_m s t))) :=
  derives_m hQ .add_succ
    (VariableSubstitution.cons s (VariableSubstitution.cons t VariableSubstitution.empty))

theorem mul_zero_m (t : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (mul_m t zero_m) zero_m) :=
  derives_m hQ .mul_zero (VariableSubstitution.cons t VariableSubstitution.empty)

theorem mul_succ_m (s t : Term signature_m [] Δ .num) :
    Derives T Γ (.equal (mul_m s (succ_m t)) (add_m (mul_m s t) s)) :=
  derives_m hQ .mul_succ
    (VariableSubstitution.cons s (VariableSubstitution.cons t VariableSubstitution.empty))

end YesMetaZFC.Logic.Arithmetic.Q
