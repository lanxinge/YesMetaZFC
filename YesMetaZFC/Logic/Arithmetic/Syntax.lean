import YesMetaZFC.Logic.Arithmetic.Signature
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Basic

/-! # 算术项与数码

所有操作保留任意绑定／自由上下文。数码替换不变性只涉及语法，
不需要算术公理，也不通过标准模型相等推回语法相等。
-/
namespace YesMetaZFC.Logic.Arithmetic
open FirstOrder
set_option autoImplicit false

variable {Γ Δ Θ Ξ : SortContext signature_m}

def zero_m : Term signature_m Γ Δ .num := Term.app (σ := signature_m) .zero .nil

def succ_m (t : Term signature_m Γ Δ .num) : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons t .nil)

def add_m (s t : Term signature_m Γ Δ .num) : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

def mul_m (s t : Term signature_m Γ Δ .num) : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .mul (.cons s (.cons t .nil))

/-- 外部自然数对应的有限一元数码项。 -/
def numeral_m : Nat → Term signature_m Γ Δ .num
  | 0 => zero_m
  | n + 1 => succ_m (numeral_m n)

@[simp] theorem numeral_subst_m (n : Nat)
    (ρ : VariableSubstitution signature_m Γ Θ Ξ)
    (τ : VariableSubstitution signature_m Δ Θ Ξ) :
    (numeral_m n).substituteMapped ρ τ = numeral_m n := by
  induction n with
  | zero => rfl
  | succ n h => simpa only [numeral_m, succ_m, Term.substituteMapped,
      Arguments.substituteMapped] using congrArg succ_m h

@[simp] theorem numeral_rename_m (n : Nat)
    (ρ : VariableRenaming Γ Θ) (τ : VariableRenaming Δ Ξ) :
    (numeral_m n).renameMapped ρ τ = numeral_m n := by
  rw [Term.renameMapped_eq_substituteMapped, numeral_subst_m]

end YesMetaZFC.Logic.Arithmetic
