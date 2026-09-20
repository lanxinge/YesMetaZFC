import YesMetaZFC.Logic.Arithmetic.Syntax
import YesMetaZFC.Logic.Arithmetic.Z2.Syntax

/-! # 单排序算术到 Z₂ 的结构翻译

保留变量位置、数目函数和所有逻辑联结词；源数量词只译成数量词。
本层不使用任何理论公理或模型假设。
-/
namespace YesMetaZFC.Logic.Arithmetic.PA.Translation
open FirstOrder
set_option autoImplicit false
local notation "σ₀" => Arithmetic.signature_m
local notation "τ" => Z2.signature_m

def context_m (Γ : SortContext σ₀) : SortContext τ := Γ.map (fun _ => Z2.sort_m.num)

def variable_m {Γ : SortContext σ₀} {s : Arithmetic.sort_m} :
    Variable Γ s → Variable (context_m Γ) Z2.sort_m.num
  | .here => .here
  | .there v => .there (variable_m v)

private def app {Γ Δ : SortContext σ₀} (f : Arithmetic.func_m) :
    Arguments τ (context_m Γ) (context_m Δ) (context_m ((σ₀).funcDomain f)) →
      Term τ (context_m Γ) (context_m Δ) .num :=
  match f with
  | .zero => Term.app (σ := τ) .zero
  | .succ => Term.app (σ := τ) .succ
  | .add => Term.app (σ := τ) .add
  | .mul => Term.app (σ := τ) .mul

mutual
def term_m {Γ Δ : SortContext σ₀} : {s : Arithmetic.sort_m} →
    Term σ₀ Γ Δ s → Term τ (context_m Γ) (context_m Δ) .num
  | _, .bvar v => .bvar (variable_m v)
  | _, .fvar v => .fvar (variable_m v)
  | _, .app f a => app f (arguments_m a)

def arguments_m {Γ Δ : SortContext σ₀} : {Θ : SortContext σ₀} →
    Arguments σ₀ Γ Δ Θ → Arguments τ (context_m Γ) (context_m Δ) (context_m Θ)
  | _, .nil => .nil
  | _, .cons t a => .cons (term_m t) (arguments_m a)
end

def formula_m {Γ Δ : SortContext σ₀} : Formula σ₀ Γ Δ → Formula τ (context_m Γ) (context_m Δ)
  | .falsum => .falsum
  | .truth => .truth
  | .rel r _ => nomatch r
  | .equal s t => .equal (term_m s) (term_m t)
  | .neg φ => .neg (formula_m φ)
  | .conj φ ψ => .conj (formula_m φ) (formula_m ψ)
  | .disj φ ψ => .disj (formula_m φ) (formula_m ψ)
  | .imp φ ψ => .imp (formula_m φ) (formula_m ψ)
  | .iff φ ψ => .iff (formula_m φ) (formula_m ψ)
  | .forallE _ φ => .forallE .num (formula_m φ)
  | .existsE _ φ => .existsE .num (formula_m φ)

def renaming_m {Γ Δ : SortContext σ₀} (ρ : VariableRenaming Γ Δ) :
    VariableRenaming (context_m Γ) (context_m Δ) :=
  fun {s} v => match Γ, v with
    | [], v => nomatch v
    | _ :: _, .here => variable_m (ρ .here)
    | _ :: _, .there v => renaming_m (fun v => ρ (.there v)) v

@[simp] theorem renaming_variable_m {Γ Δ : SortContext σ₀} (ρ : VariableRenaming Γ Δ)
    {s : Arithmetic.sort_m} (v : Variable Γ s) :
    renaming_m ρ (variable_m v) = variable_m (ρ v) := by
  induction v with
  | here => rfl
  | there v h => exact h (fun v => ρ (.there v))

def substitution_m {Γ Θ Ξ : SortContext σ₀} (ρ : VariableSubstitution σ₀ Γ Θ Ξ) :
    VariableSubstitution τ (context_m Γ) (context_m Θ) (context_m Ξ) :=
  fun {s} v => match Γ, v with
    | [], v => nomatch v
    | _ :: _, .here => term_m (ρ .here)
    | _ :: _, .there v => substitution_m (fun v => ρ (.there v)) v

@[simp] theorem substitution_variable_m {Γ Θ Ξ : SortContext σ₀}
    (ρ : VariableSubstitution σ₀ Γ Θ Ξ) {s : Arithmetic.sort_m} (v : Variable Γ s) :
    substitution_m ρ (variable_m v) = term_m (ρ v) := by
  induction v with
  | here => rfl
  | there v h => exact h (fun v => ρ (.there v))

universe u

/-- 映射后的上下文只有源变量；逐源变量相等足以得到映射相等。 -/
theorem variable_ext_m {Γ : SortContext σ₀} {C : Z2.sort_m → Sort u}
    {f g : {s : Z2.sort_m} → Variable (context_m Γ) s → C s}
    (h : ∀ {s : Arithmetic.sort_m} (v : Variable Γ s), f (variable_m v) = g (variable_m v)) :
    @f = @g := by
  funext s v
  cases Γ with
  | nil => exact nomatch v
  | cons t Γ =>
    cases v with
    | here => exact h .here
    | there v =>
      exact congrFun (congrFun (variable_ext_m (Γ := Γ) (f := fun v => f (.there v))
        (g := fun v => g (.there v)) (fun v => h (.there v))) _) v

@[simp] theorem renaming_id_m {Γ : SortContext σ₀} :
    @Eq (VariableRenaming (context_m Γ) (context_m Γ))
      (renaming_m VariableRenaming.id) VariableRenaming.id := by
  apply variable_ext_m
  intro s v
  exact renaming_variable_m _ v

@[simp] theorem renaming_weaken_m {Γ : SortContext σ₀} (s : Arithmetic.sort_m) :
    @Eq (VariableRenaming (context_m Γ) (context_m (s :: Γ)))
      (renaming_m (VariableRenaming.weaken s)) (VariableRenaming.weaken Z2.sort_m.num) := by
  apply variable_ext_m
  intro t v
  exact renaming_variable_m _ v

@[simp] theorem renaming_lift_m {Γ Δ : SortContext σ₀} (s : Arithmetic.sort_m)
    (ρ : VariableRenaming Γ Δ) :
    @Eq (VariableRenaming (context_m (s :: Γ)) (context_m (s :: Δ)))
      (renaming_m (VariableRenaming.lift (introduced := s) ρ))
      (VariableRenaming.lift (introduced := Z2.sort_m.num) (renaming_m ρ)) := by
  apply variable_ext_m (Γ := s :: Γ)
  intro t v
  rw [renaming_variable_m]
  cases v with
  | here => rfl
  | there v => exact congrArg Variable.there (renaming_variable_m ρ v).symm

mutual
theorem term_rename_m {Γ Δ Θ Ξ : SortContext σ₀} (ρ : VariableRenaming Γ Θ)
    (υ : VariableRenaming Δ Ξ) {s : Arithmetic.sort_m} (t : Term σ₀ Γ Δ s) :
    term_m (t.renameMapped ρ υ) = (term_m t).renameMapped (renaming_m ρ) (renaming_m υ) := by
  match t with
  | .bvar v => exact congrArg Term.bvar (renaming_variable_m ρ v).symm
  | .fvar v => exact congrArg Term.fvar (renaming_variable_m υ v).symm
  | .app f a =>
    have h := congrArg (app (Γ := Θ) (Δ := Ξ) f) (arguments_rename_m ρ υ a)
    cases f <;> exact h

theorem arguments_rename_m {Γ Δ Θ Ξ Λ : SortContext σ₀} (ρ : VariableRenaming Γ Θ)
    (υ : VariableRenaming Δ Ξ) (a : Arguments σ₀ Γ Δ Λ) :
    arguments_m (a.renameMapped ρ υ) =
      (arguments_m a).renameMapped (renaming_m ρ) (renaming_m υ) := by
  match a with
  | .nil => rfl
  | .cons t a =>
    simp only [Arguments.renameMapped, arguments_m, term_rename_m, arguments_rename_m]
    rfl
end

theorem formula_rename_m {Γ Δ Θ Ξ : SortContext σ₀} (ρ : VariableRenaming Γ Θ)
    (υ : VariableRenaming Δ Ξ) (φ : Formula σ₀ Γ Δ) :
    formula_m (φ.renameMapped ρ υ) =
      (formula_m φ).renameMapped (renaming_m ρ) (renaming_m υ) := by
  match φ with
  | .falsum | .truth => rfl
  | .rel r _ => exact nomatch r
  | .equal s t => simp only [Formula.renameMapped, formula_m, term_rename_m]
  | .neg φ => simp only [Formula.renameMapped, formula_m, formula_rename_m]
  | .conj φ ψ | .disj φ ψ | .imp φ ψ | .iff φ ψ =>
    simp only [Formula.renameMapped, formula_m, formula_rename_m]
  | .forallE s φ | .existsE s φ =>
    simp only [Formula.renameMapped, formula_m, formula_rename_m, renaming_lift_m]
    rfl

@[simp] theorem term_weaken_bound_m {Γ Δ : SortContext σ₀} (s : Arithmetic.sort_m)
    {t : Arithmetic.sort_m} (a : Term σ₀ Γ Δ t) :
    term_m (a.weakenBound s) = (term_m a).weakenBound Z2.sort_m.num := by
  change term_m (a.renameMapped _ _) = _
  rw [term_rename_m, renaming_weaken_m, renaming_id_m]
  rfl

@[simp] theorem formula_weaken_free_m {Γ Δ : SortContext σ₀} (s : Arithmetic.sort_m)
    (φ : Formula σ₀ Γ Δ) :
    formula_m (φ.weakenFree s) = (formula_m φ).weakenFree Z2.sort_m.num := by
  change formula_m (φ.renameMapped _ _) = _
  rw [formula_rename_m, renaming_id_m, renaming_weaken_m]
  rfl

@[simp] theorem substitution_weaken_m {Γ Θ Ξ : SortContext σ₀} (s : Arithmetic.sort_m)
    (ρ : VariableSubstitution σ₀ Γ Θ Ξ) :
    @Eq (VariableSubstitution τ (context_m Γ) (context_m (s :: Θ)) (context_m Ξ))
      (substitution_m (VariableSubstitution.weakenBound s ρ))
      (VariableSubstitution.weakenBound Z2.sort_m.num (substitution_m ρ)) := by
  apply variable_ext_m
  intro t v
  simp only [substitution_variable_m, VariableSubstitution.weakenBound, term_weaken_bound_m]
  rfl

@[simp] theorem substitution_lift_m {Γ Θ Ξ : SortContext σ₀} (s : Arithmetic.sort_m)
    (ρ : VariableSubstitution σ₀ Γ Θ Ξ) :
    @Eq (VariableSubstitution τ (context_m (s :: Γ)) (context_m (s :: Θ)) (context_m Ξ))
      (substitution_m (VariableSubstitution.liftBound s ρ))
      (VariableSubstitution.liftBound (σ := τ) Z2.sort_m.num (substitution_m ρ)) := by
  apply variable_ext_m (Γ := s :: Γ)
  intro t v
  rw [substitution_variable_m]
  cases v with
  | here => rfl
  | there v =>
    change term_m ((ρ v).weakenBound s) = (substitution_m ρ (variable_m v)).weakenBound _
    rw [term_weaken_bound_m, substitution_variable_m]

mutual
theorem term_subst_m {Γ Δ Θ Ξ : SortContext σ₀} (ρ : VariableSubstitution σ₀ Γ Θ Ξ)
    (υ : VariableSubstitution σ₀ Δ Θ Ξ) {s : Arithmetic.sort_m} (t : Term σ₀ Γ Δ s) :
    term_m (t.substituteMapped ρ υ) =
      (term_m t).substituteMapped (substitution_m ρ) (substitution_m υ) := by
  match t with
  | .bvar v => exact (substitution_variable_m ρ v).symm
  | .fvar v => exact (substitution_variable_m υ v).symm
  | .app f a =>
    have h := congrArg (app (Γ := Θ) (Δ := Ξ) f) (arguments_subst_m ρ υ a)
    cases f <;> exact h

theorem arguments_subst_m {Γ Δ Θ Ξ Λ : SortContext σ₀} (ρ : VariableSubstitution σ₀ Γ Θ Ξ)
    (υ : VariableSubstitution σ₀ Δ Θ Ξ) (a : Arguments σ₀ Γ Δ Λ) :
    arguments_m (a.substituteMapped ρ υ) =
      (arguments_m a).substituteMapped (substitution_m ρ) (substitution_m υ) := by
  match a with
  | .nil => rfl
  | .cons t a =>
    simp only [Arguments.substituteMapped, arguments_m, term_subst_m, arguments_subst_m]
    rfl
end

theorem formula_subst_m {Γ Δ Θ Ξ : SortContext σ₀} (ρ : VariableSubstitution σ₀ Γ Θ Ξ)
    (υ : VariableSubstitution σ₀ Δ Θ Ξ) (φ : Formula σ₀ Γ Δ) :
    formula_m (φ.substituteMapped ρ υ) =
      (formula_m φ).substituteMapped (substitution_m ρ) (substitution_m υ) := by
  match φ with
  | .falsum | .truth => rfl
  | .rel r _ => exact nomatch r
  | .equal s t => simp only [Formula.substituteMapped, formula_m, term_subst_m]
  | .neg φ => simp only [Formula.substituteMapped, formula_m, formula_subst_m]
  | .conj φ ψ | .disj φ ψ | .imp φ ψ | .iff φ ψ =>
    simp only [Formula.substituteMapped, formula_m, formula_subst_m]
  | .forallE s φ | .existsE s φ =>
    simp only [Formula.substituteMapped, formula_m, formula_subst_m,
      substitution_lift_m, substitution_weaken_m]
    rfl

end YesMetaZFC.Logic.Arithmetic.PA.Translation
