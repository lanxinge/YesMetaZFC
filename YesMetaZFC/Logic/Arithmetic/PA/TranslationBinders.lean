import YesMetaZFC.Logic.Arithmetic.PA.Translation
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure

/-! # 算术翻译与绑定操作相容

由同时替换定理统一推出实例化、自由变量抽象、量化和闭包保持。
所有参数上下文均保留，不用有限数值样例代替一般公式定理。
-/
namespace YesMetaZFC.Logic.Arithmetic.PA.Translation
open FirstOrder
set_option autoImplicit false
local notation "σ₀" => Arithmetic.signature_m
local notation "τ" => Z2.signature_m

theorem formula_subst_free_m {Γ Δ Ξ : SortContext σ₀}
    (ρ : VariableSubstitution σ₀ Δ Γ Ξ) (φ : Formula σ₀ Γ Δ) :
    formula_m (φ.substituteFree ρ) = (formula_m φ).substituteFree (substitution_m ρ) := by
  change formula_m (φ.substituteMapped _ _) = (formula_m φ).substituteMapped _ _
  rw [formula_subst_m]
  congr 1
  apply variable_ext_m
  intro s v
  rw [substitution_variable_m]
  rfl

theorem formula_instantiate_m {Γ Δ : SortContext σ₀} {s : Arithmetic.sort_m}
    (t : Term σ₀ Γ Δ s) (φ : Formula σ₀ (s :: Γ) Δ) :
    formula_m (φ.instantiateTop t) = (formula_m φ).instantiateTop (term_m t) := by
  change formula_m (φ.substituteMapped _ _) = (formula_m φ).substituteMapped _ _
  rw [formula_subst_m]
  congr 1
  · apply variable_ext_m (Γ := s :: Γ)
    intro t v
    rw [substitution_variable_m]
    cases v <;> rfl
  · apply variable_ext_m (Γ := Δ)
    intro t v
    rw [substitution_variable_m]
    rfl

theorem formula_instantiate_free_m {Γ Δ : SortContext σ₀} {s : Arithmetic.sort_m}
    (t : Term σ₀ Γ Δ s) (φ : Formula σ₀ Γ (s :: Δ)) :
    formula_m (φ.instantiateFreeTop t) = (formula_m φ).instantiateFreeTop (term_m t) := by
  change formula_m (φ.substituteMapped _ _) = (formula_m φ).substituteMapped _ _
  rw [formula_subst_m]
  congr 1
  · apply variable_ext_m (Γ := Γ)
    intro t v
    rw [substitution_variable_m]
    rfl
  · apply variable_ext_m (Γ := s :: Δ)
    intro t v
    rw [substitution_variable_m]
    cases v <;> rfl

theorem formula_abstract_m {Γ Δ : SortContext σ₀} {s : Arithmetic.sort_m}
    (φ : Formula σ₀ Γ (s :: Δ)) :
    formula_m φ.abstractFreeTop = (formula_m φ).abstractFreeTop := by
  change formula_m (φ.substituteMapped _ _) = (formula_m φ).substituteMapped _ _
  rw [formula_subst_m]
  congr 1
  · apply variable_ext_m (Γ := Γ)
    intro t v
    rw [substitution_variable_m]
    rfl
  · apply variable_ext_m (Γ := s :: Δ)
    intro t v
    rw [substitution_variable_m]
    cases v <;> rfl

theorem formula_forall_m {Γ Δ : SortContext σ₀} (s : Arithmetic.sort_m)
    (φ : Formula σ₀ Γ (s :: Δ)) :
    formula_m (φ.forallFreeTop s) = (formula_m φ).forallFreeTop Z2.sort_m.num := by
  simp only [Formula.forallFreeTop, formula_m, formula_abstract_m]
  rfl

theorem formula_exists_m {Γ Δ : SortContext σ₀} (s : Arithmetic.sort_m)
    (φ : Formula σ₀ Γ (s :: Δ)) :
    formula_m (φ.existsFreeTop s) = (formula_m φ).existsFreeTop Z2.sort_m.num := by
  simp only [Formula.existsFreeTop, formula_m, formula_abstract_m]
  rfl

theorem formula_sentence_m (Δ : SortContext σ₀) (φ : Sentence σ₀) :
    formula_m (Formula.fromSentence (free := Δ) φ) = Formula.fromSentence (formula_m φ) := by
  cases Δ with
  | nil => rfl
  | cons s Δ =>
    change formula_m (φ.renameMapped _ _) = (formula_m φ).renameMapped _ _
    rw [formula_rename_m, renaming_id_m]
    congr 1
    apply variable_ext_m (Γ := [])
    intro t v
    cases v

theorem formula_close_m {Δ : SortContext σ₀} (φ : Formula σ₀ [] Δ) :
    formula_m (Metatheory.Formula.forall_close φ) =
      Metatheory.Formula.forall_close (formula_m φ) := by
  induction Δ with
  | nil => rfl
  | cons s Δ h =>
    change formula_m (Metatheory.Formula.forall_close (φ.forallFreeTop s)) = _
    rw [h, formula_forall_m]
    rfl

end YesMetaZFC.Logic.Arithmetic.PA.Translation
