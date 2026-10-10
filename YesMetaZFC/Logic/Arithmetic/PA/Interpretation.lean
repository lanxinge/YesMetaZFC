import YesMetaZFC.Logic.Arithmetic.PA.TranslationBinders
import YesMetaZFC.Logic.Arithmetic.PA.Axioms
import YesMetaZFC.Logic.Arithmetic.Z2.Induction

/-! # PA 推导在 Z₂ 中的保真翻译

先传输原 Hilbert 逻辑公理及六种证明构造，再验证 PA 公理像。
这是正向解释，不是反向保守性，也不通过标准模型真值或完备性替代句法证明。
-/
namespace YesMetaZFC.Logic.Arithmetic.PA.Translation
open FirstOrder
set_option autoImplicit false
local notation "σ₀" => Arithmetic.signature_m
local notation "τ" => Z2.signature_m

def logical_m {Δ : SortContext σ₀} {φ : Formula σ₀ [] Δ}
    (h : HilbertBaseAxiom σ₀ φ) : HilbertBaseAxiom τ (formula_m φ) := by
  cases h with
  | implication_distribution φ ψ χ => exact .implication_distribution (formula_m φ) (formula_m ψ) (formula_m χ)
  | self_implication φ => exact .self_implication (formula_m φ)
  | weakening φ ψ => exact .weakening (formula_m φ) (formula_m ψ)
  | contradiction φ ψ => exact .contradiction (formula_m φ) (formula_m ψ)
  | classical φ => exact .classical (formula_m φ)
  | explosion φ ψ => exact .explosion (formula_m φ) (formula_m ψ)
  | case_analysis φ ψ => exact .case_analysis (formula_m φ) (formula_m ψ)
  | truth_intro => exact .truth_intro
  | falsum_elimination φ => exact .falsum_elimination (formula_m φ)
  | negation_intro φ => exact .negation_intro (formula_m φ)
  | negation_elimination φ => exact .negation_elimination (formula_m φ)
  | conjunction_intro φ ψ => exact .conjunction_intro (formula_m φ) (formula_m ψ)
  | conjunction_elim_left φ ψ => exact .conjunction_elim_left (formula_m φ) (formula_m ψ)
  | conjunction_elim_right φ ψ => exact .conjunction_elim_right (formula_m φ) (formula_m ψ)
  | disjunction_intro_left φ ψ => exact .disjunction_intro_left (formula_m φ) (formula_m ψ)
  | disjunction_intro_right φ ψ => exact .disjunction_intro_right (formula_m φ) (formula_m ψ)
  | disjunction_elimination φ ψ χ => exact .disjunction_elimination (formula_m φ) (formula_m ψ) (formula_m χ)
  | biconditional_intro φ ψ => exact .biconditional_intro (formula_m φ) (formula_m ψ)
  | biconditional_elim_left φ ψ => exact .biconditional_elim_left (formula_m φ) (formula_m ψ)
  | biconditional_elim_right φ ψ => exact .biconditional_elim_right (formula_m φ) (formula_m ψ)
  | forall_specialization s φ t =>
    simp only [formula_m, formula_instantiate_m]
    exact .forall_specialization (σ := τ) Z2.sort_m.num (formula_m φ) (term_m t)
  | forall_distribution s φ ψ =>
    simp only [formula_m, formula_forall_m]
    exact .forall_distribution (σ := τ) Z2.sort_m.num (formula_m φ) (formula_m ψ)
  | vacuous_forall s φ =>
    simp only [formula_m, formula_forall_m, formula_weaken_free_m]
    exact .vacuous_forall (σ := τ) Z2.sort_m.num (formula_m φ)
  | exists_introduction s φ t =>
    simp only [formula_m, formula_instantiate_m]
    exact .exists_introduction (σ := τ) Z2.sort_m.num (formula_m φ) (term_m t)
  | exists_elimination s φ ψ =>
    simp only [formula_m, formula_forall_m, formula_exists_m, formula_weaken_free_m]
    exact .exists_elimination (σ := τ) Z2.sort_m.num (formula_m φ) (formula_m ψ)
  | equality_substitution s t u φ =>
    simp only [formula_m, formula_instantiate_m]
    exact .equality_substitution (σ := τ) Z2.sort_m.num (term_m t) (term_m u) (formula_m φ)
  | equality_reflexivity t => exact .equality_reflexivity (term_m t)

private theorem sentence_weaken {T : Theory τ} {φ : Sentence τ}
    (h : Provable T φ) (Δ : SortContext τ) : Provable T (Formula.fromSentence (free := Δ) φ) := by
  cases Δ with
  | nil => exact h
  | cons s Δ =>
    have h₁ : Derives T ([] : Context τ (s :: Δ))
        (φ.renameFree VariableRenaming.empty) :=
      Derives.free_renaming (σ := τ) (Γ := []) VariableRenaming.empty h
    exact h₁

/-- 源理论的每个公理像可证，即可传输全部六种 Hilbert 构造。 -/
theorem provable_of_axioms_m {T : Theory σ₀} {U : Theory τ}
    (hTU : ∀ {φ : Sentence σ₀}, T φ → Provable U (formula_m φ))
    {Δ : SortContext σ₀} {φ : Formula σ₀ [] Δ} (h : Provable T φ) :
    Provable U (formula_m φ) := by
  rcases h with ⟨p⟩
  induction p with
  | logical_axiom h => exact Provable.logical_axiom (logical_m h)
  | @theory_axiom Δ φ h =>
    rw [formula_sentence_m]
    exact sentence_weaken (hTU h) _
  | modus_ponens p q h₁ h₂ => exact Provable.modus_ponens h₁ h₂
  | forall_generalization p h =>
    rw [formula_forall_m]
    exact Provable.forall_generalization h
  | free_strengthening p h =>
    rw [formula_weaken_free_m] at h
    exact Provable.free_strengthening h
  | free_substitution ρ p h =>
    rw [formula_subst_free_m]
    exact Provable.free_substitution (substitution_m ρ) h

theorem formula_discharge_m {Δ : SortContext σ₀} (Γ : Context σ₀ Δ) (φ : Formula σ₀ [] Δ) :
    formula_m (Context.discharge Γ φ) = Context.discharge (Γ.map formula_m) (formula_m φ) := by
  induction Γ generalizing φ with
  | nil => rfl
  | cons ψ Γ h => exact h (.imp ψ φ)

theorem derives_of_axioms_m {T : Theory σ₀} {U : Theory τ}
    (hTU : ∀ {φ : Sentence σ₀}, T φ → Provable U (formula_m φ))
    {Δ : SortContext σ₀} {Γ : Context σ₀ Δ} {φ : Formula σ₀ [] Δ} (h : Derives T Γ φ) :
    Derives U (Γ.map formula_m) (formula_m φ) := by
  change Provable U (Context.discharge (Γ.map formula_m) (formula_m φ))
  rw [← formula_discharge_m]
  exact provable_of_axioms_m hTU h

theorem substitution_next_m {Δ : SortContext σ₀} :
    @Eq (VariableSubstitution τ (context_m (.num :: Δ)) [] (context_m (.num :: Δ)))
      (substitution_m PA.next_m) Z2.next_m := by
  apply variable_ext_m (Γ := .num :: Δ)
  intro s v
  rw [substitution_variable_m]
  cases v <;> rfl

theorem induction_image_m {Δ : SortContext σ₀} (φ : Formula σ₀ [] (.num :: Δ)) :
    formula_m (PA.induction_m φ) = Z2.induction_m (formula_m φ) := by
  simp only [PA.induction_m, Z2.induction_m, formula_m, formula_instantiate_free_m,
    formula_forall_m, formula_subst_free_m, substitution_next_m]
  rfl

theorem number_image_m (k : Robinson.base_m) : formula_m (Q.sentence_m k) = Z2.number_m k := by
  cases k <;> rfl

/-- 验证 PA 的全部公理模式，而不向 Z₂ 增加新的模式公理。 -/
theorem axiom_derives_m {φ : Sentence σ₀} (h : PA.theory_m φ) :
    Provable Z2.theory_m (formula_m φ) := by
  cases h with
  | robinson h =>
    cases h with
    | base k =>
      rw [number_image_m]
      exact Provable.theory_axiom (Z2.axiom_m.number k)
  | induction φ =>
    rw [formula_close_m, induction_image_m]
    exact Metatheory.Derives.forall_close_of_derives (Z2.induction_derives_m (fun h => h) _)

/-- 任意带局部假设的 PA 推导，在 Z₂ 中保持其准确翻译。 -/
theorem derives_m {Δ : SortContext σ₀} {Γ : Context σ₀ Δ} {φ : Formula σ₀ [] Δ}
    (h : Derives PA.theory_m Γ φ) : Derives Z2.theory_m (Γ.map formula_m) (formula_m φ) :=
  derives_of_axioms_m axiom_derives_m h

end YesMetaZFC.Logic.Arithmetic.PA.Translation
