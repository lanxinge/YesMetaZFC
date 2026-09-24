import YesMetaZFC.Model.Arithmetic.PA.LinearOrder

/-! # PA 模型中的带参数可定义最小元

只对实际算术公式所定义的非空数类取最小元。归纳公式表示有界区间
不含见证，不假定内部数序在外部良基，不对任意宿主谓词使用归纳。
-/
namespace YesMetaZFC.Model.Arithmetic.PA
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u

variable {ℳ : Structure.{0, 0, 0, u} signature_m}

/-- 共同最小化论证。对 P 的有界无见证归纳必须显式提供，不能仅由模型性推出。 -/
theorem minimum_rule_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    (P : num_l ℳ → Prop)
    (hI : (∀ m, le_l m (zero_l ℳ) → ¬P m) →
      (∀ n, (∀ m, le_l m n → ¬P m) → ∀ m, le_l m (succ_l n) → ¬P m) →
      ∀ n m, le_l m n → ¬P m)
    (hP : ∃ n, P n) : ∃ n, P n ∧ ∀ m, lt_l m n → ¬P m := by
  classical
  apply Classical.byContradiction
  intro h
  have h₁ (n : num_l ℳ) (hn : P n) : ∃ m, lt_l m n ∧ P m := by
    apply Classical.byContradiction
    intro h₂
    exact h ⟨n, hn, fun m hm hP => h₂ ⟨m, hm, hP⟩⟩
  have h₂ : ∀ n m, le_l m n → ¬P m := by
    apply hI
    · intro m hm hP
      have hm₀ := le_antisymm_m hPA hm (zero_le_m hPA m)
      obtain ⟨k, hk, _⟩ := h₁ m hP
      apply not_lt_of_le_m hPA (m := k) (n := m) ?_ hk
      rw [hm₀]
      exact zero_le_m hPA k
    · intro n hn m hm hP
      rcases le_cases_m hPA hm with hm | hm
      · obtain ⟨k, hk, hP⟩ := h₁ m hP
        have hk₁ : lt_l k (succ_l n) := hm ▸ hk
        exact hn k ((lt_succ_m hPA).mp hk₁) hP
      · exact hn m ((lt_succ_m hPA).mp hm) hP
  obtain ⟨n, hn⟩ := hP
  exact h₂ n n (le_refl_m hPA n) hn

/-- 候选以下没有 P 点，则该候选不大于任意 P 点；不要求 P 可定义。 -/
theorem minimum_le_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    {P : num_l ℳ → Prop} {n : num_l ℳ} (h : ∀ m, lt_l m n → ¬P m)
    (m : num_l ℳ) (hm : P m) : le_l n m := by
  rcases le_total_m hPA n m with h₁ | h₁
  · exact h₁
  · rcases le_cases_m hPA h₁ with h₁ | h₁
    · rw [h₁]
      exact le_refl_m hPA n
    · exact False.elim (h m h₁ hm)

theorem minimum_unique_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    {P : num_l ℳ → Prop} {m n : num_l ℳ} (hm : P m) (hn : P n)
    (h₁ : ∀ k, lt_l k m → ¬P k) (h₂ : ∀ k, lt_l k n → ¬P k) : m = n :=
  le_antisymm_m hPA (minimum_le_m hPA h₁ n hn) (minimum_le_m hPA h₂ m hm)

theorem minimum_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ)) (η : Env ℳ [] Δ)
    (hφ : ∃ n : num_l ℳ, φ.satisfies (η.pushFree n)) :
    ∃ n : num_l ℳ, φ.satisfies (η.pushFree n) ∧
      ∀ m : num_l ℳ, lt_l m n → ¬φ.satisfies (η.pushFree m) := by
  apply minimum_rule_m hPA (fun n => φ.satisfies (η.pushFree n)) ?_ hφ
  intro h₀ h₁
  let χ := φ.renameFree (VariableRenaming.lift (VariableRenaming.weaken sort_m.num))
  let ψ : Formula signature_m [] (.num :: Δ) :=
    (Formula.imp (le_m (.fvar .here) (.fvar (.there .here))) (.neg χ)).forallFreeTop sort_m.num
  have hχ (n m : num_l ℳ) : χ.satisfies ((η.pushFree n).pushFree m) ↔
      φ.satisfies (η.pushFree m) := by
    unfold χ Formula.renameFree
    rw [Formula.satisfies_rename]
    apply Iff.of_eq
    apply congrArg (fun η => φ.satisfies η)
    apply Env.ext
    · intro s v; cases v
    · intro s v; cases v <;> rfl
  have hψ (n : num_l ℳ) : ψ.satisfies (η.pushFree n) ↔
      ∀ m : num_l ℳ, le_l m n → ¬φ.satisfies (η.pushFree m) := by
    simp only [ψ, Formula.satisfies_forallFreeTop, Formula.satisfies, le_sat_m, hχ]
    rfl
  exact induct_m hPA ψ η (fun n => ∀ m, le_l m n → ¬φ.satisfies (η.pushFree m)) hψ h₀ h₁

end YesMetaZFC.Model.Arithmetic.PA
