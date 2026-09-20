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

theorem minimum_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ)) (η : Env ℳ [] Δ)
    (hφ : ∃ n : num_l ℳ, φ.satisfies (η.pushFree n)) :
    ∃ n : num_l ℳ, φ.satisfies (η.pushFree n) ∧
      ∀ m : num_l ℳ, lt_l m n → ¬φ.satisfies (η.pushFree m) := by
  classical
  apply Classical.byContradiction
  intro h
  have h₁ (n : num_l ℳ) (hn : φ.satisfies (η.pushFree n)) :
      ∃ m : num_l ℳ, lt_l m n ∧ φ.satisfies (η.pushFree m) := by
    apply Classical.byContradiction
    intro h₂
    exact h ⟨n, hn, fun m hm hφ => h₂ ⟨m, hm, hφ⟩⟩
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
  have h₂ : ∀ n : num_l ℳ, ∀ m : num_l ℳ, le_l m n → ¬φ.satisfies (η.pushFree m) := by
    apply induct_m hPA ψ η (fun n => ∀ m, le_l m n → ¬φ.satisfies (η.pushFree m)) hψ
    · intro m hm hφ
      have hm₀ := le_antisymm_m hPA hm (zero_le_m hPA m)
      obtain ⟨k, hk, _⟩ := h₁ m hφ
      apply not_lt_of_le_m hPA (m := k) (n := m) ?_ hk
      rw [hm₀]
      exact zero_le_m hPA k
    · intro n hn m hm hφ
      rcases le_cases_m hPA hm with hm | hm
      · obtain ⟨k, hk, hφ⟩ := h₁ m hφ
        have hk₁ : lt_l k (succ_l n) := hm ▸ hk
        exact hn k ((lt_succ_m hPA).mp hk₁) hφ
      · exact hn m ((lt_succ_m hPA).mp hm) hφ
  obtain ⟨n, hn⟩ := hφ
  exact h₂ n n (le_refl_m hPA n) hn

end YesMetaZFC.Model.Arithmetic.PA
