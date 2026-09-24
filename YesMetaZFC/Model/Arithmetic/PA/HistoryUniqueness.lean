import YesMetaZFC.Model.Arithmetic.PA.History

/-! # 确定性转移的内部历史唯一性

归纳公式比较两份 β 码在同一位置的读值；只在给定内部长度以内使用转移条件。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.History
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}
variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

theorem unique_m {R : num_l ℳ → num_l ℳ → Prop}
    {S : num_l ℳ → num_l ℳ → num_l ℳ → num_l ℳ → Prop}
    (hR : ∀ x a d, R x a → R x d → a = d)
    (hS : ∀ x i a d e, S x i a d → S x i a e → d = e)
    {x n y z : num_l ℳ} (hy : graph_l R S x n y) (hz : graph_l R S x n z) : y = z := by
  obtain ⟨b, c, ⟨a, hRa, ha⟩, hy, h₁⟩ := hy
  obtain ⟨d, e, ⟨v, hRv, hv⟩, hz, h₂⟩ := hz
  let φ : OpenFormula signature_m [.num, .num, .num, .num, .num, .num] :=
    .imp (le_m (.fvar .here) (.fvar (.there .here)))
      (.forallE .num (.forallE .num (.imp
        (Logic.Arithmetic.Beta.graph_m (.fvar (.there (.there .here)))
          (.fvar (.there (.there (.there .here)))) (.fvar .here) (.bvar (.there .here)))
        (.imp (Logic.Arithmetic.Beta.graph_m (.fvar (.there (.there (.there (.there .here)))))
          (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here) (.bvar .here))
          (.equal (.bvar (.there .here)) (.bvar .here))))))
  let η := (((((Env.empty (M := ℳ)).pushFree e).pushFree d).pushFree c).pushFree b).pushFree n
  have hφ (i : num_l ℳ) : φ.satisfies (η.pushFree i) ↔
      (le_l i n → ∀ p q, Beta.graph_l b c i p → Beta.graph_l d e i q → p = q) := by
    simp only [φ, Formula.satisfies, le_sat_m, Beta.graph_sat_m]
    rfl
  have h := induct_m hPA φ η
    (fun i => le_l i n → ∀ p q, Beta.graph_l b c i p → Beta.graph_l d e i q → p = q) hφ
    (by
      intro _ p q hp hq
      exact (Beta.unique_m hPA hp ha).trans ((hR x a v hRa hRv).trans (Beta.unique_m hPA hv hq)))
    (by
      intro i hi hin p q hp hq
      obtain ⟨r, s, hr, hs, hS₁⟩ := h₁ i hin
      obtain ⟨t, w, ht, hw, hS₂⟩ := h₂ i hin
      have hrt := hi (lt_le_m hPA hin) r t hr ht
      subst t
      exact (Beta.unique_m hPA hp hs).trans
        ((hS x i r s w hS₁ hS₂).trans (Beta.unique_m hPA hw hq)))
  exact h n (le_refl_m hPA n) y z hy hz

end YesMetaZFC.Model.Arithmetic.PA.History
