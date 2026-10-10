import YesMetaZFC.Model.Arithmetic.PA.BetaSequence

/-! # 内部 β 序列的单点延长

通过实际算术公式重新编码旧截段与末值。长度 n 是模型数，不使用宿主列表。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Beta
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}
variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

theorem extend_m (b c n v : num_l ℳ) :
    ∃ d e, graph_l d e n v ∧
      ∀ i, lt_l i n → ∀ a, graph_l d e i a ↔ graph_l b c i a := by
  let φ : OpenFormula signature_m [.num, .num, .num, .num, .num, .num] :=
    .disj (.conj (lt_m (.fvar (.there .here)) (.fvar (.there (.there .here))))
      (Logic.Arithmetic.Beta.graph_m (.fvar (.there (.there (.there (.there (.there .here))))))
        (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here)) (.fvar .here)))
      (.conj (.equal (.fvar (.there .here)) (.fvar (.there (.there .here))))
        (.equal (.fvar .here) (.fvar (.there (.there (.there .here))))))
  let η := ((((Env.empty (M := ℳ)).pushFree b).pushFree c).pushFree v).pushFree n
  have hφ (i a : num_l ℳ) : φ.satisfies ((η.pushFree i).pushFree a) ↔
      (lt_l i n ∧ graph_l b c i a) ∨ (i = n ∧ a = v) := by
    simp only [φ, Formula.satisfies, lt_sat_m, graph_sat_m]
    rfl
  obtain ⟨d, e, h⟩ := sequence_m hPA φ η (succ_l n) (by
    intro i hi
    rcases le_cases_m hPA ((lt_succ_m hPA).mp hi) with hEq | hi
    · subst i
      refine ⟨v, (hφ n v).mpr (Or.inr ⟨rfl, rfl⟩), ?_⟩
      intro a ha
      rcases (hφ n a).mp ha with ha | ha
      · exact False.elim (lt_irrefl_m hPA n ha.1)
      · exact ha.2
    · obtain ⟨a, ha⟩ := total_m hPA b c i
      refine ⟨a, (hφ i a).mpr (Or.inl ⟨hi, ha⟩), ?_⟩
      intro z hz
      rcases (hφ i z).mp hz with hz | hz
      · exact unique_m hPA hz.2 ha
      · exact False.elim (lt_irrefl_m hPA n (hz.1 ▸ hi)))
  refine ⟨d, e, (h n ((lt_succ_m hPA).mpr (le_refl_m hPA n)) v).mpr
    ((hφ n v).mpr (Or.inr ⟨rfl, rfl⟩)), ?_⟩
  intro i hi a
  rw [h i ((lt_succ_m hPA).mpr (lt_le_m hPA hi)) a, hφ]
  constructor
  · rintro (ha | ha)
    · exact ha.2
    · exact False.elim (lt_irrefl_m hPA n (ha.1 ▸ hi))
  · exact fun ha => Or.inl ⟨hi, ha⟩

theorem singleton_m (a : num_l ℳ) : ∃ b c, graph_l b c (zero_l ℳ) a := by
  obtain ⟨b, c, h, _⟩ := extend_m hPA (zero_l ℳ) (zero_l ℳ) (zero_l ℳ) a
  exact ⟨b, c, h⟩

end YesMetaZFC.Model.Arithmetic.PA.Beta
