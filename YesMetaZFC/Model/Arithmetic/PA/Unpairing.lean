import YesMetaZFC.Model.Arithmetic.PA.PairingBounds

/-! # PA 全数域的反配对与投影

选择只提供模型解释的宿主函数接口；对象层仍使用原语言的图，
其存在与唯一性已经由实际公式归纳及平方区间论证证明。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Unpairing
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}

noncomputable def value_l (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m) (z : num_l ℳ) :
    num_l ℳ × num_l ℳ :=
  ⟨(Pairing.surjective_m hPA z).choose, (Pairing.surjective_m hPA z).choose_spec.choose⟩

theorem pair_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m) (z : num_l ℳ) :
    Arithmetic.Pairing.value_l (value_l hPA z).1 (value_l hPA z).2 = z :=
  (Pairing.surjective_m hPA z).choose_spec.choose_spec

theorem unpair_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m) (m n : num_l ℳ) :
    value_l hPA (Arithmetic.Pairing.value_l m n) = (m, n) := by
  have h := Pairing.injective_m hPA _ _ m n (pair_m hPA (Arithmetic.Pairing.value_l m n))
  exact Prod.ext h.1 h.2

theorem left_sat_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Pairing.left_m s t).satisfies η ↔ (value_l hPA (s.eval η)).1 = t.eval η := by
  simp only [Logic.Arithmetic.Pairing.left_m, Formula.satisfies, Arithmetic.Pairing.graph_sat_m,
    Term.eval_weakenBound, Term.eval]
  change (∃ n, Arithmetic.Pairing.value_l (t.eval η) n = s.eval η) ↔ _
  constructor
  · rintro ⟨n, h⟩
    rw [← h, unpair_m]
  · intro h
    exact ⟨(value_l hPA (s.eval η)).2, by rw [← h, pair_m]⟩

theorem right_sat_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Pairing.right_m s t).satisfies η ↔ (value_l hPA (s.eval η)).2 = t.eval η := by
  simp only [Logic.Arithmetic.Pairing.right_m, Formula.satisfies, Arithmetic.Pairing.graph_sat_m,
    Term.eval_weakenBound, Term.eval]
  change (∃ m, Arithmetic.Pairing.value_l m (t.eval η) = s.eval η) ↔ _
  constructor
  · rintro ⟨m, h⟩
    rw [← h, unpair_m]
  · intro h
    exact ⟨(value_l hPA (s.eval η)).1, by rw [← h, pair_m]⟩

end YesMetaZFC.Model.Arithmetic.PA.Unpairing
