import YesMetaZFC.Model.Arithmetic.PA.PairingBounds

/-! # PA 全数域反配对的关系接口

反配对保留存在唯一性，不从 Prop 存在证明选择 Type 层的坐标函数。
-/
namespace YesMetaZFC.Model.Arithmetic.PA.Unpairing
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}

def left_l (z m : num_l ℳ) : Prop := ∃ n, Arithmetic.Pairing.graph_l m n z
def right_l (z n : num_l ℳ) : Prop := ∃ m, Arithmetic.Pairing.graph_l m n z

theorem left_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (s t : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Pairing.left_m s t).satisfies η ↔ left_l (s.eval η) (t.eval η) := by
  simp only [Logic.Arithmetic.Pairing.left_m, Formula.satisfies, Arithmetic.Pairing.graph_sat_m,
    Term.eval_weakenBound, Term.eval]
  rfl

theorem right_sat_m {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (s t : Term signature_m Γ Δ .num) :
    (Logic.Arithmetic.Pairing.right_m s t).satisfies η ↔ right_l (s.eval η) (t.eval η) := by
  simp only [Logic.Arithmetic.Pairing.right_m, Formula.satisfies, Arithmetic.Pairing.graph_sat_m,
    Term.eval_weakenBound, Term.eval]
  rfl

theorem total_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m) (z : num_l ℳ) :
    ∃ m n, Arithmetic.Pairing.graph_l m n z ∧ left_l z m ∧ right_l z n := by
  obtain ⟨m, n, h⟩ := Pairing.surjective_m hPA z
  exact ⟨m, n, h, ⟨n, h⟩, ⟨m, h⟩⟩

theorem left_unique_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    {z m n : num_l ℳ} (hm : left_l z m) (hn : left_l z n) : m = n := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  exact (Pairing.injective_m hPA m a n b ha hb).1

theorem right_unique_m (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
    {z m n : num_l ℳ} (hm : right_l z m) (hn : right_l z n) : m = n := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  exact (Pairing.injective_m hPA a m b n ha hb).2

end YesMetaZFC.Model.Arithmetic.PA.Unpairing
