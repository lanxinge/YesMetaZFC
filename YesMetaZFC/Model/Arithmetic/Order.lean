import YesMetaZFC.Logic.Arithmetic.Order
import YesMetaZFC.Model.Arithmetic.Structure
import YesMetaZFC.Model.FirstOrder.SubstitutionSemantics

/-! # 可定义序在任意算术结构中的语义

这里只解释存在量词，不预设 Q、PA、全序性或标准性。
-/
namespace YesMetaZFC.Model.Arithmetic
open Logic FirstOrder Logic.Arithmetic
set_option autoImplicit false
universe u

def le_l {ℳ : Structure.{0, 0, 0, u} signature_m} (m n : num_l ℳ) : Prop :=
  ∃ k : num_l ℳ, add_l m k = n

def lt_l {ℳ : Structure.{0, 0, 0, u} signature_m} (m n : num_l ℳ) : Prop :=
  le_l (succ_l m) n

theorem le_sat_m {ℳ : Structure.{0, 0, 0, u} signature_m}
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    (le_m s t).satisfies η ↔ le_l (s.eval η) (t.eval η) := by
  rw [le_m, Formula.satisfies_existsFreeTop]
  simp only [le_body_m, Formula.satisfies, add_m, Term.eval, Arguments.eval,
    Term.eval_weakenFree]
  rfl

theorem lt_sat_m {ℳ : Structure.{0, 0, 0, u} signature_m}
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    (lt_m s t).satisfies η ↔ lt_l (s.eval η) (t.eval η) := le_sat_m η (succ_m s) t

end YesMetaZFC.Model.Arithmetic
