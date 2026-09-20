import YesMetaZFC.Logic.Arithmetic.Z2.Order
import YesMetaZFC.Model.Arithmetic.Z2.Reduct
import YesMetaZFC.Model.Arithmetic.Order

/-! # 双排序数序与 PA 数域约化的对应

复用约化上的数序，不复制偏序／全序证明。逐公式语义不要求模型性。
-/
namespace YesMetaZFC.Model.Arithmetic.Z2
open Logic FirstOrder Logic.Arithmetic.Z2
set_option autoImplicit false
universe u

abbrev le_l {ℳ : Structure.{0, 0, 0, u} signature_m} (m n : num_l ℳ) : Prop :=
  Arithmetic.le_l (ℳ := reduct_m ℳ) m n

abbrev lt_l {ℳ : Structure.{0, 0, 0, u} signature_m} (m n : num_l ℳ) : Prop :=
  Arithmetic.lt_l (ℳ := reduct_m ℳ) m n

theorem le_sat_m {ℳ : Structure.{0, 0, 0, u} signature_m}
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    (le_m s t).satisfies η ↔ le_l (s.eval η) (t.eval η) := by
  rw [le_m, Formula.satisfies_existsFreeTop]
  simp only [Formula.satisfies, add_m, Term.eval, Arguments.eval, Term.eval_weakenFree]
  rfl

theorem lt_sat_m {ℳ : Structure.{0, 0, 0, u} signature_m}
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    (lt_m s t).satisfies η ↔ lt_l (s.eval η) (t.eval η) := le_sat_m η (succ_m s) t

end YesMetaZFC.Model.Arithmetic.Z2
