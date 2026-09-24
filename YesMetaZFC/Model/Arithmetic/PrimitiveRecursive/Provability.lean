import YesMetaZFC.Model.Arithmetic.PrimitiveRecursive.Numeral
import YesMetaZFC.Model.Arithmetic.Completeness

/-! # PA 中逐程序可推导的总性与函数性

从全部原 PA 模型中的已证结论调用一阶完备性；不从标准模型真值反射为可证性。
本模块按需导入，不进入不依赖完备性的核心入口。
-/
namespace YesMetaZFC.Model.Arithmetic.PrimitiveRecursive.Provability
open Logic FirstOrder Logic.Arithmetic Logic.Arithmetic.PrimitiveRecursive
set_option autoImplicit false
variable {T : Theory signature_m} (hPA : Theory.Extends T Logic.Arithmetic.PA.theory_m)
variable {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
include hPA

theorem total_m (c : code_m) (s : Term signature_m [] Δ .num) :
    Derives T Γ (.existsE .num (graph_m c (s.weakenBound sort_m.num) (.bvar .here))) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, graph_sat_m, Term.eval_weakenBound]
  exact PrimitiveRecursive.total_m hℳ c (s.eval η)

theorem unique_m (c : code_m) (s t v : Term signature_m [] Δ .num) :
    Derives T Γ (.imp (graph_m c s t) (.imp (graph_m c s v) (.equal t v))) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, graph_sat_m]
  exact fun ht hv => PrimitiveRecursive.unique_m hℳ c ht hv

/-- 标准输入下，任意对象输出都等价于正确求值数码；不限于标准输出。 -/
theorem numeral_m (c : code_m) (n : Nat) (t : Term signature_m [] Δ .num) :
    Derives T Γ (.iff (graph_m c (Logic.Arithmetic.numeral_m n) t)
      (.equal (Logic.Arithmetic.numeral_m (eval_l c n)) t)) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, graph_sat_m, Numeral.eval_m]
  exact numeral_iff_m hℳ c n (t.eval η)

theorem evaluates_m (c : code_m) (n : Nat) :
    Derives T Γ (graph_m c (Logic.Arithmetic.numeral_m n) (Logic.Arithmetic.numeral_m (eval_l c n))) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [graph_sat_m, Numeral.eval_m]
  exact PrimitiveRecursive.numeral_m hℳ c n

theorem rejects_m (c : code_m) (n k : Nat) (h : eval_l c n ≠ k) :
    Derives T Γ (.neg (graph_m c (Logic.Arithmetic.numeral_m n) (Logic.Arithmetic.numeral_m k))) := by
  apply Derives.theory_weaken hPA
  apply Completeness.derives_m
  intro ℳ hℳ η
  simp only [Formula.satisfies, graph_sat_m, Numeral.eval_m]
  intro hc
  exact h (Numeral.injective_m hℳ ((numeral_iff_m hℳ c n _).mp hc))

end YesMetaZFC.Model.Arithmetic.PrimitiveRecursive.Provability
