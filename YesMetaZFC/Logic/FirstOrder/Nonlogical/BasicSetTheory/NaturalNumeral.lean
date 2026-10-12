import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.FiniteOrdinal
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Successor

/-!
# 有限自然数成员

本模块承载有限 numeral 的对象语言成员关系。它只依赖后继算子理论，
不把 `ω` 或自然算术编码理论提前下沉到有限序数基础层。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 有限自然数成员 -/

theorem finite_numeral_mem_of_lt
    {free : SetContext} {Γ : Context signature free}
    {left right : Nat} (hLt : left < right) :
    Γ ⊢ₘ[successor_operator_theory]
      (numₘ(left) : SetOpenTerm free) ∈ₘ numₘ(right) := by
  induction right with
  | zero =>
      exfalso
      omega
  | succ right ih =>
      by_cases hEq : left = right
      · subst left
        simpa [finite_numeral_term] using
          (mem_successor_self
            (Γ := Γ) (numₘ(right) : SetOpenTerm free))
      · have hPrev : left < right := by omega
        have hMember := ih hPrev
        have hStep := FirstOrder.Derives.imp_elim
          (mem_successor_of_mem
            (Γ := Γ)
            (numₘ(right) : SetOpenTerm free)
            (numₘ(left) : SetOpenTerm free))
          hMember
        simpa [finite_numeral_term] using hStep

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
