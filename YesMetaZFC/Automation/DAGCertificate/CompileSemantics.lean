import YesMetaZFC.Automation.DAGCertificate.Compile
import YesMetaZFC.Model.FirstOrder.SubstitutionSemantics

/-!
# 检查编译的内在语义接口

本层只证明编译结果的通用语义性质，不参与原始语法计算。最核心的接口是：逐层把
free 上下文量化为闭句，恰好等价于原开公式在全部 typed assignment 下成立。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace Compile

open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder

universe x

/-- 用一个 typed free assignment 解释无外层 bound 变量的开公式。 -/
def openEnv {σ : Signature} {M : Structure.{0, 0, 0, x} σ}
    {free : SortContext σ} (assignment : Assignment M free) :
    Env M [] free where
  boundVal := Assignment.empty
  freeVal := assignment

/-- 开公式对全部 typed free assignment 成立。 -/
def UniversallyValid {σ : Signature} (M : Structure.{0, 0, 0, x} σ)
    {free : SortContext σ} (formula : OpenFormula σ free) : Prop :=
  ∀ assignment : Assignment M free,
    Formula.satisfies (openEnv assignment) formula

/-- `forallFree` 逐层关闭 free 上下文的直接语义。 -/
theorem forallFree_trueIn_iff {σ : Signature}
    {M : Structure.{0, 0, 0, x} σ}
    {free : SortContext σ} (formula : OpenFormula σ free) :
    (forallFree formula).TrueIn M ↔ UniversallyValid M formula := by
  induction free with
  | nil =>
      constructor
      · intro h assignment
        have hEnv :
            openEnv assignment = (Env.empty : Env M [] []) := by
          apply Env.ext
          · intro sort entry
            cases entry
          · intro sort entry
            cases entry
        rw [hEnv]
        exact h
      · intro h
        simpa only [Formula.TrueIn, forallFree] using!
          h (@Assignment.empty σ M)
  | cons sort rest ih =>
      change
        (forallFree (formula.forallFreeTop sort)).TrueIn M ↔
          UniversallyValid M formula
      rw [ih]
      constructor
      · intro h assignment
        let tail : Assignment M rest :=
          fun entry => assignment (.there entry)
        have hAll :=
          (Formula.satisfies_forallFreeTop
            (openEnv tail) formula).mp (h tail)
        have hHead := hAll
          (assignment (.here : Logic.FirstOrder.Variable (sort :: rest) sort))
        have hEnv :
            (openEnv tail).pushFree
                (assignment
                  (.here : Logic.FirstOrder.Variable (sort :: rest) sort)) =
              openEnv assignment := by
          apply Env.ext
          · intro boundSort entry
            cases entry
          · intro freeSort entry
            cases entry with
            | here => rfl
            | there previous => rfl
        rw [← hEnv]
        exact hHead
      · intro h tail
        apply (Formula.satisfies_forallFreeTop
          (openEnv tail) formula).mpr
        intro value
        exact h (Assignment.push value tail)

end Compile
end DAGCertificate
end Automation
end YesMetaZFC
