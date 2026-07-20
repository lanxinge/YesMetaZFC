import YesMetaZFC.Logic.Syntax

/-!
# 一阶逻辑原始记号

这一层面向 checker、soundness 与调试代码。所有记号都直接展开为 locally nameless
构造子，不引入具名变量环境或额外语法对象。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

namespace Raw

/-- 原始 bound 变量项。 -/
def bound {σ : Signature} (sort : σ.SortSymbol) (index : Nat) : Term σ :=
  .var (.bvar sort index)

/-- 原始 free 变量项。 -/
def free {σ : Signature} (sort : σ.SortSymbol) (id : FreeVarId) : Term σ :=
  .var (.fvar sort id)

scoped notation:max "#ᵇ[" sort ", " index "]" =>
  Raw.bound sort index

scoped notation:max "#ᶠ[" sort ", " id "]" =>
  Raw.free sort id

scoped syntax:max "𝒇₁[" term "](" term,* ")" : term

scoped macro_rules
  | `(𝒇₁[$function]($arguments,*)) =>
      `(FirstOrder.Term.app $function [$arguments,*])

scoped syntax:max "ℛ₁[" term "](" term,* ")" : term

scoped macro_rules
  | `(ℛ₁[$relation]($arguments,*)) =>
      `(FirstOrder.Formula.rel $relation [$arguments,*])

scoped notation "⊥₁" => FirstOrder.Formula.falsum
scoped notation "⊤₁" => FirstOrder.Formula.truth
scoped prefix:40 "¬₁ " => FirstOrder.Formula.neg
scoped infixr:35 " ∧₁ " => FirstOrder.Formula.conj
scoped infixr:30 " ∨₁ " => FirstOrder.Formula.disj
scoped infixr:25 " →₁ " => FirstOrder.Formula.imp
scoped infix:20 " ↔₁ " => FirstOrder.Formula.iff
scoped infix:50 " ≐ " => FirstOrder.Formula.equal

scoped notation:10 "∀₁[" sort "], " body =>
  FirstOrder.Formula.forallE sort body

scoped notation:10 "∃₁[" sort "], " body =>
  FirstOrder.Formula.existsE sort body

end Raw
end FirstOrder
end Logic
end YesMetaZFC
