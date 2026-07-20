import YesMetaZFC.Logic.Syntax

/-!
# 一阶逻辑数学 DSL 文法

本文件只声明语法类别，不执行 locally nameless 编译。关系 mixfix 模板可以在这些
类别上安全扩展，而不会污染 Lean 的普通 `term` 文法。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Surface

declare_syntax_cat foTerm
declare_syntax_cat foFormula

syntax ident : foTerm
syntax:max "(" foTerm ")" : foTerm
syntax:max "#ᶠ[" term ", " num "]" : foTerm
syntax:max "⌜" term "⌝ₜ" : foTerm
syntax:max "𝒇[" term "](" foTerm,* ")" : foTerm
syntax:max ident "(" foTerm,* ")" : foTerm

syntax:max "⊥" : foFormula
syntax:max "⊤" : foFormula
syntax:max "⌜" term "⌝ₚ" : foFormula
syntax:max "(" foFormula ")" : foFormula
syntax:max "ℛ[" term "](" foTerm,* ")" : foFormula
syntax:50 foTerm:51 " = " foTerm:51 : foFormula
syntax:40 "¬ " foFormula:40 : foFormula
syntax:35 foFormula:36 " ∧ " foFormula:35 : foFormula
syntax:30 foFormula:31 " ∨ " foFormula:30 : foFormula
syntax:25 foFormula:26 " → " foFormula:25 : foFormula
syntax:20 foFormula:21 " ↔ " foFormula:21 : foFormula
syntax:10 "∀ " ident+ " : " term ", " foFormula:10 : foFormula
syntax:10 "∃ " ident+ " : " term ", " foFormula:10 : foFormula

/-- 把数学 DSL 编译成普通的一阶 locally nameless 公式。 -/
syntax:max "fo[" term "]" " ⟪" foFormula "⟫" : term

end Surface
end FirstOrder
end Logic
end YesMetaZFC
