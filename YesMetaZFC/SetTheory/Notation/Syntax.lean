import Lean.Parser

/-!
# 项目集合论纸面语法

文法独立于 Lean 普通 `term`，避免全局污染。集合论公式使用无类型一元变量；
`=`、`≠`、`⊆`、`⊊` 和有界量词由 elaborator 编译为 Project 公式。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Surface

declare_syntax_cat setTerm
declare_syntax_cat setFormula

syntax ident : setTerm
syntax:max "(" setTerm ")" : setTerm
syntax:max "#ᶠ[" num "]" : setTerm
syntax:max "⌜" term "⌝ₛ" : setTerm

syntax:max "⊥" : setFormula
syntax:max "⊤" : setFormula
syntax:max "⌜" term "⌝ₚ" : setFormula
syntax:max "(" setFormula ")" : setFormula
syntax:55 setTerm:56 " ∈ " "⋃" setTerm:56 : setFormula
syntax:55 setTerm:56 " ∈ " "𝒫" "(" setTerm ")" : setFormula
syntax:55 setTerm:56 " ∈ " "(" setTerm " ∩ " setTerm ")" : setFormula
syntax:55 setTerm:56 " ∈ " "(" setTerm " ∖ " setTerm ")" : setFormula
syntax:55 "⟨" setTerm "," setTerm "⟩" " ∈ " setTerm:56 : setFormula
syntax:55 "⟨" setTerm "," setTerm "⟩" "[" term "]" " ∈ " setTerm:56 : setFormula
syntax:max "Rel" "(" setTerm ")" : setFormula
syntax:max "Rel" "[" term "]" "(" setTerm ")" : setFormula
syntax:max "Fun" "(" setTerm ")" : setFormula
syntax:max "Fun" "[" term "]" "(" setTerm ")" : setFormula
syntax:50 setTerm:51 " : " setTerm:51 " ⟶ " setTerm:51 : setFormula
syntax:50 setTerm:51 " :" "[" term "]" setTerm:51 " ⟶ " setTerm:51 : setFormula
syntax:max "Inj" "(" setTerm ")" : setFormula
syntax:max "Inj" "[" term "]" "(" setTerm ")" : setFormula
syntax:55 setTerm:56 " ∈ " setTerm:56 : setFormula
syntax:55 setTerm:56 " ∉ " setTerm:56 : setFormula
syntax:50 setTerm:51 " = " setTerm:51 : setFormula
syntax:50 setTerm:51 " ≠ " setTerm:51 : setFormula
syntax:50 setTerm:51 " ⊆ " setTerm:51 : setFormula
syntax:50 setTerm:51 " ⊊ " setTerm:51 : setFormula
syntax:40 "¬ " setFormula:40 : setFormula
syntax:35 setFormula:36 " ∧ " setFormula:35 : setFormula
syntax:30 setFormula:31 " ∨ " setFormula:30 : setFormula
syntax:25 setFormula:26 " → " setFormula : setFormula
syntax:20 setFormula:21 " ↔ " setFormula : setFormula
syntax:10 "∀ " ident+ ", " setFormula:10 : setFormula
syntax:10 "∃ " ident+ ", " setFormula:10 : setFormula
syntax:10 "∀ " ident " ∈ " setTerm ", " setFormula:10 : setFormula
syntax:10 "∃ " ident " ∈ " setTerm ", " setFormula:10 : setFormula

/-- 构造指定 de Bruijn 深度的纯集合论公式。 -/
syntax:max "set[" term "]" " ⟪" setFormula "⟫" : term

/-- 构造深度为零的纯集合论公式。 -/
syntax:max "set!" " ⟪" setFormula "⟫" : term

/-- 构造没有 free 变量的纯集合论句子。 -/
syntax:max "sentence!" " ⟪" setFormula "⟫" : term

/-- 构造指定深度的 Jech 风格可定义类 `{x | φ}`。 -/
syntax:max "class[" term "]" " ⟪" ident " | " setFormula "⟫" : term

/-- 构造没有外层 bound 参数的可定义类。 -/
syntax:max "class!" " ⟪" ident " | " setFormula "⟫" : term

end Surface
end SetTheory
end YesMetaZFC
