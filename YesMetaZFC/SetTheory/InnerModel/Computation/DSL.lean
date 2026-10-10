import Lean
import YesMetaZFC.SetTheory.InnerModel.Computation.Boolean

/-! # 集合程序的 C 风格前端

`setfn! (x, y) { set d = x - y; return x - d; }` 编译为带有限寄存器的程序。
`union_for (z : x) { return e; }` 对模型内部集合 x 并合各次返回值，不枚举外部序列。
局部变量按词法作用域压栈；无界循环和隐式真值测试不属于此基础语言。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Lean

declare_syntax_cat cp_expr
declare_syntax_cat cp_block
syntax ident : cp_expr
syntax "{}" : cp_expr
syntax:max "(" cp_expr ")" : cp_expr
syntax:max ident "(" cp_expr,* ")" : cp_expr
syntax:65 cp_expr:65 " - " cp_expr:66 : cp_expr
syntax:60 cp_expr:60 " & " cp_expr:61 : cp_expr
syntax:55 cp_expr:55 " | " cp_expr:56 : cp_expr
syntax:max "union_for" "(" ident " : " cp_expr ")" "{" cp_block "}" : cp_expr
syntax "return " cp_expr ";" : cp_block
syntax "set " ident " = " cp_expr ";" cp_block : cp_block
syntax:max "setfn!" "(" ident,* ")" "{" cp_block "}" : term

/-- 原语菜单固定到已验证的 Rd 运算；参数数目在展开时检查。 -/
private def cp_call_expand_l (f : TSyntax `ident) (a : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  match f.getId.toString, a.toList with
  | "pair", [p, q] => `(cp_pair_l $p $q)
  | "diff", [p, q] => `(cp_diff_l $p $q)
  | "union", [p] => `(Cp_code.op .union $p .zero .zero)
  | "range", [p] => `(Cp_code.op .range $p .zero .zero)
  | "memrel", [p] => `(Cp_code.op .mem $p .zero .zero)
  | "prod", [p, q] => `(Cp_code.op .prod $p $q .zero)
  | "mid", [p, q] => `(Cp_code.op .mid $p $q .zero)
  | "last", [p, q] => `(Cp_code.op .last $p $q .zero)
  | "fibers", [p, q] => `(Cp_code.op .fibers $p $q .zero)
  | "opair", [p, q] => `(Cp_code.op .opair $p $q .zero)
  | "triple", [p, q, r] => `(Cp_code.op .triple $p $q $r)
  | "adj", [p, q, r] => `(Cp_code.op .adj $p $q $r)
  | "fiber", [p, q] => `(Cp_code.op .fiber $p $q .zero)
  | "has", [p, q] => `(cp_member_l $p $q)
  | "subset", [p, q] => `(cp_subset_l $p $q)
  | "equal", [p, q] => `(cp_equal_l $p $q)
  | "not", [p] => `(cp_not_l $p)
  | "and", [p, q] => `(cp_and_l $p $q)
  | "or", [p, q] => `(cp_or_l $p $q)
  | _, _ => Macro.throwErrorAt f s!"未知集合原语或参数数目错误：{f.getId}（{a.size} 个参数）"

mutual
private partial def cp_expr_expand_l (e : List Name) (s : TSyntax `cp_expr) : MacroM (TSyntax `term) := do
  match s with
  | `(cp_expr| $x:ident) =>
    match e.idxOf? x.getId with
    | some i => `(Cp_code.var ⟨$(quote i), by decide⟩)
    | none => Macro.throwErrorAt x s!"未绑定的集合变量：{x.getId}"
  | `(cp_expr| {}) => `(Cp_code.zero)
  | `(cp_expr| ($p)) => cp_expr_expand_l e p
  | `(cp_expr| $f:ident($a,*)) => cp_call_expand_l f (← a.getElems.mapM (cp_expr_expand_l e))
  | `(cp_expr| $p - $q) => `(cp_diff_l $(← cp_expr_expand_l e p) $(← cp_expr_expand_l e q))
  | `(cp_expr| $p & $q) => `(cp_and_l $(← cp_expr_expand_l e p) $(← cp_expr_expand_l e q))
  | `(cp_expr| $p | $q) =>
    `(Cp_code.op .union (cp_pair_l $(← cp_expr_expand_l e p) $(← cp_expr_expand_l e q)) .zero .zero)
  | `(cp_expr| union_for ($x:ident : $p) { $b:cp_block }) =>
    `(Cp_code.bunion $(← cp_expr_expand_l e p) $(← cp_block_expand_l (x.getId :: e) b))
  | _ => Macro.throwErrorAt s "不支持的集合表达式"

private partial def cp_block_expand_l (e : List Name) (s : TSyntax `cp_block) : MacroM (TSyntax `term) := do
  match s with
  | `(cp_block| return $p;) => cp_expr_expand_l e p
  | `(cp_block| set $x:ident = $p; $b:cp_block) =>
    `(Cp_code.let1 $(← cp_expr_expand_l e p) $(← cp_block_expand_l (x.getId :: e) b))
  | _ => Macro.throwErrorAt s "集合程序块必须以 return 结束"
end

macro_rules
  | `(setfn! ($xs:ident,*) { $b:cp_block }) => do
    let e := xs.getElems.toList.map (·.getId)
    unless e.eraseDups.length == e.length do
      Macro.throwErrorAt b "集合函数的形参不能重名"
    `(show Cp_code $(quote e.length) from $(← cp_block_expand_l e b))

end YesMetaZFC.SetTheory.InnerModel
