import YesMetaZFC.Model.ZFC.Pure.PureOpenTransfer
import YesMetaZFC.Automation.ObjectExpressionIteration

/-! # 纯隶属公式自身的完整 AST 编码

结构嵌入逐节点保留变量、原子、联结词和量词，不插入消元见证。
因此使用当前完整 AST quotation 的相同标签，而非源翻译公式或旧 Hilbert 编码。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureQuotation
open Nonlogical.BasicSetTheory PureOpenTransfer
open _root_.YesMetaZFC.Automation IntrinsicQuotation ObjectHorn NatPacket
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature PureCompletedStage.interpretation

theorem variable_index_m {parameters : SetContext} {s : _root_.YesMetaZFC.SetTheory.SetSort}
    (v : Variable (pureContext_m parameters) s) : (sourceVariable_m v).index = v.index := by
  induction parameters with
  | nil => cases v
  | cons sort parameters ih =>
    cases sort
    cases v with
    | here => rfl
    | there v => exact congrArg Nat.succ (ih v)

def term_m {bound free : SetContext} {s : _root_.YesMetaZFC.SetTheory.SetSort} :
    Term ℒ (pureContext_m bound) (pureContext_m free) s → SetTerm bound free
  | .bvar v => .bvar (sourceVariable_m v)
  | .fvar v => .fvar (sourceVariable_m v)
  | .app f _ => nomatch f

def formula_m {bound free : SetContext} :
    Formula ℒ (pureContext_m bound) (pureContext_m free) → SetFormula bound free
  | .falsum => .falsum
  | .truth => .truth
  | .rel .membership (.cons a (.cons b .nil)) =>
      .rel .membership (.cons (term_m a) (.cons (term_m b) .nil))
  | .equal a b => .equal (term_m a) (term_m b)
  | .neg p => .neg (formula_m p)
  | .conj p q => .conj (formula_m p) (formula_m q)
  | .disj p q => .disj (formula_m p) (formula_m q)
  | .imp p q => .imp (formula_m p) (formula_m q)
  | .iff p q => .iff (formula_m p) (formula_m q)
  | .forallE .set p => .forallE SetSort.set (formula_m p)
  | .existsE .set p => .existsE SetSort.set (formula_m p)

def termTree_m {bound free : SortContext ℒ} {s : _root_.YesMetaZFC.SetTheory.SetSort} :
    Term ℒ bound free s → Tree
  | .bvar v => .node 0 [leaf v.index]
  | .fvar v => .node 1 [leaf v.index]
  | .app f _ => nomatch f

def argumentsTree_m {bound free : SortContext ℒ} :
    {sorts : SortContext ℒ} → Arguments ℒ bound free sorts → List Tree
  | _, .nil => []
  | _, .cons a rest => termTree_m a :: argumentsTree_m rest

def tree_m {bound free : SortContext ℒ} : Formula ℒ bound free → Tree
  | .falsum => leaf 0
  | .truth => leaf 1
  | .rel _ args => .node 2 (leaf 0 :: argumentsTree_m args)
  | .equal a b => .node 3 [termTree_m a, termTree_m b]
  | .neg p => .node 4 [tree_m p]
  | .conj p q => .node 5 [tree_m p, tree_m q]
  | .disj p q => .node 6 [tree_m p, tree_m q]
  | .imp p q => .node 7 [tree_m p, tree_m q]
  | .iff p q => .node 8 [tree_m p, tree_m q]
  | .forallE _ p => .node 9 [tree_m p]
  | .existsE _ p => .node 10 [tree_m p]

def code_m {bound free : SetContext}
    (φ : Formula ℒ (pureContext_m bound) (pureContext_m free)) : Nat := treeValue (tree_m φ)

abbrev mem_m {bound free : SortContext ℒ} (a b : Term ℒ bound free PureModel.setSort) :
    Formula ℒ bound free := .rel .membership (.cons a (.cons b .nil))

/-- 输入 y 和输出 x 位于两个最内绑定槽；尾部上下文完全不出现。 -/
def successor_m {bound free : SetContext} :
    Formula ℒ (pureContext_m (SetSort.set :: SetSort.set :: bound)) (pureContext_m free) :=
  .forallE PureModel.setSort
    (.iff (mem_m (.bvar .here) (.bvar (.there (.there .here))))
      (.disj (mem_m (.bvar .here) (.bvar (.there .here)))
        (.equal (.bvar .here) (.bvar (.there .here)))))

/-- Nₙ(x) 仅以等号、隶属与量词定义标准有限 von Neumann 数码。 -/
def numeral_m {bound free : SetContext} : Nat →
    Formula ℒ (pureContext_m (SetSort.set :: bound)) (pureContext_m free)
  | 0 => .forallE PureModel.setSort (.neg (mem_m (.bvar .here) (.bvar (.there .here))))
  | n + 1 => .existsE PureModel.setSort (.conj (numeral_m n) successor_m)

def zeroCode_m : Nat := code_m (numeral_m (bound := []) (free := []) 0)
def successorCode_m : Nat := code_m (successor_m (bound := []) (free := []))
def numeralStep_m : Expr 2 :=
  .node (.literal 10) [.node (.literal 5) [.var 1, .literal successorCode_m]]
def numeralCode_m := ObjectExpressionIteration.value_m zeroCode_m numeralStep_m

theorem numeralStep_variable_m : 1 ∈ numeralStep_m.variables := by decide

theorem numeral_code_m {bound free : SetContext} (n : Nat) :
    code_m (numeral_m (bound := bound) (free := free) n) = numeralCode_m n := by
  induction n generalizing bound with
  | zero => rfl
  | succ n ih =>
    simp only [numeral_m, code_m, tree_m, treeValue_node, List.map_cons, List.map_nil]
    rw [show treeValue (tree_m (numeral_m (bound := SetSort.set :: bound) (free := free) n)) = numeralCode_m n from ih]
    rfl

/-- 把绑定正文的首槽用纯数码公式封闭；正文 AST 本身原样保留。 -/
def specialize_m {free : SetContext}
    (body : Formula ℒ (pureContext_m [SetSort.set]) (pureContext_m free)) (n : Nat) :
    OpenFormula ℒ (pureContext_m free) :=
  .existsE PureModel.setSort (.conj (numeral_m (bound := []) (free := free) n) body)

def diagonalValue_m (n : Nat) := nodeValue 10 [nodeValue 5 [numeralCode_m n, n]]

theorem specialize_code_m {free : SetContext}
    (body : Formula ℒ (pureContext_m [SetSort.set]) (pureContext_m free)) (n : Nat) :
    code_m (bound := []) (free := free) (specialize_m body n) = nodeValue 10 [nodeValue 5 [numeralCode_m n, code_m body]] := by
  simp only [specialize_m, code_m, tree_m,
    treeValue_node, List.map_cons, List.map_nil]
  rw [show treeValue (tree_m (numeral_m (bound := []) (free := free) n)) = numeralCode_m n
    from numeral_code_m n]

/-- 真正的自编码恒等式：右侧编码的就是最终生成的纯公式。 -/
theorem self_code_m {free : SetContext}
    (body : Formula ℒ (pureContext_m [SetSort.set]) (pureContext_m free)) :
    code_m (bound := []) (free := free) (specialize_m body (code_m body)) = diagonalValue_m (code_m body) :=
  specialize_code_m body (code_m body)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureQuotation
