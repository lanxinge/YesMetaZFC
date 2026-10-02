import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHorn
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaRenameInstances

/-!
# 正文识别与重命名的统一对象规则图

规则表是固定的有限数据。正文识别使用项行与公式行；重命名另使用表查找、
量词深度下的索引映射以及整表合法性行。量词只增加 cutoff，不复制或预先计算提升表。
本模块给出实际统一公式和 Delta0 分类；正负推导见 SchemaBodyDerives 和 SchemaRenameDerives。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph
open Nonlogical.BasicSetTheory QuineEncoding
open _root_.YesMetaZFC.Automation ObjectHorn
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def node {n : Nat} (tag : Nat) (fields : List (Expr n)) : Expr n :=
  .node (.literal tag) fields

def boundVar {n : Nat} (index : Expr n) : Expr n := node 0 [.node index []]

namespace Body
def termRule : Rule where
  arity := 2
  head := node 0 [.var 0, boundVar (.var 1)]
  guards := [(.var 1, .var 0)]

def constantRule (tag : Nat) : Rule where
  arity := 1
  head := node 1 [.var 0, node tag []]

def atomRule (tag : Nat) : Rule where
  arity := 3
  head := node 1 [.var 0, node tag [.var 1, .var 2]]
  premises := [node 0 [.var 0, .var 1] , node 0 [.var 0, .var 2]]

def unaryRule (tag : Nat) (binder : Bool) : Rule where
  arity := 2
  head := node 1 [.var 0, node tag [.var 1]]
  premises := [node 1 [if binder then .succ (.var 0) else .var 0, .var 1]]

def binaryRule (tag : Nat) : Rule where
  arity := 3
  head := node 1 [.var 0, node tag [.var 1, .var 2]]
  premises := [node 1 [.var 0, .var 1] , node 1 [.var 0, .var 2]]

def rules : List Rule :=
  [termRule, constantRule 0, constantRule 1, atomRule 2, atomRule 3,
    unaryRule 4 false, binaryRule 5, binaryRule 6, binaryRule 7, binaryRule 8,
    unaryRule 9 true, unaryRule 10 true, atomRule 11]

def condition {bound free : SetContext} (depth input : SetTerm bound free) : SetFormula bound free :=
  ObjectHorn.condition rules (IntrinsicQuotation.node 1 [depth, input])

theorem condition_delta0 {bound free : SetContext} (depth input : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition depth input) :=
  ObjectHorn.condition_delta0 _ _
end Body

namespace Rename
def lookupZero : Rule where
  arity := 2
  head := node 0 [.succ (.pair (.literal 1) (.pair (.var 0) (.var 1))), .literal 0, .var 0]

def lookupSucc : Rule where
  arity := 4
  head := node 0 [.succ (.pair (.literal 1) (.pair (.var 0) (.var 1))), .succ (.var 2), .var 3]
  premises := [node 0 [.var 1, .var 2, .var 3]]

def indexBase : Rule where
  arity := 3
  head := node 1 [.var 0, .literal 0, .var 1, .var 2]
  premises := [node 0 [.var 0, .var 1, .var 2]]

def indexZero : Rule where
  arity := 2
  head := node 1 [.var 0, .succ (.var 1), .literal 0, .literal 0]

def indexSucc : Rule where
  arity := 4
  head := node 1 [.var 0, .succ (.var 1), .succ (.var 2), .succ (.var 3)]
  premises := [node 1 [.var 0, .var 1, .var 2, .var 3]]

def termRule : Rule where
  arity := 4
  head := node 3 [.var 0, .var 1, boundVar (.var 2), boundVar (.var 3)]
  premises := [node 1 [.var 0, .var 1, .var 2, .var 3]]

def constantRule (tag : Nat) : Rule where
  arity := 2
  head := node 2 [.var 0, .var 1, node tag [] , node tag []]

def unaryRule (tag : Nat) (binder : Bool) : Rule where
  arity := 4
  head := node 2 [.var 0, .var 1, node tag [.var 2] , node tag [.var 3]]
  premises := [node 2 [.var 0, if binder then .succ (.var 1) else .var 1, .var 2, .var 3]]

def binaryRule (tag premiseTag : Nat) : Rule where
  arity := 6
  head := node 2 [.var 0, .var 1, node tag [.var 2, .var 3] , node tag [.var 4, .var 5]]
  premises := [node premiseTag [.var 0, .var 1, .var 2, .var 4] ,
    node premiseTag [.var 0, .var 1, .var 3, .var 5]]

def validNil : Rule where
  arity := 1
  head := node 4 [.var 0, .list []]

def validCons : Rule where
  arity := 3
  head := node 4 [.var 0, .succ (.pair (.literal 1) (.pair (.var 1) (.var 2)))]
  guards := [(.var 1, .var 0)]
  premises := [node 4 [.var 0, .var 2]]

def runRule : Rule where
  arity := 4
  head := node 5 [.var 0, .var 1, .var 2, .var 3]
  premises := [node 4 [.var 0, .var 1] , node 2 [.var 1, .literal 0, .var 2, .var 3]]

def rules : List Rule :=
  [lookupZero, lookupSucc, indexBase, indexZero, indexSucc, termRule,
    constantRule 0, constantRule 1, binaryRule 2 3, binaryRule 3 3, unaryRule 4 false,
    binaryRule 5 2, binaryRule 6 2, binaryRule 7 2, binaryRule 8 2,
    unaryRule 9 true, unaryRule 10 true, binaryRule 11 3, validNil, validCons, runRule]

def condition {bound free : SetContext} (target table input output : SetTerm bound free) :
    SetFormula bound free :=
  ObjectHorn.condition rules (IntrinsicQuotation.node 5 [target, table, input, output])

theorem condition_delta0 {bound free : SetContext} (target table input output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition target table input output) :=
  ObjectHorn.condition_delta0 _ _
end Rename

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph
