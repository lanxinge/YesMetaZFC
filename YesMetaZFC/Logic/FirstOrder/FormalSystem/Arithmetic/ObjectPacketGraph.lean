import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectPacketData

/-! # 版本一传输包到对象树码的固定规则图 -/
namespace YesMetaZFC.Automation.ObjectPacket
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding NatPacket IntrinsicQuotation
open ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def node {n : Nat} (tag : Nat) (fields : List (Expr n)) : Expr n := .node (.literal tag) fields
def rawNode {n : Nat} (tag fields : Expr n) : Expr n := .succ (.pair tag fields)
def cons {n : Nat} (head tail : Expr n) : Expr n := .succ (.pair (.literal 1) (.pair head tail))

def affineBase (relation radix : Nat) : Rule where
  arity := 1
  head := node relation [.var 0, .literal 0, .var 0]
  guards := [(.var 0, .literal radix)]
  premises := []

def affineStep (relation radix : Nat) : Rule where
  arity := 3
  head := node relation [.var 0, .succ (.var 1), Expr.addConst radix (.var 2)]
  guards := []
  premises := [node relation [.var 0, .var 1, .var 2]]

def tokenSmall : Rule where
  arity := 3
  head := node 2 [.var 0, .var 1, .var 2]
  guards := [(.var 0, .literal 128)]
  premises := [node 1 [.var 0, .var 1, .var 2]]

def tokenLarge : Rule where
  arity := 6
  head := node 2 [.var 0, .var 1, .var 2]
  guards := [(.literal 0, .var 4), (.var 3, .literal 128)]
  premises := [node 0 [.var 3, .var 4, .var 0] ,
    node 2 [.var 4, .var 1, .var 5] , node 1 [Expr.addConst 128 (.var 3), .var 5, .var 2]]

def treeRule : Rule where
  arity := 7
  head := node 3 [rawNode (.var 0) (.var 1), .var 2, .var 3]
  guards := []
  premises := [node 4 [.var 1, .var 4, .var 2, .var 5] ,
    node 2 [.var 4, .var 5, .var 6] , node 2 [.var 0, .var 6, .var 3]]

def forestNil : Rule where
  arity := 1
  head := node 4 [Expr.list [] , .literal 0, .var 0, .var 0]
  guards := []
  premises := []

def forestCons : Rule where
  arity := 6
  head := node 4 [cons (.var 0) (.var 1), .succ (.var 2), .var 3, .var 4]
  guards := []
  premises := [node 4 [.var 1, .var 2, .var 3, .var 5] , node 3 [.var 0, .var 5, .var 4]]

def packetRule : Rule where
  arity := 3
  head := node 5 [.var 1, .var 0]
  guards := []
  premises := [node 1 [.literal 1, .var 2, .var 1] , node 3 [.var 0, .literal 1, .var 2]]

def rules : List Rule :=
  [affineBase 0 128, affineStep 0 128, affineBase 1 256, affineStep 1 256,
    tokenSmall, tokenLarge, treeRule, forestNil, forestCons, packetRule]

theorem heads_tagged : ∀ rule, rule ∈ rules → rule.head.tag?.isSome := by
  intro rule h
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

@[simp] theorem rulesFor_zero : rulesFor rules 0 = [affineBase 0 128, affineStep 0 128] := rfl
@[simp] theorem rulesFor_one : rulesFor rules 1 = [affineBase 1 256, affineStep 1 256] := rfl
@[simp] theorem rulesFor_two : rulesFor rules 2 = [tokenSmall, tokenLarge] := rfl
@[simp] theorem rulesFor_three : rulesFor rules 3 = [treeRule] := rfl
@[simp] theorem rulesFor_four : rulesFor rules 4 = [forestNil, forestCons] := rfl
@[simp] theorem rulesFor_five : rulesFor rules 5 = [packetRule] := rfl

def condition {bound free : SetContext} (packet treeCode : SetTerm bound free) : SetFormula bound free :=
  ObjectHorn.condition rules (IntrinsicQuotation.node 5 [packet, treeCode])

theorem condition_delta0 {bound free : SetContext} (packet treeCode : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition packet treeCode) := ObjectHorn.condition_delta0 _ _

end YesMetaZFC.Automation.ObjectPacket
