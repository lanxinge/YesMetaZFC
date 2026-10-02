import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxSubstitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCodeProjection

/-! # 局部证明规则共用的数值语法变换

模式 0 加强自由上下文；1 抽象最新自由变量；2 实例化最新束缚变量；
3 使用有限表同时代入自由变量。depth 记录已经穿过的量词数。
本层计算原始结构码，不以对象公式真值定义计算结果。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxTransform
open Nonlogical.BasicSetTheory NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn ObjectCodeProjection
set_option autoImplicit false

/-- 有限数值表的精确查找；非法列表外壳和越界均失败。 -/
def lookup (table index : Nat) : Option Nat :=
  if table = ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value (head table) (tail table)) + 1 then
    match index with
    | 0 => some (head table)
    | i + 1 => if _h : tail table < table then lookup (tail table) i else none
  else none
termination_by table

@[simp] theorem lookup_cons_zero (first rest : Nat) :
    lookup (ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value first rest) + 1) 0 = some first := by
  rw [lookup.eq_def]
  simp [head, tail, payload, ProofCode.godel_unpair_value_pair]

@[simp] theorem lookup_cons_succ (first rest index : Nat) :
    lookup (ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value first rest) + 1) (index + 1) =
      lookup rest index := by
  rw [lookup.eq_def]
  simp only [head, tail, payload, Nat.add_sub_cancel, ProofCode.godel_unpair_value_pair, if_true]
  exact dif_pos (tail_lt_cons first rest)

@[simp] theorem lookup_list (values : List Nat) (index : Nat) :
    lookup (listValue values) index = values[index]? := by
  induction values generalizing index with
  | nil =>
    have hShape : listValue [] ≠ ProofCode.godel_pair_value 1
        (ProofCode.godel_pair_value (head (listValue [])) (tail (listValue []))) + 1 := by decide
    rw [lookup.eq_def, if_neg hShape]
    simp
  | cons first rest ih =>
    have hShape : listValue (first :: rest) = ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value (head (listValue (first :: rest))) (tail (listValue (first :: rest)))) + 1 := by
      simp only [head_cons, tail_cons]
      rfl
    rw [lookup.eq_def, if_pos hShape]
    cases index with
    | zero => simp
    | succ index =>
      dsimp only
      have hLt : tail (listValue (first :: rest)) < listValue (first :: rest) := by
        rw [tail_cons]
        exact tail_lt_cons first (listValue rest)
      rw [dif_pos hLt, tail_cons, ih]
      rfl

/-- 束缚变量转换；点代入的参数为替换项的数值码。 -/
def boundValue (mode depth parameter index : Nat) : Option Nat :=
  match mode with
  | 0 | 3 => some (treeValue (SyntaxSubstitution.bvar index))
  | 1 => some (treeValue (SyntaxSubstitution.bvar (if index < depth then index else index + 1)))
  | 2 => if index < depth then some (treeValue (SyntaxSubstitution.bvar index))
      else if index = depth then some parameter
      else some (treeValue (SyntaxSubstitution.bvar (index - 1)))
  | _ => none

/-- 自由变量转换；同时代入的参数为项码列表的数值码。 -/
def freeValue (mode depth parameter index : Nat) : Option Nat :=
  match mode with
  | 0 => some (treeValue (SyntaxSubstitution.fvar (index + 1)))
  | 1 => match index with
      | 0 => some (treeValue (SyntaxSubstitution.bvar depth))
      | i + 1 => some (treeValue (SyntaxSubstitution.fvar i))
  | 2 => some (treeValue (SyntaxSubstitution.fvar index))
  | 3 => lookup parameter index
  | _ => none

mutual
def term (mode depth parameter : Nat) : Tree → Option Nat
  | .node 0 [.node index []] => boundValue mode depth parameter index
  | .node 1 [.node index []] => freeValue mode depth parameter index
  | .node 2 (.node symbol [] :: args) => do
      let result ← arguments mode depth parameter args
      return ProofCode.godel_pair_value 2
        (ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value (nodeValue symbol []) result) + 1) + 1
  | _ => none

def arguments (mode depth parameter : Nat) : List Tree → Option Nat
  | [] => if mode < 4 then some (listValue []) else none
  | head :: tail => do
      let first ← term mode depth parameter head
      let rest ← arguments mode depth parameter tail
      return ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value first rest) + 1
end

def formula (mode depth parameter : Nat) : Tree → Option Nat
  | .node 0 [] => if mode < 4 then some (nodeValue 0 []) else none
  | .node 1 [] => if mode < 4 then some (nodeValue 1 []) else none
  | .node 2 (.node symbol [] :: args) => do
      let result ← arguments mode depth parameter args
      return ProofCode.godel_pair_value 2
        (ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value (nodeValue symbol []) result) + 1) + 1
  | .node 3 [left, right] => do
      return nodeValue 3 [← term mode depth parameter left, ← term mode depth parameter right]
  | .node 4 [body] => do return nodeValue 4 [← formula mode depth parameter body]
  | .node 5 [left, right] => do
      return nodeValue 5 [← formula mode depth parameter left, ← formula mode depth parameter right]
  | .node 6 [left, right] => do
      return nodeValue 6 [← formula mode depth parameter left, ← formula mode depth parameter right]
  | .node 7 [left, right] => do
      return nodeValue 7 [← formula mode depth parameter left, ← formula mode depth parameter right]
  | .node 8 [left, right] => do
      return nodeValue 8 [← formula mode depth parameter left, ← formula mode depth parameter right]
  | .node 9 [body] => do return nodeValue 9 [← formula mode (depth + 1) parameter body]
  | .node 10 [body] => do return nodeValue 10 [← formula mode (depth + 1) parameter body]
  | _ => none

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxTransform
