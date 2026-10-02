import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCodeBounds

/-! # 结构行码的计算投影

投影对所有自然数有定义；其规范性定理仅在相应构造子处使用。
它们提供递归检查的元层秩，不给对象公式增加新的函数符号。
-/
namespace YesMetaZFC.Automation.ObjectCodeProjection
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem ProofCode
open ObjectHorn
set_option autoImplicit false

def tag (input : Nat) : Nat := (godel_unpair_value (input - 1)).1
def payload (input : Nat) : Nat := (godel_unpair_value (input - 1)).2
def head (input : Nat) : Nat := (godel_unpair_value (payload input)).1
def tail (input : Nat) : Nat := (godel_unpair_value (payload input)).2
def get (input : Nat) : Nat → Nat
  | 0 => head input
  | n + 1 => get (tail input) n
def field (input index : Nat) : Nat := get (payload input) index

@[simp] theorem tag_node (tagValue : Nat) (fields : List Nat) :
    tag (nodeValue tagValue fields) = tagValue := by
  simp [tag, nodeValue, godel_unpair_value_pair]

@[simp] theorem payload_node (tagValue : Nat) (fields : List Nat) :
    payload (nodeValue tagValue fields) = listValue fields := by
  simp [payload, nodeValue, godel_unpair_value_pair]

@[simp] theorem head_cons (first : Nat) (rest : List Nat) :
    head (listValue (first :: rest)) = first := by
  simp [head, payload, listValue, godel_unpair_value_pair]

@[simp] theorem tail_cons (first : Nat) (rest : List Nat) :
    tail (listValue (first :: rest)) = listValue rest := by
  simp [tail, payload, listValue, godel_unpair_value_pair]

@[simp] theorem get_zero (first : Nat) (rest : List Nat) :
    get (listValue (first :: rest)) 0 = first := by simp [get]

@[simp] theorem get_succ (first : Nat) (rest : List Nat) (index : Nat) :
    get (listValue (first :: rest)) (index + 1) = get (listValue rest) index := by simp [get]

@[simp] theorem field_node (tagValue : Nat) (fields : List Nat) (index : Nat) :
    field (nodeValue tagValue fields) index = get (listValue fields) index := by simp [field]

theorem node_field_lt (tagValue : Nat) (fields : List Nat) (value : Nat) (h : value ∈ fields) :
    value < nodeValue tagValue fields :=
  Nat.lt_succ_of_le (Nat.le_trans (ObjectCodeBounds.list_field_le fields value h)
    (right_le_godel_pair_value _ _))

theorem head_lt_cons (first rest : Nat) :
    first < godel_pair_value 1 (godel_pair_value first rest) + 1 :=
  Nat.lt_succ_of_le (Nat.le_trans (left_le_godel_pair_value _ _) (right_le_godel_pair_value _ _))

theorem tail_lt_cons (first rest : Nat) :
    rest < godel_pair_value 1 (godel_pair_value first rest) + 1 :=
  Nat.lt_succ_of_le (Nat.le_trans (right_le_godel_pair_value _ _) (right_le_godel_pair_value _ _))

end YesMetaZFC.Automation.ObjectCodeProjection
