import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornValues

/-! # 内核 quotation 数值的实际逆解码

这里解码结构配数，区别于版本化 NatPacket 字节包。
输入为任意自然数；非规范的节点或列表编码均返回 none。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.IntrinsicQuotation
open NatPacket ProofCode
open _root_.YesMetaZFC.Automation.ObjectHorn
set_option autoImplicit false

mutual
def decodeTree (number : Nat) : Option Tree :=
  match number with
  | 0 => none
  | n + 1 => do
      let fields ← decodeForest (godel_unpair_value n).2
      return .node (godel_unpair_value n).1 fields
termination_by number
decreasing_by exact Nat.lt_succ_of_le (godel_unpair_value_right_le _)

def decodeForest (number : Nat) : Option (List Tree) :=
  match number with
  | 0 => none
  | n + 1 =>
    let fields := godel_unpair_value n
    if fields.1 = 0 then
      if fields.2 = 0 then some [] else none
    else if fields.1 = 1 then do
      let pair := godel_unpair_value fields.2
      let first ← decodeTree pair.1
      let rest ← decodeForest pair.2
      return first :: rest
    else none
termination_by number
decreasing_by
  all_goals apply Nat.lt_succ_of_le
  · exact Nat.le_trans (godel_unpair_value_left_le _) (godel_unpair_value_right_le _)
  · exact Nat.le_trans (godel_unpair_value_right_le _) (godel_unpair_value_right_le _)
end

mutual
@[simp] theorem decode_treeValue (input : Tree) : decodeTree (treeValue input) = some input := by
  cases input with
  | node tag children =>
    rw [treeValue_node]
    unfold nodeValue
    rw [decodeTree.eq_def]
    simp only [godel_unpair_value_pair, decode_listValue children]
    rfl
termination_by sizeOf input

@[simp] theorem decode_listValue (input : List Tree) :
    decodeForest (listValue (input.map treeValue)) = some input := by
  cases input with
  | nil =>
    rw [List.map_nil, listValue, decodeForest.eq_def]
    rfl
  | cons first rest =>
    rw [List.map_cons, listValue, decodeForest.eq_def]
    simp only [godel_unpair_value_pair, Nat.one_ne_zero, if_false, if_true,
      decode_treeValue first, decode_listValue rest]
    rfl
termination_by sizeOf input
end

mutual
theorem treeValue_of_decode {number : Nat} {input : Tree} (h : decodeTree number = some input) :
    treeValue input = number := by
  cases hNumber : number with
  | zero => rw [hNumber, decodeTree.eq_def] at h; cases h
  | succ n =>
    rw [hNumber, decodeTree.eq_def] at h
    obtain ⟨fields, hFields, hInput⟩ := Option.bind_eq_some_iff.mp h
    cases hInput
    rw [treeValue_node, nodeValue, listValue_of_decode hFields, godel_unpair_value_spec]
termination_by number
decreasing_by
  rw [hNumber]
  exact Nat.lt_succ_of_le (godel_unpair_value_right_le _)

theorem listValue_of_decode {number : Nat} {input : List Tree} (h : decodeForest number = some input) :
    listValue (input.map treeValue) = number := by
  cases hNumber : number with
  | zero => rw [hNumber, decodeForest.eq_def] at h; cases h
  | succ n =>
    rw [hNumber, decodeForest.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hTag
      split at h
      · rename_i hPayload
        cases h
        have hPair := godel_unpair_value_spec n
        rw [hTag, hPayload] at hPair
        exact congrArg Nat.succ hPair
      · cases h
    · split at h
      · rename_i hTag
        obtain ⟨first, hFirst, hRemaining⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨rest, hTailDecode, hInput⟩ := Option.bind_eq_some_iff.mp hRemaining
        cases hInput
        rw [List.map_cons, listValue, treeValue_of_decode hFirst, listValue_of_decode hTailDecode,
          godel_unpair_value_spec, ← hTag, godel_unpair_value_spec]
      · cases h
termination_by number
decreasing_by
  all_goals rw [hNumber]
  all_goals apply Nat.lt_succ_of_le
  · exact Nat.le_trans (godel_unpair_value_left_le _) (godel_unpair_value_right_le _)
  · exact Nat.le_trans (godel_unpair_value_right_le _) (godel_unpair_value_right_le _)
end

theorem decodeTree_eq_some_iff (number : Nat) (input : Tree) :
    decodeTree number = some input ↔ treeValue input = number :=
  ⟨treeValue_of_decode, fun h => h ▸ decode_treeValue input⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.IntrinsicQuotation
