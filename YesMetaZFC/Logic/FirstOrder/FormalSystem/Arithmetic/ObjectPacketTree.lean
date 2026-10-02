import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectPacketToken

/-! # 任意有限树与子树列表的传输前缀证书 -/
namespace YesMetaZFC.Automation.ObjectPacket
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem ProofT NatPacket IntrinsicQuotation ProofCode
open ObjectHorn
set_option autoImplicit false

def forestCode (input : List Tree) : Nat := listValue (input.map treeValue)

theorem tree_code (tag : Nat) (children : List Tree) :
    treeValue (.node tag children) = godel_pair_value tag (forestCode children) + 1 := treeValue_node _ _

theorem forestCode_cons (head : Tree) (rest : List Tree) :
    forestCode (head :: rest) = godel_pair_value 1 (godel_pair_value (treeValue head) (forestCode rest)) + 1 := rfl

theorem forest_head_le (head : Tree) (rest : List Tree) : treeValue head ≤ forestCode (head :: rest) :=
  list_field_le List.mem_cons_self

theorem forest_tail_code_le (head : Tree) (rest : List Tree) : forestCode rest ≤ forestCode (head :: rest) :=
  Nat.le_trans (right_le_godel_pair_value _ _)
    (Nat.le_trans (right_le_godel_pair_value _ _) (Nat.le_succ _))

theorem tree_rule_accept (tag : Nat) (children : List Tree) (tail : Nat)
    (hForest : Acceptance rules (nodeValue 4 [forestCode children, children.length, tail, forest children tail])) :
    Acceptance rules (nodeValue 3 [treeValue (.node tag children), tail, tree (.node tag children) tail]) := by
  let mid := forest children tail
  let payload := token children.length mid
  let output := token tag payload
  let root := nodeValue 3 [godel_pair_value tag (forestCode children) + 1, tail, output]
  have hInput : godel_pair_value tag (forestCode children) + 1 ≤ root := field_le 3 (by simp)
  have hTag : tag ≤ root := Nat.le_trans (left_le_godel_pair_value _ _) (Nat.le_trans (Nat.le_succ _) hInput)
  have hChildren : forestCode children ≤ root := Nat.le_trans (right_le_godel_pair_value _ _) (Nat.le_trans (Nat.le_succ _) hInput)
  have hTail : tail ≤ root := field_le 3 (by simp)
  have hOut : output ≤ root := field_le 3 (by simp)
  have hPayload : payload ≤ root := Nat.le_trans (token_tail_le tag payload) hOut
  have hCount : children.length ≤ root := Nat.le_trans (token_number_le _ _) hPayload
  have hMid : mid ≤ root := Nat.le_trans (token_tail_le _ _) hPayload
  have h := Acceptance.of_rule (rules := rules) treeRule (by simp [rules])
    (fun i : Fin 7 => [tag, forestCode children, tail, output, children.length, mid, payload][i])
    (by
      change ∀ i : Fin 7, [tag, forestCode children, tail, output, children.length, mid, payload][i] ≤ root
      apply list_bounds [tag, forestCode children, tail, output, children.length, mid, payload] root
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    (by intro guard h; exact False.elim (List.not_mem_nil h))
    (by
      intro premise hPremise
      dsimp only [treeRule] at hPremise
      rcases List.mem_cons.mp hPremise with rfl | hPremise
      · exact hForest
      · rcases List.mem_cons.mp hPremise with rfl | hPremise
        · exact token_accept children.length mid
        · have hPremise := List.mem_singleton.mp hPremise
          subst premise
          exact token_accept tag payload)
  rw [tree_code, tree_node]
  exact h

theorem forest_nil_accept (tail : Nat) : Acceptance rules (nodeValue 4 [forestCode [] , 0, tail, tail]) :=
  accept_head forestNil (by simp [rules]) (fun _ => tail) (by decide)
    (by intro guard h; exact False.elim (List.not_mem_nil h))
    (by intro premise h; exact False.elim (List.not_mem_nil h))

theorem forest_cons_accept (head : Tree) (rest : List Tree) (tail : Nat)
    (hRest : Acceptance rules (nodeValue 4 [forestCode rest, rest.length, tail, forest rest tail]))
    (hHead : Acceptance rules (nodeValue 3 [treeValue head, forest rest tail, tree head (forest rest tail)])) :
    Acceptance rules (nodeValue 4 [forestCode (head :: rest), (head :: rest).length, tail, forest (head :: rest) tail]) := by
  let mid := forest rest tail
  let output := tree head mid
  let root := nodeValue 4 [forestCode (head :: rest), rest.length + 1, tail, output]
  have hInput : forestCode (head :: rest) ≤ root := field_le 4 (by simp)
  have hHeadCode : treeValue head ≤ root := Nat.le_trans (forest_head_le head rest) hInput
  have hRestCode : forestCode rest ≤ root := Nat.le_trans (forest_tail_code_le head rest) hInput
  have hCount : rest.length ≤ root := Nat.le_trans (Nat.le_succ _) (field_le 4 (by simp))
  have hTail : tail ≤ root := field_le 4 (by simp)
  have hOut : output ≤ root := field_le 4 (by simp)
  have hMid : mid ≤ root := Nat.le_trans (tree_tail_le head mid) hOut
  have h := Acceptance.of_rule (rules := rules) forestCons (by simp [rules])
    (fun i : Fin 6 => [treeValue head, forestCode rest, rest.length, tail, output, mid][i])
    (by
      change ∀ i : Fin 6, [treeValue head, forestCode rest, rest.length, tail, output, mid][i] ≤ root
      apply list_bounds [treeValue head, forestCode rest, rest.length, tail, output, mid] root
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    (by intro guard h; exact False.elim (List.not_mem_nil h))
    (by
      intro premise hPremise
      dsimp only [forestCons] at hPremise
      rcases List.mem_cons.mp hPremise with rfl | hPremise
      · exact hRest
      · have hPremise := List.mem_singleton.mp hPremise
        subst premise
        exact hHead)
  rw [forest_cons]
  exact h

mutual
theorem tree_accept (input : Tree) (tail : Nat) :
    Acceptance rules (nodeValue 3 [treeValue input, tail, tree input tail]) := by
  cases input with
  | node tag children => exact tree_rule_accept tag children tail (forest_accept children tail)
termination_by sizeOf input

theorem forest_accept (input : List Tree) (tail : Nat) :
    Acceptance rules (nodeValue 4 [forestCode input, input.length, tail, forest input tail]) := by
  cases input with
  | nil => exact forest_nil_accept tail
  | cons head rest =>
    exact forest_cons_accept head rest tail (forest_accept rest tail) (tree_accept head (forest rest tail))
termination_by sizeOf input
end

end YesMetaZFC.Automation.ObjectPacket
