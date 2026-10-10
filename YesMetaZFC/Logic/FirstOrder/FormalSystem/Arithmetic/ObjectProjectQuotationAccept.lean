import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProjectQuotation

/-! # quotation 转换的有限接受证书 -/
namespace YesMetaZFC.Automation.ObjectProjectQuotation
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem ProofT NatPacket IntrinsicQuotation
open ObjectHorn
set_option autoImplicit false

def row (input : Tree) (output : Nat) : Nat := nodeValue 0 [treeValue input, output]

theorem constant_accept (tag : Nat) (hRule : constantRule tag ∈ rules) :
    Acceptance rules (row (.node tag []) (treeValue (.node tag []))) := by
  exact accept_rule (constantRule tag) hRule Fin.elim0
    (by intro premise h; cases h)

theorem atom_accept (tag : Nat) (children : List Tree) (hRule : atomRule tag ∈ rules) :
    Acceptance rules (row (.node tag children) (treeValue (atom tag children))) := by
  have h := accept_rule (atomRule tag) hRule (fun _ => listValue (children.map treeValue))
    (by intro premise h; cases h)
  simpa only [row, atomRule, node, rawNode, Expr.node_eval, Expr.eval, List.map_cons,
    List.map_nil, treeValue_node, atom_value, nodeValue] using h

theorem unary_accept (tag : Nat) (input output : Tree) (hRule : unaryRule tag ∈ rules)
    (hBody : Acceptance rules (row input (treeValue output))) :
    Acceptance rules (row (.node tag [input]) (treeValue (.node tag [output]))) := by
  have h := accept_rule (unaryRule tag) hRule
    (fun i : Fin 2 => if i.val = 0 then treeValue input else treeValue output)
    (by
      intro premise h
      have h := List.mem_singleton.mp h
      subst premise
      exact hBody)
  exact h

theorem binary_accept (tag : Nat) (left right a b : Tree) (hRule : binaryRule tag ∈ rules)
    (hLeft : Acceptance rules (row left (treeValue a)))
    (hRight : Acceptance rules (row right (treeValue b))) :
    Acceptance rules (row (.node tag [left, right]) (treeValue (.node tag [a, b]))) := by
  have h := accept_rule (binaryRule tag) hRule
    (fun i : Fin 4 => [treeValue left, treeValue right, treeValue a, treeValue b][i])
    (by
      intro premise h
      dsimp only [binaryRule] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact hLeft
      · have h := List.mem_singleton.mp h
        subst premise
        exact hRight)
  exact h

theorem run_accept (input : Tree) : ∀ output, run input = some output →
    Acceptance rules (row input (treeValue output)) := by
  fun_induction run input
  case case1 | case2 =>
    intro output h
    cases h
    exact constant_accept _ (by simp [rules])
  case case3 | case4 | case12 =>
    intro output h
    cases h
    exact atom_accept _ _ (by simp [rules])
  case case5 body ih | case10 body ih | case11 body ih =>
    intro output h
    obtain ⟨decoded, hBody, hOut⟩ := Option.bind_eq_some_iff.mp h
    cases hOut
    exact unary_accept _ _ _ (by simp [rules]) (ih decoded hBody)
  case case6 left right ihLeft ihRight | case7 left right ihLeft ihRight
     | case8 left right ihLeft ihRight | case9 left right ihLeft ihRight =>
    intro output h
    obtain ⟨a, hLeft, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hRight, hOut⟩ := Option.bind_eq_some_iff.mp hRest
    cases hOut
    exact binary_accept _ _ _ _ _ (by simp [rules]) (ihLeft a hLeft) (ihRight b hRight)
  case case13 => intro output h; cases h

end YesMetaZFC.Automation.ObjectProjectQuotation
