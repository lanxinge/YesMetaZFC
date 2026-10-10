import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectSyntaxTransform

/-! # 递归语法变换的有限接受证书

每次成功计算均生成有限规则轨迹；与可靠性合并后得到全自然数的精确规格。
-/
namespace YesMetaZFC.Automation.ObjectSyntaxTransform
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT NatPacket IntrinsicQuotation
open ObjectHorn ObjectCodeProjection
set_option autoImplicit false

set_option maxHeartbeats 1000000 in
theorem head_variables (rule : Rule) (h : rule ∈ rules) : ∀ i, i ∈ rule.head.variables := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem accept_rule (rule : Rule) (hRule : rule ∈ rules) (values : Fin rule.arity → Nat)
    (hGuards : ∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values)
    (hPremises : ∀ premise, premise ∈ rule.premises → Acceptance rules (premise.eval values)) :
    Acceptance rules (rule.head.eval values) :=
  Acceptance.of_rule rule hRule values
    (fun i => rule.head.variable_le values (head_variables rule hRule i)) hGuards hPremises

def termRow (mode depth parameter : Nat) (input : Tree) (output : Nat) : Nat :=
  nodeValue 1 [mode, depth, parameter, treeValue input, output]
def argumentRow (mode depth parameter : Nat) (input : List Tree) (output : Nat) : Nat :=
  nodeValue 2 [mode, depth, parameter, listValue (input.map treeValue), output]
def formulaRow (mode depth parameter : Nat) (input : Tree) (output : Nat) : Nat :=
  nodeValue 3 [mode, depth, parameter, treeValue input, output]

theorem lookup_accept (table index output : Nat) (h : SyntaxTransform.lookup table index = some output) :
    Acceptance rules (nodeValue 0 [table, index, output]) := by
  rw [SyntaxTransform.lookup.eq_def] at h
  split at h
  · rename_i hShape
    cases index with
    | zero =>
      cases h
      have hAccept := accept_rule lookupHead (by simp [rules])
        (fun i : Fin 2 => [head table, tail table][i])
        (by intro guard h; cases h) (by intro premise h; cases h)
      change Acceptance rules (nodeValue 0 [ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value (head table) (tail table)) + 1, 0, head table]) at hAccept
      rwa [← hShape] at hAccept
    | succ index =>
      dsimp only at h
      split at h
      · rename_i hLt
        have hChild := lookup_accept (tail table) index output h
        have hAccept := accept_rule lookupTail (by simp [rules])
          (fun i : Fin 4 => [head table, tail table, index, output][i])
          (by intro guard h; cases h)
          (by intro premise h; obtain rfl := List.mem_singleton.mp h; exact hChild)
        change Acceptance rules (nodeValue 0 [ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value (head table) (tail table)) + 1, index + 1, output]) at hAccept
        rwa [← hShape] at hAccept
      · cases h
  · cases h
termination_by table

private theorem bound_identity_accept (mode : Nat) (below : Bool) (hRule : boundIdentity mode below ∈ rules)
    (depth parameter index : Nat) (hBelow : below = true → index < depth) :
    Acceptance rules (termRow mode depth parameter (SyntaxSubstitution.bvar index)
      (treeValue (SyntaxSubstitution.bvar index))) := by
  apply accept_rule (boundIdentity mode below) hRule
    (fun i : Fin 3 => [depth, parameter, index][i])
  · intro guard h
    cases below with
    | false => cases h
    | true =>
      obtain rfl := List.mem_singleton.mp h
      exact hBelow rfl
  · intro premise h; cases h

private theorem bound_abstract_accept (depth parameter index : Nat) (hLe : depth ≤ index) :
    Acceptance rules (termRow 1 depth parameter (SyntaxSubstitution.bvar index)
      (treeValue (SyntaxSubstitution.bvar (index + 1)))) := by
  apply accept_rule boundAbstract (by simp [rules])
    (fun i : Fin 3 => [depth, parameter, index][i])
  · intro guard h
    obtain rfl := List.mem_singleton.mp h
    exact Nat.lt_succ_of_le hLe
  · intro premise h; cases h

private theorem bound_point_accept (depth parameter : Nat) :
    Acceptance rules (termRow 2 depth parameter (SyntaxSubstitution.bvar depth) parameter) :=
  accept_rule boundPoint (by simp [rules]) (fun i : Fin 2 => [depth, parameter][i])
    (by intro guard h; cases h) (by intro premise h; cases h)

private theorem bound_predecessor_accept (depth parameter index : Nat) (hLt : depth < index + 1) :
    Acceptance rules (termRow 2 depth parameter (SyntaxSubstitution.bvar (index + 1))
      (treeValue (SyntaxSubstitution.bvar index))) := by
  apply accept_rule boundPredecessor (by simp [rules]) (fun i : Fin 3 => [depth, parameter, index][i])
  · intro guard h
    obtain rfl := List.mem_singleton.mp h
    exact hLt
  · intro premise h; cases h

theorem bound_accept (mode depth parameter index output : Nat)
    (h : SyntaxTransform.boundValue mode depth parameter index = some output) :
    Acceptance rules (termRow mode depth parameter (SyntaxSubstitution.bvar index) output) := by
  match mode with
  | 0 =>
    cases h
    exact bound_identity_accept 0 false (by simp [rules]) _ _ _ (by intro h; cases h)
  | 1 =>
    simp only [SyntaxTransform.boundValue] at h
    split at h
    · cases h
      exact bound_identity_accept 1 true (by simp [rules]) _ _ _ (fun _ => ‹index < depth›)
    · cases h
      exact bound_abstract_accept _ _ _ (Nat.le_of_not_gt ‹¬ index < depth›)
  | 2 =>
    simp only [SyntaxTransform.boundValue] at h
    split at h
    · cases h
      exact bound_identity_accept 2 true (by simp [rules]) _ _ _ (fun _ => ‹index < depth›)
    · split at h
      · subst index
        cases h
        exact bound_point_accept _ _
      · cases h
        cases index with
        | zero => omega
        | succ index => exact bound_predecessor_accept _ _ _ (by omega)
  | 3 =>
    cases h
    exact bound_identity_accept 3 false (by simp [rules]) _ _ _ (by intro h; cases h)
  | _ + 4 => cases h

theorem free_accept (mode depth parameter index output : Nat)
    (h : SyntaxTransform.freeValue mode depth parameter index = some output) :
    Acceptance rules (termRow mode depth parameter (SyntaxSubstitution.fvar index) output) := by
  match mode with
  | 0 =>
    cases h
    exact accept_rule freeWeaken (by simp [rules]) (fun i : Fin 3 => [depth, parameter, index][i])
      (by intro guard h; cases h) (by intro premise h; cases h)
  | 1 =>
    cases index with
    | zero =>
      cases h
      exact accept_rule freeAbstractHead (by simp [rules]) (fun i : Fin 2 => [depth, parameter][i])
        (by intro guard h; cases h) (by intro premise h; cases h)
    | succ index =>
      cases h
      exact accept_rule freeAbstractTail (by simp [rules]) (fun i : Fin 3 => [depth, parameter, index][i])
        (by intro guard h; cases h) (by intro premise h; cases h)
  | 2 =>
    cases h
    exact accept_rule freeIdentity (by simp [rules]) (fun i : Fin 3 => [depth, parameter, index][i])
      (by intro guard h; cases h) (by intro premise h; cases h)
  | 3 =>
    apply accept_rule freeReplace (by simp [rules]) (fun i : Fin 4 => [depth, parameter, index, output][i])
    · intro guard h; cases h
    · intro premise hPremise
      obtain rfl := List.mem_singleton.mp hPremise
      exact lookup_accept _ _ _ h
  | _ + 4 => cases h

private theorem application_accept (kind mode depth parameter symbol : Nat) (input : List Tree) (output : Nat)
    (hRule : application kind ∈ rules)
    (hArgs : Acceptance rules (argumentRow mode depth parameter input output)) :
    Acceptance rules (nodeValue kind [mode, depth, parameter, treeValue (.node 2 (.node symbol [] :: input)),
      ProofCode.godel_pair_value 2 (ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value (nodeValue symbol []) output) + 1) + 1]) := by
  have h := accept_rule (application kind) hRule
    (fun i : Fin 6 => [mode, depth, parameter, symbol, listValue (input.map treeValue), output][i])
    (by intro guard h; cases h)
    (by intro premise h; obtain rfl := List.mem_singleton.mp h; exact hArgs)
  change Acceptance rules (nodeValue kind [mode, depth, parameter,
    ProofCode.godel_pair_value 2 (ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value (nodeValue symbol []) (listValue (input.map treeValue))) + 1) + 1,
    ProofCode.godel_pair_value 2 (ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value (nodeValue symbol []) output) + 1) + 1]) at h
  simpa only [treeValue_node, List.map_cons, List.map_nil, nodeValue, listValue] using h

mutual
theorem term_accept (mode depth parameter : Nat) : (input : Tree) → (output : Nat) →
    SyntaxTransform.term mode depth parameter input = some output →
    Acceptance rules (termRow mode depth parameter input output)
  | input, output, h => by
    rw [SyntaxTransform.term.eq_def] at h
    split at h
    · exact bound_accept _ _ _ _ _ h
    · exact free_accept _ _ _ _ _ h
    · obtain ⟨out, hArgs, hOut⟩ := Option.bind_eq_some_iff.mp h
      cases hOut
      exact application_accept 1 _ _ _ _ _ _ (by simp [rules]) (arguments_accept _ _ _ _ out hArgs)
    · cases h
termination_by input => sizeOf input

theorem arguments_accept (mode depth parameter : Nat) : (input : List Tree) → (output : Nat) →
    SyntaxTransform.arguments mode depth parameter input = some output →
    Acceptance rules (argumentRow mode depth parameter input output)
  | [] , output, h => by
    simp only [SyntaxTransform.arguments] at h
    split at h
    · cases h
      apply accept_rule nilArguments (by simp [rules]) (fun i : Fin 3 => [mode, depth, parameter][i])
      · intro guard h
        obtain rfl := List.mem_singleton.mp h
        exact ‹mode < 4›
      · intro premise h; cases h
    · cases h
  | first :: rest, output, h => by
    simp only [SyntaxTransform.arguments] at h
    obtain ⟨firstOut, hFirst, hRemaining⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨restOut, hRest, hOut⟩ := Option.bind_eq_some_iff.mp hRemaining
    cases hOut
    apply accept_rule consArguments (by simp [rules])
      (fun i : Fin 7 => [mode, depth, parameter, treeValue first, listValue (rest.map treeValue), firstOut, restOut][i])
    · intro guard h; cases h
    · intro premise h
      rcases List.mem_cons.mp h with rfl | h
      · exact term_accept _ _ _ first firstOut hFirst
      · obtain rfl := List.mem_singleton.mp h
        exact arguments_accept _ _ _ rest restOut hRest
termination_by input => sizeOf input
end


private theorem constant_accept (tag mode depth parameter : Nat) (hRule : constant tag ∈ rules)
    (hMode : mode < 4) :
    Acceptance rules (formulaRow mode depth parameter (.node tag []) (nodeValue tag [])) := by
  apply accept_rule (constant tag) hRule (fun i : Fin 3 => [mode, depth, parameter][i])
  · intro guard h
    obtain rfl := List.mem_singleton.mp h
    exact hMode
  · intro premise h; cases h

private theorem binary_accept (tag kind mode depth parameter : Nat) (left right : Tree) (leftOut rightOut : Nat)
    (hRule : binary tag kind ∈ rules)
    (hLeft : Acceptance rules (nodeValue kind [mode, depth, parameter, treeValue left, leftOut]))
    (hRight : Acceptance rules (nodeValue kind [mode, depth, parameter, treeValue right, rightOut])) :
    Acceptance rules (formulaRow mode depth parameter (.node tag [left, right]) (nodeValue tag [leftOut, rightOut])) := by
  have h := accept_rule (binary tag kind) hRule
    (fun i : Fin 7 => [mode, depth, parameter, treeValue left, treeValue right, leftOut, rightOut][i])
    (by intro guard h; cases h)
    (by
      intro premise h
      dsimp only [binary] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact hLeft
      · obtain rfl := List.mem_singleton.mp h
        exact hRight)
  exact h

private theorem unary_accept (tag : Nat) (binder : Bool) (mode depth parameter : Nat) (input : Tree) (output : Nat)
    (hRule : unary tag binder ∈ rules)
    (hBody : Acceptance rules (formulaRow mode (if binder then depth + 1 else depth) parameter input output)) :
    Acceptance rules (formulaRow mode depth parameter (.node tag [input]) (nodeValue tag [output])) := by
  have h := accept_rule (unary tag binder) hRule
    (fun i : Fin 5 => [mode, depth, parameter, treeValue input, output][i])
    (by intro guard h; cases h)
    (by intro premise h; obtain rfl := List.mem_singleton.mp h; cases binder <;> exact hBody)
  exact h

theorem formula_accept (mode depth parameter : Nat) : (input : Tree) → (output : Nat) →
    SyntaxTransform.formula mode depth parameter input = some output →
    Acceptance rules (formulaRow mode depth parameter input output)
  | input, output, h => by
    rw [SyntaxTransform.formula.eq_def] at h
    split at h
    · split at h
      · cases h
        exact constant_accept 0 _ _ _ (by simp [rules]) ‹mode < 4›
      · cases h
    · split at h
      · cases h
        exact constant_accept 1 _ _ _ (by simp [rules]) ‹mode < 4›
      · cases h
    · obtain ⟨out, hArgs, hOut⟩ := Option.bind_eq_some_iff.mp h
      cases hOut
      exact application_accept 3 _ _ _ _ _ _ (by simp [rules]) (arguments_accept _ _ _ _ out hArgs)
    · obtain ⟨leftOut, hLeft, hRemaining⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rightOut, hRight, hOut⟩ := Option.bind_eq_some_iff.mp hRemaining
      cases hOut
      exact binary_accept 3 1 _ _ _ _ _ leftOut rightOut (by simp [rules])
        (term_accept _ _ _ _ leftOut hLeft) (term_accept _ _ _ _ rightOut hRight)
    · obtain ⟨out, hBody, hOut⟩ := Option.bind_eq_some_iff.mp h
      cases hOut
      exact unary_accept 4 false _ _ _ _ out (by simp [rules]) (formula_accept _ _ _ _ out hBody)
    · obtain ⟨leftOut, hLeft, hRemaining⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rightOut, hRight, hOut⟩ := Option.bind_eq_some_iff.mp hRemaining
      cases hOut
      exact binary_accept 5 3 _ _ _ _ _ leftOut rightOut (by simp [rules])
        (formula_accept _ _ _ _ leftOut hLeft) (formula_accept _ _ _ _ rightOut hRight)
    · obtain ⟨leftOut, hLeft, hRemaining⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rightOut, hRight, hOut⟩ := Option.bind_eq_some_iff.mp hRemaining
      cases hOut
      exact binary_accept 6 3 _ _ _ _ _ leftOut rightOut (by simp [rules])
        (formula_accept _ _ _ _ leftOut hLeft) (formula_accept _ _ _ _ rightOut hRight)
    · obtain ⟨leftOut, hLeft, hRemaining⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rightOut, hRight, hOut⟩ := Option.bind_eq_some_iff.mp hRemaining
      cases hOut
      exact binary_accept 7 3 _ _ _ _ _ leftOut rightOut (by simp [rules])
        (formula_accept _ _ _ _ leftOut hLeft) (formula_accept _ _ _ _ rightOut hRight)
    · obtain ⟨leftOut, hLeft, hRemaining⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rightOut, hRight, hOut⟩ := Option.bind_eq_some_iff.mp hRemaining
      cases hOut
      exact binary_accept 8 3 _ _ _ _ _ leftOut rightOut (by simp [rules])
        (formula_accept _ _ _ _ leftOut hLeft) (formula_accept _ _ _ _ rightOut hRight)
    · obtain ⟨out, hBody, hOut⟩ := Option.bind_eq_some_iff.mp h
      cases hOut
      exact unary_accept 9 true _ _ _ _ out (by simp [rules]) (formula_accept _ _ _ _ out hBody)
    · obtain ⟨out, hBody, hOut⟩ := Option.bind_eq_some_iff.mp h
      cases hOut
      exact unary_accept 10 true _ _ _ _ out (by simp [rules]) (formula_accept _ _ _ _ out hBody)
    · cases h
termination_by input => sizeOf input

/-- 成功的独立变换计算总能被固定有限图接受。 -/
theorem checked_complete (mode depth parameter : Nat) (input : Tree) (output : Nat)
    (h : SyntaxTransform.formula mode depth parameter input = some output) :
    checked mode depth parameter (treeValue input) output = true :=
  acceptance_check rules rank descending _ (formula_accept mode depth parameter input output h)

end YesMetaZFC.Automation.ObjectSyntaxTransform
