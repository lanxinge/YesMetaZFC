import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectFormulaSyntax

/-! # 完整内核公式的有限接受证书 -/
namespace YesMetaZFC.Automation.ObjectFormulaSyntax
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT NatPacket IntrinsicQuotation ObjectHorn
open ObjectTermSyntax
set_option autoImplicit false

theorem relation_mem (symbol : RelationSymbol) : symbol ∈ SyntaxDecode.relationSymbols.toList := by
  cases symbol <;> simp [SyntaxDecode.relationSymbols]

theorem head_variables (rule : Rule) (h : rule ∈ rules) : ∀ i, i ∈ rule.head.variables := by
  simp only [rules, termRules, argumentRules, formulaRules, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (((rfl | rfl) | h) | rfl | rfl) |
    ((rfl | rfl) | h) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | decide
    | obtain ⟨symbol, _, rfl⟩ := List.mem_map.mp h
      change ∀ i : Fin 3, i ∈ ([0, 1, 2] : List (Fin 3))
      decide

theorem accept_rule (rule : Rule) (hRule : rule ∈ rules) (values : Fin rule.arity → Nat)
    (hGuards : ∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values)
    (hPremises : ∀ premise, premise ∈ rule.premises → Acceptance rules (premise.eval values)) :
    Acceptance rules (rule.head.eval values) :=
  Acceptance.of_rule rule hRule values
    (fun i => rule.head.variable_le values (head_variables rule hRule i)) hGuards hPremises

def termRow (bound free : Nat) (input : Tree) : Nat := nodeValue 0 [bound, free, treeValue input]
def argumentRow (bound free count : Nat) (input : List Tree) : Nat :=
  nodeValue 1 [bound, free, count, listValue (input.map treeValue)]
def formulaRow (bound free : Nat) (input : Tree) : Nat := nodeValue 4 [bound, free, treeValue input]

theorem variable_accept (isFree : Bool) (bound free index : Nat)
    (hLt : index < if isFree then free else bound) :
    Acceptance rules (termRow bound free (.node (if isFree then 1 else 0) [leaf index])) := by
  have h := accept_rule (variableRule isFree) (by cases isFree <;> simp [rules, termRules])
    (fun i : Fin 3 => [bound, free, index][i])
    (by
      intro guard hGuard
      have hGuard := List.mem_singleton.mp hGuard
      subst guard
      cases isFree <;> exact hLt)
    (by intro premise h; cases h)
  simpa [termRow, variableRule, variableRule.rawNodeVar, ObjectTermSyntax.node, Expr.eval, leaf] using h

theorem application_accept (symbol : FunctionSymbol) (bound free : Nat) (input : List Tree)
    (hArgs : Acceptance rules (argumentRow bound free (signature.funcDomain symbol).length input)) :
    Acceptance rules (termRow bound free (.node 2 (leaf symbol.ctorIdx :: input))) := by
  have h := accept_rule (applicationRule symbol)
    (by
      have hMem : applicationRule symbol ∈ termRules :=
        List.mem_append_right _ (List.mem_map.mpr ⟨symbol, symbol_mem symbol, rfl⟩)
      exact List.mem_append_left _ (List.mem_append_left _ hMem))
    (fun i : Fin 3 => [bound, free, listValue (input.map treeValue)][i])
    (by intro guard h; cases h)
    (by
      intro premise h
      have h := List.mem_singleton.mp h
      subst premise
      exact hArgs)
  simpa [applicationRule, ObjectTermSyntax.node, rawNode, cons, Expr.eval, termRow, leaf, listValue, nodeValue] using h

theorem nil_accept (bound free : Nat) : Acceptance rules (argumentRow bound free 0 []) := by
  exact accept_rule nilRule (by simp [rules, argumentRules])
    (fun i : Fin 2 => if i.val = 0 then bound else free)
    (by intro guard h; cases h) (by intro premise h; cases h)

theorem cons_accept (bound free count : Nat) (head : Tree) (tail : List Tree)
    (hHead : Acceptance rules (termRow bound free head))
    (hTail : Acceptance rules (argumentRow bound free count tail)) :
    Acceptance rules (argumentRow bound free (count + 1) (head :: tail)) := by
  exact accept_rule consRule (by simp [rules, argumentRules])
    (fun i : Fin 5 => [bound, free, count, treeValue head, listValue (tail.map treeValue)][i])
    (by intro guard h; cases h)
    (by
      intro premise h
      dsimp only [consRule] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact hHead
      · have h := List.mem_singleton.mp h
        subst premise
        exact hTail)

mutual
theorem term_accept {bound free : SetContext} : (input : SetTerm bound free) →
    Acceptance rules (termRow bound.length free.length (SyntaxEncode.term input))
  | .bvar entry => variable_accept false _ _ _ (SyntaxDecode.variable_lt entry)
  | .fvar entry => variable_accept true _ _ _ (SyntaxDecode.variable_lt entry)
  | .app symbol args => by
    rw [SyntaxEncode.term_app]
    exact application_accept symbol _ _ _ (arguments_accept args)
termination_by input => sizeOf (SyntaxEncode.term input)
decreasing_by rw [SyntaxEncode.term_app]; simp_wf; omega

theorem arguments_accept {bound free : SetContext} :
    {sorts : SetContext} → (input : Arguments signature bound free sorts) →
    Acceptance rules (argumentRow bound.length free.length sorts.length (SyntaxEncode.argumentsList input))
  | [] , .nil => nil_accept _ _
  | .set :: _, .cons head tail => cons_accept _ _ _ _ _ (term_accept head) (arguments_accept tail)
termination_by _ input => sizeOf (SyntaxEncode.argumentsList input)
decreasing_by all_goals simp only [SyntaxEncode.argumentsList]; all_goals simp_wf; all_goals omega
end

theorem constant_accept (tag : Nat) (hTag : tag = 0 ∨ tag = 1) (bound free : Nat) :
    Acceptance rules (formulaRow bound free (.node tag [])) := by
  apply accept_rule (constantRule tag)
    (by rcases hTag with rfl | rfl <;> simp [rules, formulaRules])
    (fun i : Fin 2 => [bound, free][i])
  · intro guard h; cases h
  · intro premise h; cases h

theorem relation_accept (symbol : RelationSymbol) (bound free : Nat) (input : List Tree)
    (hArgs : Acceptance rules (argumentRow bound free (signature.relDomain symbol).length input)) :
    Acceptance rules (formulaRow bound free (.node 2 (leaf symbol.ctorIdx :: input))) := by
  have h := accept_rule (relationRule symbol)
    (by
      apply List.mem_append_right
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨symbol, relation_mem symbol, rfl⟩)
    (fun i : Fin 3 => [bound, free, listValue (input.map treeValue)][i])
    (by intro guard h; cases h)
    (by
      intro premise h
      have h := List.mem_singleton.mp h
      subst premise
      exact hArgs)
  simpa [relationRule, ObjectTermSyntax.node, rawNode, cons, Expr.eval, formulaRow, leaf, listValue, nodeValue] using h

theorem equality_accept (bound free : Nat) (left right : Tree)
    (hLeft : Acceptance rules (termRow bound free left))
    (hRight : Acceptance rules (termRow bound free right)) :
    Acceptance rules (formulaRow bound free (.node 3 [left, right])) := by
  apply accept_rule equalityRule (by simp [rules, formulaRules])
    (fun i : Fin 4 => [bound, free, treeValue left, treeValue right][i])
  · intro guard h; cases h
  · intro premise h
    rcases List.mem_cons.mp h with rfl | h
    · exact hLeft
    · have h := List.mem_singleton.mp h
      subst premise
      exact hRight

theorem unary_accept (tag : Nat) (binder : Bool)
    (hRule : unaryRule tag binder ∈ formulaRules) (bound free : Nat) (body : Tree)
    (hBody : Acceptance rules (formulaRow (if binder then bound + 1 else bound) free body)) :
    Acceptance rules (formulaRow bound free (.node tag [body])) := by
  have h := accept_rule (unaryRule tag binder) (List.mem_append_right _ hRule)
    (fun i : Fin 3 => [bound, free, treeValue body][i])
    (by intro guard h; cases h)
    (by
      intro premise h
      have h := List.mem_singleton.mp h
      subst premise
      cases binder <;> exact hBody)
  exact h

theorem binary_accept (tag : Nat) (hRule : binaryRule tag ∈ formulaRules)
    (bound free : Nat) (left right : Tree)
    (hLeft : Acceptance rules (formulaRow bound free left))
    (hRight : Acceptance rules (formulaRow bound free right)) :
    Acceptance rules (formulaRow bound free (.node tag [left, right])) := by
  apply accept_rule (binaryRule tag) (List.mem_append_right _ hRule)
    (fun i : Fin 4 => [bound, free, treeValue left, treeValue right][i])
  · intro guard h; cases h
  · intro premise h
    rcases List.mem_cons.mp h with rfl | h
    · exact hLeft
    · have h := List.mem_singleton.mp h
      subst premise
      exact hRight

theorem formula_accept {bound free : SetContext} (input : SetFormula bound free) :
    Acceptance rules (formulaRow bound.length free.length (SyntaxEncode.formula input)) := by
  induction input with
  | falsum => exact constant_accept 0 (Or.inl rfl) _ _
  | truth => exact constant_accept 1 (Or.inr rfl) _ _
  | rel symbol args => exact relation_accept symbol _ _ _ (arguments_accept args)
  | equal left right =>
    cases ‹SetSort›
    exact equality_accept _ _ _ _ (term_accept left) (term_accept right)
  | neg body ih => exact unary_accept 4 false (by simp [formulaRules]) _ _ _ ih
  | conj left right ihLeft ihRight => exact binary_accept 5 (by simp [formulaRules]) _ _ _ _ ihLeft ihRight
  | disj left right ihLeft ihRight => exact binary_accept 6 (by simp [formulaRules]) _ _ _ _ ihLeft ihRight
  | imp left right ihLeft ihRight => exact binary_accept 7 (by simp [formulaRules]) _ _ _ _ ihLeft ihRight
  | iff left right ihLeft ihRight => exact binary_accept 8 (by simp [formulaRules]) _ _ _ _ ihLeft ihRight
  | forallE sort body ih =>
    cases sort
    exact unary_accept 9 true (by simp [formulaRules]) _ _ _ ih
  | existsE sort body ih =>
    cases sort
    exact unary_accept 10 true (by simp [formulaRules]) _ _ _ ih

/-- 当前 AST 的任意合法公式都被固定图的实际检查器接受。 -/
theorem checked_encode {bound free : SetContext} (formula : SetFormula bound free) :
    checked bound.length free.length (treeValue (SyntaxEncode.formula formula)) = true :=
  acceptance_check rules rank descending _ (formula_accept formula)

end YesMetaZFC.Automation.ObjectFormulaSyntax
