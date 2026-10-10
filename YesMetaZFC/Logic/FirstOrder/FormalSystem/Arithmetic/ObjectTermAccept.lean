import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectTermSyntax

/-! # 任意类型正确内核项的有限接受证书 -/
namespace YesMetaZFC.Automation.ObjectTermSyntax
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT NatPacket IntrinsicQuotation ObjectHorn
set_option autoImplicit false

def termRow (bound free : Nat) (input : Tree) : Nat := nodeValue 0 [bound, free, treeValue input]
def argumentRow (bound free count : Nat) (input : List Tree) : Nat :=
  nodeValue 1 [bound, free, count, listValue (input.map treeValue)]
def parameterRow (free count : Nat) (input : Tree) : Nat := nodeValue 2 [free, count, treeValue input]
def envelopeRow (count : Nat) (input : Tree) : Nat := nodeValue 3 [count, treeValue input]

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
  simpa [termRow, variableRule, variableRule.rawNodeVar, node, Expr.eval, leaf] using h

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
  simpa [applicationRule, node, rawNode, cons, Expr.eval, termRow, leaf, listValue, nodeValue] using h

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

end YesMetaZFC.Automation.ObjectTermSyntax
