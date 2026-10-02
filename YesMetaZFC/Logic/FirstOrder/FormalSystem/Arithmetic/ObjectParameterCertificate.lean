import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectTermReject
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxParameters

/-! # 原 indexed 参数外壳的正负递归证书 -/
namespace YesMetaZFC.Automation.ObjectTermSyntax
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT NatPacket IntrinsicQuotation ObjectHorn
set_option autoImplicit false

theorem parameter_nil_accept (free : Nat) : Acceptance rules (parameterRow free 0 (leaf 0)) := by
  exact accept_rule parameterNilRule (by simp [rules, parameterRules]) (fun _ => free)
    (by intro guard h; cases h) (by intro premise h; cases h)

theorem parameter_cons_accept (free count : Nat) (head tail : Tree)
    (hHead : Acceptance rules (termRow 0 free head))
    (hTail : Acceptance rules (parameterRow free count tail)) :
    Acceptance rules (parameterRow free (count + 1) (.node 0 [head, tail])) := by
  exact accept_rule parameterConsRule (by simp [rules, parameterRules])
    (fun i : Fin 4 => [free, count, treeValue head, treeValue tail][i])
    (by intro guard h; cases h)
    (by
      intro premise h
      dsimp only [parameterConsRule] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact hHead
      · have h := List.mem_singleton.mp h
        subst premise
        exact hTail)

theorem parameters_accept {free sorts : SetContext} (args : Arguments signature [] free sorts) :
    Acceptance rules (parameterRow free.length sorts.length (SyntaxParameters.encodeTerms args)) := by
  cases args with
  | nil => exact parameter_nil_accept _
  | @cons sort sorts head tail =>
    cases sort
    exact parameter_cons_accept _ _ _ _ (term_accept head) (parameters_accept tail)

theorem envelope_accept {count : Nat} (parameters : SyntaxParameters.Parameters count) :
    Acceptance rules (envelopeRow count (SyntaxParameters.encode parameters)) := by
  have h := accept_rule envelopeRule (by simp [rules, parameterRules])
    (fun i : Fin 3 => [count, parameters.free.length, treeValue (SyntaxParameters.encodeTerms parameters.args)][i])
    (by intro guard h; cases h)
    (by
      intro premise h
      have h := List.mem_singleton.mp h
      subst premise
      change Acceptance rules (parameterRow parameters.free.length count (SyntaxParameters.encodeTerms parameters.args))
      simpa only [List.length_replicate] using parameters_accept parameters.args)
  exact h

theorem parameters_reject (free sorts : SetContext) (input : Tree)
    (hBad : SyntaxParameters.terms free sorts input = none) :
    Rejection rules (parameterRow free.length sorts.length input) := by
  apply Rejection.of_tagged heads_tagged 2 [free.length, sorts.length, treeValue input]
  intro rule hRule values _ hHead _
  rw [rulesFor_two] at hRule
  rcases List.mem_cons.mp hRule with rfl | hRule
  · dsimp only [parameterNilRule] at values hHead ⊢
    have h := ((nodeValue_eq_iff 2 2 [free.length, sorts.length, treeValue input]
      [values 0, 0, nodeValue 0 []]).mp hHead).2
    simp only [List.cons.injEq, and_true] at h
    have hSorts := List.length_eq_zero_iff.mp h.2.1
    have hInput := treeValue_node_zero h.2.2
    subst sorts
    subst input
    cases hBad
  · have hRule := List.mem_singleton.mp hRule
    subst rule
    dsimp only [parameterConsRule] at values hHead ⊢
    have h := ((nodeValue_eq_iff 2 2 [free.length, sorts.length, treeValue input]
      [values 0, values 1 + 1, nodeValue 0 [values 2, values 3]]).mp hHead).2
    simp only [List.cons.injEq, and_true] at h
    obtain ⟨head, tail, rfl, hHeadCode, hTailCode⟩ := treeValue_node_two h.2.2
    cases sorts with
    | nil => simp at h
    | cons sort sorts =>
      cases sort
      have hCount : sorts.length = values 1 := by simpa using h.2.1
      cases hTerm : SyntaxDecode.term [] free head with
      | none =>
        refine ⟨node 0 [.literal 0, .var 0, .var 2] , List.mem_cons_self, ?_⟩
        change Rejection rules (nodeValue 0 [0, values 0, values 2])
        rw [← h.1, ← hHeadCode]
        exact term_reject [] free head hTerm
      | some headTerm =>
        refine ⟨node 2 [.var 0, .var 1, .var 3] , List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
        change Rejection rules (nodeValue 2 [values 0, values 1, values 3])
        rw [← h.1, ← hCount, ← hTailCode]
        apply parameters_reject free sorts tail
        rw [SyntaxParameters.terms.eq_def] at hBad
        cases hTail : SyntaxParameters.terms free sorts tail with
        | none => rfl
        | some args => simp [hTerm, hTail] at hBad
termination_by sizeOf input

theorem envelope_reject (count : Nat) (input : Tree) (hBad : SyntaxParameters.decode count input = none) :
    Rejection rules (envelopeRow count input) := by
  apply Rejection.of_tagged heads_tagged 3 [count, treeValue input]
  intro rule hRule values _ hHead _
  rw [rulesFor_three] at hRule
  have hRule := List.mem_singleton.mp hRule
  subst rule
  dsimp only [envelopeRule] at values hHead ⊢
  have h := ((nodeValue_eq_iff 3 3 [count, treeValue input]
    [values 0, nodeValue 0 [nodeValue (values 1) [] , values 2]]).mp hHead).2
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨contextTree, termsTree, rfl, hContext, hTermsCode⟩ := treeValue_node_two h.2
  have hContext := treeValue_node_zero hContext
  subst contextTree
  refine ⟨node 2 [.var 1, .var 0, .var 2] , List.mem_cons_self, ?_⟩
  change Rejection rules (nodeValue 2 [values 1, values 0, values 2])
  rw [← h.1, ← hTermsCode]
  have hTermsBad : SyntaxParameters.terms (List.replicate (values 1) SetSort.set)
      (List.replicate count SetSort.set) termsTree = none := by
    cases hTerms : SyntaxParameters.terms (List.replicate (values 1) SetSort.set)
        (List.replicate count SetSort.set) termsTree with
    | none => rfl
    | some args => simp [SyntaxParameters.decode, SyntaxDecode.context, scalar, hTerms] at hBad
  simpa only [parameterRow, List.length_replicate] using parameters_reject _ _ termsTree hTermsBad

end YesMetaZFC.Automation.ObjectTermSyntax
