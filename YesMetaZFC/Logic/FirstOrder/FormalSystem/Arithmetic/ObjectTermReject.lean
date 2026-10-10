import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectTermAccept

/-! # 项识别的递归拒绝证书

由实际解码失败逐个排除所有匹配规则。反演只依据原始树码单射，
不假定轨迹中的对象见证来自宿主解析结果。
-/
namespace YesMetaZFC.Automation.ObjectTermSyntax
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT NatPacket IntrinsicQuotation ObjectHorn ProofCode
set_option autoImplicit false

theorem forest_cons_shape (input : List Tree) (head tail : Nat)
    (h : listValue (input.map treeValue) = godel_pair_value 1 (godel_pair_value head tail) + 1) :
    ∃ first rest, input = first :: rest ∧ treeValue first = head ∧ listValue (rest.map treeValue) = tail := by
  cases input with
  | nil =>
    have hTag := (godel_pair_value_eq_iff.mp (Nat.add_right_cancel h)).1
    cases hTag
  | cons first rest =>
    have hFields := godel_pair_value_eq_iff.mp
      (godel_pair_value_eq_iff.mp (Nat.add_right_cancel h)).2
    exact ⟨first, rest, rfl, hFields⟩

theorem application_shape (input : Tree) (symbol fields : Nat)
    (h : treeValue input = godel_pair_value 2
      (godel_pair_value 1 (godel_pair_value (treeValue (leaf symbol)) fields) + 1) + 1) :
    ∃ children, input = .node 2 (leaf symbol :: children) ∧ listValue (children.map treeValue) = fields := by
  cases input with
  | node tag children =>
    rw [treeValue_node] at h
    have hPair := godel_pair_value_eq_iff.mp (Nat.add_right_cancel h)
    rcases hPair with ⟨rfl, hFields⟩
    obtain ⟨first, rest, rfl, hFirst, hRest⟩ := forest_cons_shape children _ _ hFields
    have hFirst := treeValue_injective hFirst
    subst first
    exact ⟨rest, rfl, hRest⟩

private theorem variable_matched (isFree : Bool) (bound free : SetContext) (input : Tree)
    (values : Fin 3 → Nat) (hHead : termRow bound.length free.length input = (variableRule isFree).head.eval values)
    (hGuard : values 2 < values (if isFree then 1 else 0))
    (hBad : SyntaxDecode.term bound free input = none) : False := by
  have h := ((nodeValue_eq_iff 0 0 [bound.length, free.length, treeValue input]
    [values 0, values 1, nodeValue (if isFree then 1 else 0) [nodeValue (values 2) []]]).mp hHead).2
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨indexTree, rfl, hIndex⟩ := treeValue_node_one h.2.2
  have hIndex := treeValue_node_zero hIndex
  subst indexTree
  cases isFree with
  | false =>
    obtain ⟨entry, hEntry⟩ := SyntaxDecode.variable_exists bound (values 2) (by rw [h.1]; exact hGuard)
    rw [SyntaxDecode.term.eq_def] at hBad
    simp [scalar, hEntry] at hBad
  | true =>
    obtain ⟨entry, hEntry⟩ := SyntaxDecode.variable_exists free (values 2) (by rw [h.2.1]; exact hGuard)
    rw [SyntaxDecode.term.eq_def] at hBad
    simp [scalar, hEntry] at hBad

mutual
theorem term_reject (bound free : SetContext) (input : Tree) (hBad : SyntaxDecode.term bound free input = none) :
    Rejection rules (termRow bound.length free.length input) := by
  apply Rejection.of_tagged heads_tagged 0 [bound.length, free.length, treeValue input]
  intro rule hRule values _ hHead hGuards
  rw [rulesFor_zero] at hRule
  simp only [termRules, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with (rfl | rfl) | hRule
  · exact False.elim (variable_matched false bound free input values hHead (hGuards _ List.mem_cons_self) hBad)
  · exact False.elim (variable_matched true bound free input values hHead (hGuards _ List.mem_cons_self) hBad)
  · obtain ⟨symbol, _, rfl⟩ := List.mem_map.mp hRule
    dsimp only [applicationRule] at values hHead ⊢
    have h := ((nodeValue_eq_iff 0 0 [bound.length, free.length, treeValue input]
      [values 0, values 1, godel_pair_value 2
        (godel_pair_value 1 (godel_pair_value (treeValue (leaf symbol.ctorIdx)) (values 2)) + 1) + 1]).mp hHead).2
    simp only [List.cons.injEq, and_true] at h
    obtain ⟨children, rfl, hFields⟩ := application_shape input symbol.ctorIdx (values 2) h.2.2
    refine ⟨node 1 [.var 0, .var 1, .literal (signature.funcDomain symbol).length, .var 2] , List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 1 [values 0, values 1, (signature.funcDomain symbol).length, values 2])
    rw [← h.1, ← h.2.1, ← hFields]
    apply arguments_reject bound free (signature.funcDomain symbol) children
    cases hArgs : SyntaxDecode.argumentsList bound free (signature.funcDomain symbol) children with
    | none => rfl
    | some args =>
      rw [SyntaxDecode.term.eq_def] at hBad
      simp [scalar, leaf, SyntaxEncode.function_roundtrip, hArgs] at hBad
termination_by sizeOf input

theorem arguments_reject (bound free sorts : SetContext) (input : List Tree)
    (hBad : SyntaxDecode.argumentsList bound free sorts input = none) :
    Rejection rules (argumentRow bound.length free.length sorts.length input) := by
  apply Rejection.of_tagged heads_tagged 1 [bound.length, free.length, sorts.length, listValue (input.map treeValue)]
  intro rule hRule values _ hHead _
  rw [rulesFor_one] at hRule
  rcases List.mem_cons.mp hRule with rfl | hRule
  · dsimp only [nilRule] at values hHead ⊢
    have h := ((nodeValue_eq_iff 1 1 [bound.length, free.length, sorts.length, listValue (input.map treeValue)]
      [values 0, values 1, 0, listValue []]).mp hHead).2
    simp only [List.cons.injEq, and_true] at h
    have hSorts := List.length_eq_zero_iff.mp h.2.2.1
    have hInput : input = [] := by
      have hMap := (listValue_eq_iff _ _).mp h.2.2.2
      simpa using hMap
    subst sorts
    subst input
    rw [SyntaxDecode.argumentsList.eq_def] at hBad
    cases hBad
  · have hRule := List.mem_singleton.mp hRule
    subst rule
    dsimp only [consRule] at values hHead ⊢
    have h := ((nodeValue_eq_iff 1 1 [bound.length, free.length, sorts.length, listValue (input.map treeValue)]
      [values 0, values 1, values 2 + 1, godel_pair_value 1 (godel_pair_value (values 3) (values 4)) + 1]).mp hHead).2
    simp only [List.cons.injEq, and_true] at h
    obtain ⟨head, tail, rfl, hHeadCode, hTailCode⟩ := forest_cons_shape input _ _ h.2.2.2
    cases sorts with
    | nil => simp at h
    | cons sort sorts =>
      cases sort
      have hCount : sorts.length = values 2 := by simpa using h.2.2.1
      cases hTerm : SyntaxDecode.term bound free head with
      | none =>
        refine ⟨node 0 [.var 0, .var 1, .var 3] , List.mem_cons_self, ?_⟩
        change Rejection rules (nodeValue 0 [values 0, values 1, values 3])
        rw [← h.1, ← h.2.1, ← hHeadCode]
        exact term_reject bound free head hTerm
      | some headTerm =>
        refine ⟨node 1 [.var 0, .var 1, .var 2, .var 4] , List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
        change Rejection rules (nodeValue 1 [values 0, values 1, values 2, values 4])
        rw [← h.1, ← h.2.1, ← hCount, ← hTailCode]
        apply arguments_reject bound free sorts tail
        rw [SyntaxDecode.argumentsList.eq_def] at hBad
        cases hTail : SyntaxDecode.argumentsList bound free sorts tail with
        | none => rfl
        | some args => simp [hTerm, hTail] at hBad
termination_by sizeOf input
end

end YesMetaZFC.Automation.ObjectTermSyntax
