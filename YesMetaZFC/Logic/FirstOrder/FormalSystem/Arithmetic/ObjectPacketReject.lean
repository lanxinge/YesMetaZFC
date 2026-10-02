import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectPacketTree

/-! # 树与子树列表对任意错误传输前缀的拒绝证书 -/
namespace YesMetaZFC.Automation.ObjectPacket
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem ProofT NatPacket IntrinsicQuotation ProofCode
open ObjectHorn
set_option autoImplicit false

mutual
theorem tree_reject (input : Tree) (tail output : Nat) (hBad : tree input tail ≠ output) :
    Rejection rules (nodeValue 3 [treeValue input, tail, output]) := by
  cases input with
  | node tag children =>
    apply Rejection.of_tagged heads_tagged 3 [treeValue (.node tag children), tail, output]
    intro rule hRule values _ hHead _
    rw [rulesFor_three] at hRule
    have hRule := List.mem_singleton.mp hRule
    subst rule
    dsimp only [treeRule] at values hHead ⊢
    have h := ((nodeValue_eq_iff 3 3 [treeValue (.node tag children), tail, output]
      [godel_pair_value (values 0) (values 1) + 1, values 2, values 3]).mp hHead).2
    simp only [List.cons.injEq, and_true] at h
    have hCode := h.1
    rw [tree_code] at hCode
    have hData := godel_pair_value_eq_iff.mp (Nat.add_right_cancel hCode)
    by_cases hForest : values 4 = children.length ∧ forest children (values 2) = values 5
    · by_cases hToken : token (values 4) (values 5) = values 6
      · refine ⟨node (n := 7) 2 [.var 0, .var 6, .var 3] ,
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
        apply token_reject
        intro hGood
        apply hBad
        rw [tree_node, hData.1, h.2.1, h.2.2, ← hForest.1, hForest.2, hToken]
        exact hGood
      · refine ⟨node (n := 7) 2 [.var 4, .var 5, .var 6] , List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
        exact token_reject _ _ _ hToken
    · refine ⟨node (n := 7) 4 [.var 1, .var 4, .var 2, .var 5] , List.mem_cons_self, ?_⟩
      change Rejection rules (nodeValue 4 [values 1, values 4, values 2, values 5])
      rw [← hData.2]
      exact forest_reject children _ _ _ hForest
termination_by sizeOf input

theorem forest_reject (input : List Tree) (count tail output : Nat)
    (hBad : ¬ (count = input.length ∧ forest input tail = output)) :
    Rejection rules (nodeValue 4 [forestCode input, count, tail, output]) := by
  apply Rejection.of_tagged heads_tagged 4 [forestCode input, count, tail, output]
  intro rule hRule values _ hHead _
  rw [rulesFor_four] at hRule
  rcases List.mem_cons.mp hRule with rfl | hRule
  · dsimp only [forestNil] at values hHead ⊢
    have h := ((nodeValue_eq_iff 4 4 [forestCode input, count, tail, output]
      [listValue [] , 0, values 0, values 0]).mp hHead).2
    simp only [List.cons.injEq, and_true] at h
    cases input with
    | nil => exact False.elim (hBad ⟨h.2.1, h.2.2.1.trans h.2.2.2.symm⟩)
    | cons head rest =>
      have hCode := h.1
      have hTag := (godel_pair_value_eq_iff.mp (Nat.add_right_cancel hCode)).1
      cases hTag
  · have hRule := List.mem_singleton.mp hRule
    subst rule
    dsimp only [forestCons] at values hHead ⊢
    have h := ((nodeValue_eq_iff 4 4 [forestCode input, count, tail, output]
      [godel_pair_value 1 (godel_pair_value (values 0) (values 1)) + 1,
        values 2 + 1, values 3, values 4]).mp hHead).2
    simp only [List.cons.injEq, and_true] at h
    cases input with
    | nil =>
      have hCode := h.1
      have hTag := (godel_pair_value_eq_iff.mp (Nat.add_right_cancel hCode)).1
      cases hTag
    | cons head rest =>
      have hCode := h.1
      have hData := godel_pair_value_eq_iff.mp
        (godel_pair_value_eq_iff.mp (Nat.add_right_cancel hCode)).2
      by_cases hRest : values 2 = rest.length ∧ forest rest (values 3) = values 5
      · refine ⟨node (n := 6) 3 [.var 0, .var 5, .var 4] , List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
        change Rejection rules (nodeValue 3 [values 0, values 5, values 4])
        rw [← hData.1]
        apply tree_reject head
        intro hGood
        apply hBad
        constructor
        · simpa only [List.length_cons, hRest.1] using h.2.1
        · rw [forest_cons, h.2.2.1, h.2.2.2, hRest.2]
          exact hGood
      · refine ⟨node (n := 6) 4 [.var 1, .var 2, .var 3, .var 5] , List.mem_cons_self, ?_⟩
        change Rejection rules (nodeValue 4 [values 1, values 2, values 3, values 5])
        rw [← hData.2]
        exact forest_reject rest _ _ _ hRest
termination_by sizeOf input
end

end YesMetaZFC.Automation.ObjectPacket
