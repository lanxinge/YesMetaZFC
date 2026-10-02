import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectPacketDerives

/-! # 传输图排除任意自然数候选码

结构码不是满射。先按数码严格下降排除非树、非列表候选，再使用规范包的唯一性；
因此对象存在量词不必预先假设中间码已经来自一棵元层树。
-/
namespace YesMetaZFC.Automation.ObjectPacket
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding NatPacket IntrinsicQuotation ProofCode
open ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

mutual
theorem malformed_tree_reject (code tail output : Nat)
    (hBad : ¬ ∃ input : Tree, treeValue input = code) :
    Rejection rules (nodeValue 3 [code, tail, output]) := by
  apply Rejection.of_tagged heads_tagged 3 [code, tail, output]
  intro rule hRule values _ hHead _
  rw [rulesFor_three] at hRule
  have hRule := List.mem_singleton.mp hRule
  subst rule
  dsimp only [treeRule] at values hHead ⊢
  have h := ((nodeValue_eq_iff 3 3 [code, tail, output]
    [godel_pair_value (values 0) (values 1) + 1, values 2, values 3]).mp hHead).2
  simp only [List.cons.injEq, and_true] at h
  refine ⟨node (n := 7) 4 [.var 1, .var 4, .var 2, .var 5] , List.mem_cons_self, ?_⟩
  apply malformed_forest_reject (values 1)
  intro hForest
  obtain ⟨children, hChildren⟩ := hForest
  apply hBad
  exact ⟨.node (values 0) children, by rw [tree_code, hChildren, h.1]⟩
termination_by code
decreasing_by
  dsimp only [treeRule] at values
  have hEq := ((nodeValue_eq_iff 3 3 [code, tail, output]
    [godel_pair_value (values 0) (values 1) + 1, values 2, values 3]).mp hHead).2
  simp only [List.cons.injEq, and_true] at hEq
  have hLe := right_le_godel_pair_value (values 0) (values 1)
  omega

theorem malformed_forest_reject (code count tail output : Nat)
    (hBad : ¬ ∃ input : List Tree, forestCode input = code) :
    Rejection rules (nodeValue 4 [code, count, tail, output]) := by
  classical
  apply Rejection.of_tagged heads_tagged 4 [code, count, tail, output]
  intro rule hRule values _ hHead _
  rw [rulesFor_four] at hRule
  rcases List.mem_cons.mp hRule with rfl | hRule
  · dsimp only [forestNil] at values hHead ⊢
    have h := ((nodeValue_eq_iff 4 4 [code, count, tail, output]
      [listValue [] , 0, values 0, values 0]).mp hHead).2
    simp only [List.cons.injEq, and_true] at h
    exact False.elim (hBad ⟨[] , h.1.symm⟩)
  · have hRule := List.mem_singleton.mp hRule
    subst rule
    dsimp only [forestCons] at values hHead ⊢
    have h := ((nodeValue_eq_iff 4 4 [code, count, tail, output]
      [godel_pair_value 1 (godel_pair_value (values 0) (values 1)) + 1,
        values 2 + 1, values 3, values 4]).mp hHead).2
    simp only [List.cons.injEq, and_true] at h
    by_cases hTree : ∃ input : Tree, treeValue input = values 0
    · refine ⟨node (n := 6) 4 [.var 1, .var 2, .var 3, .var 5] , List.mem_cons_self, ?_⟩
      apply malformed_forest_reject (values 1)
      intro hForest
      obtain ⟨head, hHead⟩ := hTree
      obtain ⟨rest, hRest⟩ := hForest
      apply hBad
      exact ⟨head :: rest, by rw [forestCode_cons, hHead, hRest, h.1]⟩
    · refine ⟨node (n := 6) 3 [.var 0, .var 5, .var 4] , List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      exact malformed_tree_reject (values 0) _ _ hTree
termination_by code
decreasing_by
  all_goals
    dsimp only [forestCons] at values
    have hEq := ((nodeValue_eq_iff 4 4 [code, count, tail, output]
      [godel_pair_value 1 (godel_pair_value (values 0) (values 1)) + 1,
        values 2 + 1, values 3, values 4]).mp hHead).2
    simp only [List.cons.injEq, and_true] at hEq
    have hOuter := right_le_godel_pair_value 1 (godel_pair_value (values 0) (values 1))
    have hLeft := left_le_godel_pair_value (values 0) (values 1)
    have hRight := right_le_godel_pair_value (values 0) (values 1)
    omega
end

theorem packet_number_reject (packet code : Nat)
    (hBad : (NatPacket.decode packet).map treeValue ≠ some code) :
    Rejection rules (nodeValue 5 [packet, code]) := by
  classical
  by_cases hTree : ∃ input : Tree, treeValue input = code
  · obtain ⟨input, rfl⟩ := hTree
    apply packet_reject packet input
    intro hEncode
    apply hBad
    rw [(NatPacket.decode_eq_some_iff packet input).mpr hEncode]
    rfl
  · apply Rejection.of_tagged heads_tagged 5 [packet, code]
    intro rule hRule values _ hHead _
    rw [rulesFor_five] at hRule
    have hRule := List.mem_singleton.mp hRule
    subst rule
    dsimp only [packetRule] at values hHead ⊢
    have h := ((nodeValue_eq_iff 5 5 [packet, code] [values 1, values 0]).mp hHead).2
    simp only [List.cons.injEq, and_true] at h
    refine ⟨node (n := 3) 3 [.var 0, .literal 1, .var 2] , List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 3 [values 0, 1, values 2])
    rw [← h.2]
    exact malformed_tree_reject code _ _ hTree

theorem negative_number {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (packet code : Nat) (h : (NatPacket.decode packet).map treeValue ≠ some code) :
    Derives T [] (¬ₘ condition (numₘ(packet)) (numₘ(code) : Code)) :=
  ObjectHorn.transport_negative rules (FirstOrder.Derives.eq_symm (node_evaluate C 5 [packet, code]))
    (ObjectHorn.negative C A (packet_number_reject packet code h))

end YesMetaZFC.Automation.ObjectPacket
