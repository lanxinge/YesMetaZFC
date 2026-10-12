import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaRenameObject

/-! # 重命名辅助关系对任意错误输出的拒绝证书 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Rename
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation ProofCode
open _root_.YesMetaZFC.Automation ObjectHorn
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

@[simp] theorem rulesFor_zero : rulesFor rules 0 = [lookupZero, lookupSucc] := rfl
@[simp] theorem rulesFor_one : rulesFor rules 1 = [indexBase, indexZero, indexSucc] := rfl
@[simp] theorem rulesFor_two : rulesFor rules 2 =
    [constantRule 0, constantRule 1, binaryRule 2 3, binaryRule 3 3, unaryRule 4 false,
      binaryRule 5 2, binaryRule 6 2, binaryRule 7 2, binaryRule 8 2,
      unaryRule 9 true, unaryRule 10 true, binaryRule 11 3] := rfl
@[simp] theorem rulesFor_three : rulesFor rules 3 = [termRule] := rfl
@[simp] theorem rulesFor_four : rulesFor rules 4 = [validNil, validCons] := rfl
@[simp] theorem rulesFor_five : rulesFor rules 5 = [runRule] := rfl

theorem lookup_reject (table : List Nat) (index output : Nat) (hBad : table[index]? ≠ some output) :
    Rejection rules (lookupRow table index output) := by
  apply Rejection.of_tagged heads_tagged 0 [listValue table, index, output]
  intro rule hRule values _ hHead _
  rw [rulesFor_zero] at hRule
  rcases List.mem_cons.mp hRule with rfl | hRule
  · dsimp only [lookupZero] at values hHead ⊢
    have hFields := ((nodeValue_eq_iff 0 0 [listValue table, index, output]
      [godel_pair_value 1 (godel_pair_value (values 0) (values 1)) + 1, 0, values 0]).mp hHead).2
    simp only [List.cons.injEq, and_true] at hFields
    rcases hFields with ⟨hTable, hIndex, hOutput⟩
    obtain ⟨tail, hTable, _⟩ := listValue_cons hTable
    exact False.elim (hBad (by rw [hTable, hIndex, hOutput]; rfl))
  · have hRule := List.mem_singleton.mp hRule
    subst rule
    dsimp only [lookupSucc] at values hHead ⊢
    have hFields := ((nodeValue_eq_iff 0 0 [listValue table, index, output]
      [godel_pair_value 1 (godel_pair_value (values 0) (values 1)) + 1, values 2 + 1, values 3]).mp hHead).2
    simp only [List.cons.injEq, and_true] at hFields
    rcases hFields with ⟨hTable, hIndex, hOutput⟩
    obtain ⟨tail, hTable, hTail⟩ := listValue_cons hTable
    subst table
    refine ⟨SchemaObjectGraph.node (n := 4) 0 [.var 1, .var 2, .var 3] , List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 0 [values 1, values 2, values 3])
    rw [← hTail]
    apply lookup_reject tail (values 2) (values 3)
    intro hGood
    apply hBad
    rw [hIndex, hOutput]
    exact hGood
termination_by table.length

theorem index_reject (table : List Nat) (cutoff index output : Nat)
    (hBad : (lifted cutoff table)[index]? ≠ some output) :
    Rejection rules (indexRow table cutoff index output) := by
  apply Rejection.of_tagged heads_tagged 1 [listValue table, cutoff, index, output]
  intro rule hRule values _ hHead _
  rw [rulesFor_one] at hRule
  rcases List.mem_cons.mp hRule with rfl | hRule
  · dsimp only [indexBase] at values hHead ⊢
    have hFields := ((nodeValue_eq_iff 1 1 [listValue table, cutoff, index, output]
      [values 0, 0, values 1, values 2]).mp hHead).2
    simp only [List.cons.injEq, and_true] at hFields
    rcases hFields with ⟨hTable, hCutoff, hIndex, hOutput⟩
    refine ⟨SchemaObjectGraph.node (n := 3) 0 [.var 0, .var 1, .var 2] , List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 0 [values 0, values 1, values 2])
    rw [← hTable, ← hIndex, ← hOutput]
    exact lookup_reject table index output (by simpa [hCutoff, lifted] using hBad)
  · rcases List.mem_cons.mp hRule with rfl | hRule
    · dsimp only [indexZero] at values hHead ⊢
      have hFields := ((nodeValue_eq_iff 1 1 [listValue table, cutoff, index, output]
        [values 0, values 1 + 1, 0, 0]).mp hHead).2
      simp only [List.cons.injEq, and_true] at hFields
      exact False.elim (hBad (by rw [hFields.2.1, hFields.2.2.1, hFields.2.2.2]; rfl))
    · have hRule := List.mem_singleton.mp hRule
      subst rule
      dsimp only [indexSucc] at values hHead ⊢
      have hFields := ((nodeValue_eq_iff 1 1 [listValue table, cutoff, index, output]
        [values 0, values 1 + 1, values 2 + 1, values 3 + 1]).mp hHead).2
      simp only [List.cons.injEq, and_true] at hFields
      rcases hFields with ⟨hTable, hCutoff, hIndex, hOutput⟩
      refine ⟨SchemaObjectGraph.node (n := 4) 1 [.var 0, .var 1, .var 2, .var 3] , List.mem_cons_self, ?_⟩
      change Rejection rules (nodeValue 1 [values 0, values 1, values 2, values 3])
      rw [← hTable]
      apply index_reject table (values 1) (values 2) (values 3)
      intro hGood
      apply hBad
      rw [hCutoff, hIndex, hOutput]
      simpa [lifted, SchemaRename.lift, List.getElem?_map] using congrArg (Option.map Nat.succ) hGood
termination_by cutoff
decreasing_by omega

theorem valid_reject (target : Nat) (table : List Nat) (hBad : SchemaRename.valid target table = false) :
    Rejection rules (validRow target table) := by
  apply Rejection.of_tagged heads_tagged 4 [target, listValue table]
  intro rule hRule values _ hHead hGuards
  rw [rulesFor_four] at hRule
  rcases List.mem_cons.mp hRule with rfl | hRule
  · dsimp only [validNil] at values hHead ⊢
    have hFields := ((nodeValue_eq_iff 4 4 [target, listValue table]
      [values 0, listValue []]).mp hHead).2
    have hEmpty := (listValue_eq_iff table []).mp (List.cons.inj (List.cons.inj hFields).2).1
    subst table
    cases hBad
  · have hRule := List.mem_singleton.mp hRule
    subst rule
    dsimp only [validCons] at values hHead hGuards ⊢
    have hFields := ((nodeValue_eq_iff 4 4 [target, listValue table]
      [values 0, godel_pair_value 1 (godel_pair_value (values 1) (values 2)) + 1]).mp hHead).2
    simp only [List.cons.injEq, and_true] at hFields
    obtain ⟨tail, hTable, hTail⟩ := listValue_cons hFields.2
    subst table
    have hGuard := hGuards (.var 1, .var 0) List.mem_cons_self
    change values 1 < values 0 at hGuard
    have hLt : values 1 < target := hFields.1.symm ▸ hGuard
    refine ⟨SchemaObjectGraph.node (n := 3) 4 [.var 0, .var 2] , List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 4 [values 0, values 2])
    rw [← hFields.1, ← hTail]
    apply valid_reject target tail
    simpa only [SchemaRename.valid, List.all_cons, decide_eq_true hLt, Bool.true_and] using hBad
termination_by table.length

theorem term_reject (table : List Nat) (cutoff : Nat) (input output : Tree)
    (hBad : SchemaRename.term (lifted cutoff table) input ≠ some output) :
    Rejection rules (termRow table cutoff input output) := by
  apply Rejection.of_tagged heads_tagged 3 [listValue table, cutoff, treeValue input, treeValue output]
  intro rule hRule values _ hHead _
  rw [rulesFor_three] at hRule
  have hRule := List.mem_singleton.mp hRule
  subst rule
  dsimp only [termRule] at values hHead ⊢
  have hFields := ((nodeValue_eq_iff 3 3 [listValue table, cutoff, treeValue input, treeValue output]
    [values 0, values 1, nodeValue 0 [nodeValue (values 2) []] , nodeValue 0 [nodeValue (values 3) []]]).mp hHead).2
  simp only [List.cons.injEq, and_true] at hFields
  rcases hFields with ⟨hTable, hCutoff, hInput, hOutput⟩
  have hInput : input = .node 0 [leaf (values 2)] := treeValue_injective hInput
  have hOutput : output = .node 0 [leaf (values 3)] := treeValue_injective hOutput
  refine ⟨SchemaObjectGraph.node (n := 4) 1 [.var 0, .var 1, .var 2, .var 3] , List.mem_cons_self, ?_⟩
  change Rejection rules (nodeValue 1 [values 0, values 1, values 2, values 3])
  rw [← hTable, ← hCutoff]
  apply index_reject table cutoff (values 2) (values 3)
  intro hGood
  apply hBad
  rw [hInput, hOutput]
  simp [SchemaRename.term, leaf, hGood]

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Rename
