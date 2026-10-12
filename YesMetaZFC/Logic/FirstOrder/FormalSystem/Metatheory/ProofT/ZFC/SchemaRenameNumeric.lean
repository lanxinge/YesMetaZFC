import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaRenameDerives

/-! # 重命名负向表示覆盖任意自然数候选码 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Rename
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def numberRow (relation : Nat) (table : List Nat) (cutoff : Nat) (input : Tree) (output : Nat) : Nat :=
  nodeValue relation [listValue table, cutoff, treeValue input, output]

theorem term_number_reject (table : List Nat) (cutoff : Nat) (input : Tree) (output : Nat)
    (hBad : (SchemaRename.term (lifted cutoff table) input).map treeValue ≠ some output) :
    Rejection rules (numberRow 3 table cutoff input output) := by
  apply Rejection.of_tagged heads_tagged 3 [listValue table, cutoff, treeValue input, output]
  intro rule hRule values _ hHead _
  rw [rulesFor_three] at hRule
  have hRule := List.mem_singleton.mp hRule
  subst rule
  dsimp only [termRule] at values hHead ⊢
  have h := (nodeValue_eq_iff 3 3 [listValue table, cutoff, treeValue input, output]
    [values 0, values 1, nodeValue 0 [nodeValue (values 2) []] , nodeValue 0 [nodeValue (values 3) []]]).mp hHead |>.2
  simp only [List.cons.injEq, and_true] at h
  have hInput : input = .node 0 [leaf (values 2)] := treeValue_injective h.2.2.1
  refine ⟨SchemaObjectGraph.node (n := 4) 1 [.var 0, .var 1, .var 2, .var 3] , List.mem_cons_self, ?_⟩
  change Rejection rules (nodeValue 1 [values 0, values 1, values 2, values 3])
  rw [← h.1, ← h.2.1]
  apply index_reject
  intro hGood
  apply hBad
  rw [hInput, h.2.2.2]
  simp [SchemaRename.term, leaf, hGood]

private theorem binary_result (tag : Nat) (atomic : Bool) (table : List Nat) (left right : Tree)
    (a b : Nat)
    (hTag : if atomic then tag = 2 ∨ tag = 3 ∨ tag = 11 else tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8)
    (ha : ((if atomic then SchemaRename.term else SchemaRename.formula) table left).map treeValue = some a)
    (hb : ((if atomic then SchemaRename.term else SchemaRename.formula) table right).map treeValue = some b) :
    (SchemaRename.formula table (.node tag [left, right])).map treeValue = some (nodeValue tag [a, b]) := by
  obtain ⟨leftOut, hLeft, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨rightOut, hRight, rfl⟩ := Option.map_eq_some_iff.mp hb
  cases atomic
  · rcases hTag with rfl | rfl | rfl | rfl
    all_goals simp only [Bool.false_eq_true, ite_false] at hLeft hRight
    all_goals rw [SchemaRename.formula.eq_def]; simp [hLeft, hRight]
  · rcases hTag with rfl | rfl | rfl
    all_goals simp only [ite_true] at hLeft hRight
    all_goals rw [SchemaRename.formula.eq_def]; simp [hLeft, hRight]

private theorem unary_result (tag : Nat) (binder : Bool) (table : List Nat) (cutoff : Nat)
    (body : Tree) (out : Nat)
    (hTag : (tag = 4 ∧ binder = false) ∨ (tag = 9 ∧ binder = true) ∨ (tag = 10 ∧ binder = true))
    (hBody : (SchemaRename.formula (lifted (if binder then cutoff + 1 else cutoff) table) body).map treeValue = some out) :
    (SchemaRename.formula (lifted cutoff table) (.node tag [body])).map treeValue = some (nodeValue tag [out]) := by
  obtain ⟨bodyOut, hRun, rfl⟩ := Option.map_eq_some_iff.mp hBody
  rcases hTag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp only [Bool.false_eq_true, ite_false, ite_true, lifted] at hRun
  all_goals rw [SchemaRename.formula.eq_def]; simp [hRun]

private theorem binary_number_matched (tag : Nat) (atomic : Bool) (table : List Nat) (cutoff : Nat)
    (input : Tree) (output : Nat) (values : Fin 6 → Nat)
    (hTag : if atomic then tag = 2 ∨ tag = 3 ∨ tag = 11 else tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8)
    (hHead : numberRow 2 table cutoff input output = nodeValue 2 [values 0, values 1,
      nodeValue tag [values 2, values 3] , nodeValue tag [values 4, values 5]])
    (hBad : (SchemaRename.formula (lifted cutoff table) input).map treeValue ≠ some output)
    (ih : ∀ nextCutoff child childOut, sizeOf child < sizeOf input →
      (SchemaRename.formula (lifted nextCutoff table) child).map treeValue ≠ some childOut →
      Rejection rules (numberRow 2 table nextCutoff child childOut)) :
    ∃ premise, premise ∈ (binaryRule tag (if atomic then 3 else 2)).premises ∧ Rejection rules (premise.eval values) := by
  have h := (nodeValue_eq_iff 2 2 [listValue table, cutoff, treeValue input, output]
    [values 0, values 1, nodeValue tag [values 2, values 3] , nodeValue tag [values 4, values 5]]).mp hHead |>.2
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨left, right, rfl, hLeft, hRight⟩ := treeValue_node_two h.2.2.1
  have rejectChild : ∀ child out, sizeOf child < sizeOf (Tree.node tag [left, right]) →
      ((if atomic then SchemaRename.term else SchemaRename.formula) (lifted cutoff table) child).map treeValue ≠ some out →
      Rejection rules (numberRow (if atomic then 3 else 2) table cutoff child out) := by
    intro child out hSize hFail
    cases atomic
    · exact ih cutoff child out hSize hFail
    · exact term_number_reject table cutoff child out hFail
  by_cases hLeftRun : ((if atomic then SchemaRename.term else SchemaRename.formula)
      (lifted cutoff table) left).map treeValue = some (values 4)
  · refine ⟨SchemaObjectGraph.node (n := 6) (if atomic then 3 else 2) [.var 0, .var 1, .var 3, .var 5] ,
      List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue (if atomic then 3 else 2) [values 0, values 1, values 3, values 5])
    rw [← h.1, ← h.2.1, ← hRight]
    apply rejectChild right (values 5) (by simp; omega)
    intro hRightRun
    apply hBad
    rw [h.2.2.2]
    exact binary_result tag atomic _ _ _ _ _ hTag hLeftRun hRightRun
  · refine ⟨SchemaObjectGraph.node (n := 6) (if atomic then 3 else 2) [.var 0, .var 1, .var 2, .var 4] ,
      List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue (if atomic then 3 else 2) [values 0, values 1, values 2, values 4])
    rw [← h.1, ← h.2.1, ← hLeft]
    exact rejectChild left (values 4) (by simp; omega) hLeftRun

private theorem unary_number_matched (tag : Nat) (binder : Bool) (table : List Nat) (cutoff : Nat)
    (input : Tree) (output : Nat) (values : Fin 4 → Nat)
    (hTag : (tag = 4 ∧ binder = false) ∨ (tag = 9 ∧ binder = true) ∨ (tag = 10 ∧ binder = true))
    (hHead : numberRow 2 table cutoff input output = nodeValue 2 [values 0, values 1,
      nodeValue tag [values 2] , nodeValue tag [values 3]])
    (hBad : (SchemaRename.formula (lifted cutoff table) input).map treeValue ≠ some output)
    (ih : ∀ nextCutoff child childOut, sizeOf child < sizeOf input →
      (SchemaRename.formula (lifted nextCutoff table) child).map treeValue ≠ some childOut →
      Rejection rules (numberRow 2 table nextCutoff child childOut)) :
    ∃ premise, premise ∈ (unaryRule tag binder).premises ∧ Rejection rules (premise.eval values) := by
  have h := (nodeValue_eq_iff 2 2 [listValue table, cutoff, treeValue input, output]
    [values 0, values 1, nodeValue tag [values 2] , nodeValue tag [values 3]]).mp hHead |>.2
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨body, rfl, hBody⟩ := treeValue_node_one h.2.2.1
  have hFail : (SchemaRename.formula (lifted (if binder then cutoff + 1 else cutoff) table) body).map treeValue ≠ some (values 3) := by
    intro hGood
    apply hBad
    rw [h.2.2.2]
    exact unary_result tag binder table cutoff body (values 3) hTag hGood
  have hReject := ih (if binder then cutoff + 1 else cutoff) body (values 3) (by simp; omega) hFail
  refine ⟨SchemaObjectGraph.node (n := 4) 2
    [.var 0, if binder then .succ (.var 1) else .var 1, .var 2, .var 3] , List.mem_cons_self, ?_⟩
  cases binder
  · change Rejection rules (nodeValue 2 [values 0, values 1, values 2, values 3])
    rw [← h.1, ← h.2.1, ← hBody]
    exact hReject
  · change Rejection rules (nodeValue 2 [values 0, values 1 + 1, values 2, values 3])
    rw [← h.1, ← h.2.1, ← hBody]
    exact hReject

theorem formula_number_reject (table : List Nat) (cutoff : Nat) (input : Tree) (output : Nat)
    (hBad : (SchemaRename.formula (lifted cutoff table) input).map treeValue ≠ some output) :
    Rejection rules (numberRow 2 table cutoff input output) := by
  apply Rejection.of_tagged heads_tagged 2 [listValue table, cutoff, treeValue input, output]
  intro rule hRule values _ hHead _
  have ih : ∀ nextCutoff child childOut, sizeOf child < sizeOf input →
      (SchemaRename.formula (lifted nextCutoff table) child).map treeValue ≠ some childOut →
      Rejection rules (numberRow 2 table nextCutoff child childOut) := by
    intro nextCutoff child childOut _ hChild
    exact formula_number_reject table nextCutoff child childOut hChild
  rw [rulesFor_two] at hRule
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [constantRule, binaryRule, unaryRule] at values hHead ⊢
  · have h := (nodeValue_eq_iff 2 2 [listValue table, cutoff, treeValue input, output]
      [values 0, values 1, nodeValue 0 [] , nodeValue 0 []]).mp hHead |>.2
    simp only [List.cons.injEq, and_true] at h
    have hInput := treeValue_node_zero h.2.2.1
    exact False.elim (hBad (by rw [hInput, h.2.2.2, SchemaRename.formula.eq_def]; rfl))
  · have h := (nodeValue_eq_iff 2 2 [listValue table, cutoff, treeValue input, output]
      [values 0, values 1, nodeValue 1 [] , nodeValue 1 []]).mp hHead |>.2
    simp only [List.cons.injEq, and_true] at h
    have hInput := treeValue_node_zero h.2.2.1
    exact False.elim (hBad (by rw [hInput, h.2.2.2, SchemaRename.formula.eq_def]; rfl))
  · exact binary_number_matched 2 true table cutoff input output values (by simp) hHead hBad ih
  · exact binary_number_matched 3 true table cutoff input output values (by simp) hHead hBad ih
  · exact unary_number_matched 4 false table cutoff input output values (by simp) hHead hBad ih
  · exact binary_number_matched 5 false table cutoff input output values (by simp) hHead hBad ih
  · exact binary_number_matched 6 false table cutoff input output values (by simp) hHead hBad ih
  · exact binary_number_matched 7 false table cutoff input output values (by simp) hHead hBad ih
  · exact binary_number_matched 8 false table cutoff input output values (by simp) hHead hBad ih
  · exact unary_number_matched 9 true table cutoff input output values (by simp) hHead hBad ih
  · exact unary_number_matched 10 true table cutoff input output values (by simp) hHead hBad ih
  · exact binary_number_matched 11 true table cutoff input output values (by simp) hHead hBad ih
termination_by sizeOf input

theorem run_number_reject (target : Nat) (table : List Nat) (input : Tree) (output : Nat)
    (hBad : (SchemaRename.run target table input).map treeValue ≠ some output) :
    Rejection rules (nodeValue 5 [target, listValue table, treeValue input, output]) := by
  apply Rejection.of_tagged heads_tagged 5 [target, listValue table, treeValue input, output]
  intro rule hRule values _ hHead _
  rw [rulesFor_five] at hRule
  have hRule := List.mem_singleton.mp hRule
  subst rule
  dsimp only [runRule] at values hHead ⊢
  have h := (nodeValue_eq_iff 5 5 [target, listValue table, treeValue input, output]
    [values 0, values 1, values 2, values 3]).mp hHead |>.2
  simp only [List.cons.injEq, and_true] at h
  by_cases hValid : SchemaRename.valid target table = true
  · refine ⟨SchemaObjectGraph.node (n := 4) 2 [.var 1, .literal 0, .var 2, .var 3] ,
      List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 2 [values 1, 0, values 2, values 3])
    rw [← h.2.1, ← h.2.2.1, ← h.2.2.2]
    apply formula_number_reject
    simpa [SchemaRename.run, hValid, lifted] using hBad
  · refine ⟨SchemaObjectGraph.node (n := 4) 4 [.var 0, .var 1] , List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 4 [values 0, values 1])
    rw [← h.1, ← h.2.1]
    exact valid_reject target table (Bool.eq_false_iff.mpr hValid)

theorem negative_number (target : Nat) (table : List Nat) (input : Tree) (output : Nat)
    (h : (SchemaRename.run target table input).map treeValue ≠ some output) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition (numₘ(target)) (numₘ(listValue table))
      (numₘ(treeValue input)) (numₘ(output) : Code)) :=
  ObjectHorn.transport_negative rules (FirstOrder.Derives.eq_symm
    (node_evaluate intrinsic_zfc_certificate_core 5 [target, listValue table, treeValue input, output]))
    (ObjectHorn.negative intrinsic_zfc_certificate_core intrinsic_zfc_arithmetic_support.toArithmeticSupport
      (run_number_reject target table input output h))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Rename
