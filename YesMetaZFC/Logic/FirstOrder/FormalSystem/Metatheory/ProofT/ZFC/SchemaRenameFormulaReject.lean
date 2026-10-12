import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaRenameObjectReject

/-! # 正文重命名对任意不匹配输出的递归拒绝 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Rename
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

/-- 通过原树数值码的单射，构造树的可判定相等；只在下述有限分支中使用。 -/
private def treeDecidableEq (left right : Tree) : Decidable (left = right) :=
  match Nat.decEq (treeValue left) (treeValue right) with
  | .isTrue h => .isTrue (treeValue_injective h)
  | .isFalse h => .isFalse (fun hEq => h (congrArg treeValue hEq))

private theorem atom_success (tag : Nat) (table : List Nat) (left right leftOut rightOut : Tree)
    (hTag : tag = 2 ∨ tag = 3 ∨ tag = 11)
    (hLeft : SchemaRename.term table left = some leftOut) (hRight : SchemaRename.term table right = some rightOut) :
    SchemaRename.formula table (.node tag [left, right]) = some (.node tag [leftOut, rightOut]) := by
  rcases hTag with rfl | rfl | rfl
  all_goals rw [SchemaRename.formula.eq_def]; simp [hLeft, hRight]

private theorem binary_success (tag : Nat) (table : List Nat) (left right leftOut rightOut : Tree)
    (hTag : tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8)
    (hLeft : SchemaRename.formula table left = some leftOut) (hRight : SchemaRename.formula table right = some rightOut) :
    SchemaRename.formula table (.node tag [left, right]) = some (.node tag [leftOut, rightOut]) := by
  rcases hTag with rfl | rfl | rfl | rfl
  all_goals rw [SchemaRename.formula.eq_def]; simp [hLeft, hRight]

private theorem unary_success (tag : Nat) (binder : Bool) (table : List Nat) (cutoff : Nat) (input output : Tree)
    (hTag : (tag = 4 ∧ binder = false) ∨ (tag = 9 ∧ binder = true) ∨ (tag = 10 ∧ binder = true))
    (hBody : SchemaRename.formula (lifted (if binder then cutoff + 1 else cutoff) table) input = some output) :
    SchemaRename.formula (lifted cutoff table) (.node tag [input]) = some (.node tag [output]) := by
  rcases hTag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    rw [SchemaRename.formula.eq_def]
    exact Option.bind_eq_some_iff.mpr ⟨output, hBody, rfl⟩

private theorem reject_atom_matched (tag : Nat) (table : List Nat) (cutoff : Nat) (input output : Tree)
    (values : Fin 6 → Nat) (hTag : tag = 2 ∨ tag = 3 ∨ tag = 11)
    (hHead : formulaRow table cutoff input output = nodeValue 2 [values 0, values 1,
      nodeValue tag [values 2, values 3] , nodeValue tag [values 4, values 5]])
    (hBad : SchemaRename.formula (lifted cutoff table) input ≠ some output) :
    ∃ premise, premise ∈ (binaryRule tag 3).premises ∧ Rejection rules (premise.eval values) := by
  letI : DecidableEq Tree := treeDecidableEq
  have hFields := ((nodeValue_eq_iff 2 2 [listValue table, cutoff, treeValue input, treeValue output]
    [values 0, values 1, nodeValue tag [values 2, values 3] , nodeValue tag [values 4, values 5]]).mp hHead).2
  simp only [List.cons.injEq, and_true] at hFields
  rcases hFields with ⟨hTable, hCutoff, hInput, hOutput⟩
  obtain ⟨left, right, rfl, hLeft, hRight⟩ := treeValue_node_two hInput
  obtain ⟨leftOut, rightOut, rfl, hLeftOut, hRightOut⟩ := treeValue_node_two hOutput
  by_cases hLeftRun : SchemaRename.term (lifted cutoff table) left = some leftOut
  · refine ⟨SchemaObjectGraph.node (n := 6) 3 [.var 0, .var 1, .var 3, .var 5] ,
      List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 3 [values 0, values 1, values 3, values 5])
    rw [← hTable, ← hCutoff, ← hRight, ← hRightOut]
    apply term_reject table cutoff right rightOut
    intro hRightRun
    exact hBad (atom_success tag _ _ _ _ _ hTag hLeftRun hRightRun)
  · refine ⟨SchemaObjectGraph.node (n := 6) 3 [.var 0, .var 1, .var 2, .var 4] , List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 3 [values 0, values 1, values 2, values 4])
    rw [← hTable, ← hCutoff, ← hLeft, ← hLeftOut]
    exact term_reject table cutoff left leftOut hLeftRun

private theorem reject_binary_matched (tag : Nat) (table : List Nat) (cutoff : Nat) (input output : Tree)
    (values : Fin 6 → Nat) (hTag : tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8)
    (hHead : formulaRow table cutoff input output = nodeValue 2 [values 0, values 1,
      nodeValue tag [values 2, values 3] , nodeValue tag [values 4, values 5]])
    (hBad : SchemaRename.formula (lifted cutoff table) input ≠ some output)
    (ih : ∀ nextCutoff child childOut, sizeOf child < sizeOf input →
      SchemaRename.formula (lifted nextCutoff table) child ≠ some childOut →
      Rejection rules (formulaRow table nextCutoff child childOut)) :
    ∃ premise, premise ∈ (binaryRule tag 2).premises ∧ Rejection rules (premise.eval values) := by
  letI : DecidableEq Tree := treeDecidableEq
  have hFields := ((nodeValue_eq_iff 2 2 [listValue table, cutoff, treeValue input, treeValue output]
    [values 0, values 1, nodeValue tag [values 2, values 3] , nodeValue tag [values 4, values 5]]).mp hHead).2
  simp only [List.cons.injEq, and_true] at hFields
  rcases hFields with ⟨hTable, hCutoff, hInput, hOutput⟩
  obtain ⟨left, right, rfl, hLeft, hRight⟩ := treeValue_node_two hInput
  obtain ⟨leftOut, rightOut, rfl, hLeftOut, hRightOut⟩ := treeValue_node_two hOutput
  by_cases hLeftRun : SchemaRename.formula (lifted cutoff table) left = some leftOut
  · refine ⟨SchemaObjectGraph.node (n := 6) 2 [.var 0, .var 1, .var 3, .var 5] ,
      List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 2 [values 0, values 1, values 3, values 5])
    rw [← hTable, ← hCutoff, ← hRight, ← hRightOut]
    apply ih cutoff right rightOut (by simp; omega)
    intro hRightRun
    exact hBad (binary_success tag _ _ _ _ _ hTag hLeftRun hRightRun)
  · refine ⟨SchemaObjectGraph.node (n := 6) 2 [.var 0, .var 1, .var 2, .var 4] , List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 2 [values 0, values 1, values 2, values 4])
    rw [← hTable, ← hCutoff, ← hLeft, ← hLeftOut]
    exact ih cutoff left leftOut (by simp; omega) hLeftRun

private theorem reject_unary_matched (tag : Nat) (binder : Bool) (table : List Nat) (cutoff : Nat)
    (input output : Tree) (values : Fin 4 → Nat)
    (hTag : (tag = 4 ∧ binder = false) ∨ (tag = 9 ∧ binder = true) ∨ (tag = 10 ∧ binder = true))
    (hHead : formulaRow table cutoff input output = nodeValue 2 [values 0, values 1,
      nodeValue tag [values 2] , nodeValue tag [values 3]])
    (hBad : SchemaRename.formula (lifted cutoff table) input ≠ some output)
    (ih : ∀ nextCutoff child childOut, sizeOf child < sizeOf input →
      SchemaRename.formula (lifted nextCutoff table) child ≠ some childOut →
      Rejection rules (formulaRow table nextCutoff child childOut)) :
    ∃ premise, premise ∈ (unaryRule tag binder).premises ∧ Rejection rules (premise.eval values) := by
  have hFields := ((nodeValue_eq_iff 2 2 [listValue table, cutoff, treeValue input, treeValue output]
    [values 0, values 1, nodeValue tag [values 2] , nodeValue tag [values 3]]).mp hHead).2
  simp only [List.cons.injEq, and_true] at hFields
  rcases hFields with ⟨hTable, hCutoff, hInput, hOutput⟩
  obtain ⟨body, rfl, hBody⟩ := treeValue_node_one hInput
  obtain ⟨bodyOut, rfl, hBodyOut⟩ := treeValue_node_one hOutput
  have hChildBad : SchemaRename.formula (lifted (if binder then cutoff + 1 else cutoff) table) body ≠ some bodyOut :=
    fun hGood => hBad (unary_success tag binder table cutoff body bodyOut hTag hGood)
  have hReject := ih (if binder then cutoff + 1 else cutoff) body bodyOut (by simp; omega) hChildBad
  refine ⟨SchemaObjectGraph.node (n := 4) 2
    [.var 0, if binder then .succ (.var 1) else .var 1, .var 2, .var 3] , List.mem_cons_self, ?_⟩
  cases binder
  · change Rejection rules (nodeValue 2 [values 0, values 1, values 2, values 3])
    rw [← hTable, ← hCutoff, ← hBody, ← hBodyOut]
    exact hReject
  · change Rejection rules (nodeValue 2 [values 0, values 1 + 1, values 2, values 3])
    rw [← hTable, ← hCutoff, ← hBody, ← hBodyOut]
    exact hReject

theorem formula_reject (table : List Nat) (cutoff : Nat) (input output : Tree)
    (hBad : SchemaRename.formula (lifted cutoff table) input ≠ some output) :
    Rejection rules (formulaRow table cutoff input output) := by
  apply Rejection.of_tagged heads_tagged 2 [listValue table, cutoff, treeValue input, treeValue output]
  intro rule hRule values _ hHead _
  have ih : ∀ nextCutoff child childOut, sizeOf child < sizeOf input →
      SchemaRename.formula (lifted nextCutoff table) child ≠ some childOut →
      Rejection rules (formulaRow table nextCutoff child childOut) := by
    intro nextCutoff child childOut _ hChild
    exact formula_reject table nextCutoff child childOut hChild
  rw [rulesFor_two] at hRule
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [constantRule, binaryRule, unaryRule] at values hHead ⊢
  · have hFields := ((nodeValue_eq_iff 2 2 [listValue table, cutoff, treeValue input, treeValue output]
      [values 0, values 1, nodeValue 0 [] , nodeValue 0 []]).mp hHead).2
    simp only [List.cons.injEq, and_true] at hFields
    have hInput := treeValue_node_zero hFields.2.2.1
    have hOutput := treeValue_node_zero hFields.2.2.2
    apply False.elim
    apply hBad
    rw [hInput, hOutput, SchemaRename.formula.eq_def]
    rfl
  · have hFields := ((nodeValue_eq_iff 2 2 [listValue table, cutoff, treeValue input, treeValue output]
      [values 0, values 1, nodeValue 1 [] , nodeValue 1 []]).mp hHead).2
    simp only [List.cons.injEq, and_true] at hFields
    have hInput := treeValue_node_zero hFields.2.2.1
    have hOutput := treeValue_node_zero hFields.2.2.2
    apply False.elim
    apply hBad
    rw [hInput, hOutput, SchemaRename.formula.eq_def]
    rfl
  · exact reject_atom_matched 2 table cutoff input output values (by simp) hHead hBad
  · exact reject_atom_matched 3 table cutoff input output values (by simp) hHead hBad
  · exact reject_unary_matched 4 false table cutoff input output values (by simp) hHead hBad ih
  · exact reject_binary_matched 5 table cutoff input output values (by simp) hHead hBad ih
  · exact reject_binary_matched 6 table cutoff input output values (by simp) hHead hBad ih
  · exact reject_binary_matched 7 table cutoff input output values (by simp) hHead hBad ih
  · exact reject_binary_matched 8 table cutoff input output values (by simp) hHead hBad ih
  · exact reject_unary_matched 9 true table cutoff input output values (by simp) hHead hBad ih
  · exact reject_unary_matched 10 true table cutoff input output values (by simp) hHead hBad ih
  · exact reject_atom_matched 11 table cutoff input output values (by simp) hHead hBad
termination_by sizeOf input

theorem run_reject (target : Nat) (table : List Nat) (input output : Tree)
    (hBad : SchemaRename.run target table input ≠ some output) : Rejection rules (runRow target table input output) := by
  apply Rejection.of_tagged heads_tagged 5 [target, listValue table, treeValue input, treeValue output]
  intro rule hRule values _ hHead _
  rw [rulesFor_five] at hRule
  have hRule := List.mem_singleton.mp hRule
  subst rule
  dsimp only [runRule] at values hHead ⊢
  have hFields := ((nodeValue_eq_iff 5 5 [target, listValue table, treeValue input, treeValue output]
    [values 0, values 1, values 2, values 3]).mp hHead).2
  simp only [List.cons.injEq, and_true] at hFields
  rcases hFields with ⟨hTarget, hTable, hInput, hOutput⟩
  by_cases hValid : SchemaRename.valid target table = true
  · refine ⟨SchemaObjectGraph.node (n := 4) 2 [.var 1, .literal 0, .var 2, .var 3] ,
      List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 2 [values 1, 0, values 2, values 3])
    rw [← hTable, ← hInput, ← hOutput]
    apply formula_reject table 0 input output
    simpa [SchemaRename.run, hValid, lifted] using hBad
  · refine ⟨SchemaObjectGraph.node (n := 4) 4 [.var 0, .var 1] , List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 4 [values 0, values 1])
    rw [← hTarget, ← hTable]
    exact valid_reject target table (Bool.eq_false_iff.mpr hValid)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Rename
