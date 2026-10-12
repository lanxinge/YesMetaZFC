import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaJoinGraph

/-! # 中间码矩阵的正负推导与真实模式流水线规格 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaJoin
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn ObjectArithmeticTerm
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def witnesses (kind : SchemaTemplate.Kind) (n : Nat) (bodies : Fin 3 → Tree) (i : Fin 7) : Nat :=
  ([listValue ((site kind 0).table n), listValue ((site kind 1).table n), listValue ((site kind 2).table n),
    treeValue (bodies 0), treeValue (bodies 1), treeValue (bodies 2), treeValue (SchemaTemplate.build kind bodies)])[i.val]

@[simp] theorem witnesses_table (kind : SchemaTemplate.Kind) (n : Nat) (bodies : Fin 3 → Tree) (i : Fin 3) :
    witnesses kind n bodies (tableSlot i) = listValue ((site kind i).table n) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rfl

@[simp] theorem witnesses_body (kind : SchemaTemplate.Kind) (n : Nat) (bodies : Fin 3 → Tree) (i : Fin 3) :
    witnesses kind n bodies (bodySlot i) = treeValue (bodies i) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rfl

@[simp] theorem witnesses_core (kind : SchemaTemplate.Kind) (n : Nat) (bodies : Fin 3 → Tree) :
    witnesses kind n bodies 6 = treeValue (SchemaTemplate.build kind bodies) := rfl

theorem witnesses_bound (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) (bodies : Fin 3 → Tree)
    (h : CorrectInputs kind n input bodies) (i : Fin 7) :
    witnesses kind n bodies i < limitValue n (treeValue (SchemaClosure.close n (SchemaTemplate.build kind bodies))) := by
  have ht : ∀ j : Fin 3, witnesses kind n bodies (tableSlot j) < limitValue n (treeValue (SchemaClosure.close n (SchemaTemplate.build kind bodies))) := by
    intro j
    rw [witnesses_table]
    exact Nat.lt_succ_of_le (Nat.le_trans (table_bound _ n) (ProofCode.left_le_godel_pair_value _ _))
  have hc : treeValue (SchemaTemplate.build kind bodies) ≤ treeValue (SchemaClosure.close n (SchemaTemplate.build kind bodies)) := by
    rw [SchemaClosure.close, ObjectUnaryIteration.tree_value]
    exact core_le_close _ _
  have hb : ∀ j : Fin 3, witnesses kind n bodies (bodySlot j) < limitValue n (treeValue (SchemaClosure.close n (SchemaTemplate.build kind bodies))) := by
    intro j
    rw [witnesses_body]
    exact Nat.lt_succ_of_le (Nat.le_trans (body_le_core kind n input bodies h j)
      (Nat.le_trans hc (ProofCode.right_le_godel_pair_value _ _)))
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ht 0
  · exact ht 1
  · exact ht 2
  · exact hb 0
  · exact hb 1
  · exact hb 2
  · exact Nat.lt_succ_of_le (Nat.le_trans hc (ProofCode.right_le_godel_pair_value _ _))

theorem matrix_positive (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) (bodies : Fin 3 → Tree)
    (h : CorrectInputs kind n input bodies) :
    Derives intrinsic_zfc_theory [] (matrix kind (fun i => (numₘ(witnesses kind n bodies i) : Code))
      (numₘ(n)) (numₘ(treeValue input)) (numₘ(treeValue (SchemaClosure.close n (SchemaTemplate.build kind bodies))))) := by
  apply allOf_intro
  intro φ hφ
  simp only [checks, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (rfl | rfl)
  · rw [witnesses_table]
    exact SchemaTable.positive _ _
  · rw [target_numeral, witnesses_table, witnesses_body]
    exact SchemaObjectGraph.Rename.positive _ _ _ _ (h i)
  · simp only [witnesses_body, witnesses_core]
    exact SchemaTemplate.positive kind _ _ (ObjectTreeTemplate.Template.value_plug _ _).symm
  · rw [witnesses_core]
    exact SchemaClosure.positive n _ _ (ObjectUnaryIteration.tree_value 9 n _).symm

private theorem table_mem (kind : SchemaTemplate.Kind) (env : Fin 7 → Code) (n input output : Code) (i : Fin 3) :
    SchemaTable.condition (numₘ((SchemaTable.entry (site kind i)).tag)) n (env (tableSlot i)) ∈ checks kind env n input output :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))

private theorem rename_mem (kind : SchemaTemplate.Kind) (env : Fin 7 → Code) (n input output : Code) (i : Fin 3) :
    SchemaObjectGraph.Rename.condition (target (site kind i) n) (env (tableSlot i)) input (env (bodySlot i)) ∈ checks kind env n input output :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩))

private theorem core_mem (kind : SchemaTemplate.Kind) (env : Fin 7 → Code) (n input output : Code) :
    SchemaTemplate.condition (numₘ(kind.tag)) (fun i => env (bodySlot i)) (env 6) ∈ checks kind env n input output :=
  List.mem_append_right _ List.mem_cons_self

private theorem close_mem (kind : SchemaTemplate.Kind) (env : Fin 7 → Code) (n input output : Code) :
    SchemaClosure.condition n (env 6) output ∈ checks kind env n input output :=
  List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- 此处的中间见证是任意自然数，不要求预先解码成表或正文。 -/
theorem matrix_negative (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) (output : Nat)
    (hBad : (SchemaClosure.run kind n input).map treeValue ≠ some output) (values : Fin 7 → Nat) :
    Derives intrinsic_zfc_theory [] (¬ₘ matrix kind (fun i => (numₘ(values i) : Code))
      (numₘ(n)) (numₘ(treeValue input)) (numₘ(output))) := by
  by_cases hTables : ∀ i, listValue ((site kind i).table n) = values (tableSlot i)
  · by_cases hRenames : ∀ i, (rename kind n input i).map treeValue = some (values (bodySlot i))
    · have hExists : ∀ i, ∃ body, rename kind n input i = some body ∧ treeValue body = values (bodySlot i) :=
        fun i => Option.map_eq_some_iff.mp (hRenames i)
      obtain ⟨body0, hBody0, hValue0⟩ := hExists 0
      obtain ⟨body1, hBody1, hValue1⟩ := hExists 1
      obtain ⟨body2, hBody2, hValue2⟩ := hExists 2
      let bodies : Fin 3 → Tree := SchemaTemplate.three body0 body1 body2
      have hBodies : CorrectInputs kind n input bodies := by
        intro i
        exact Fin.cases hBody0 (Fin.cases hBody1 (Fin.cases hBody2 (fun j => Fin.elim0 j))) i
      have hValues : ∀ i, treeValue (bodies i) = values (bodySlot i) := by
        intro i
        exact Fin.cases hValue0 (Fin.cases hValue1 (Fin.cases hValue2 (fun j => Fin.elim0 j))) i
      by_cases hCore : kind.shape.expr.eval (fun i => values (bodySlot i)) = values 6
      · apply allOf_negative_of_member (close_mem kind _ _ _ _)
        apply SchemaClosure.negative
        intro hClosed
        apply hBad
        rw [run_of_inputs kind n input bodies hBodies, Option.map_some]
        congr 1
        rw [SchemaClosure.close, ObjectUnaryIteration.tree_value, SchemaTemplate.build,
          ObjectTreeTemplate.Template.value_plug]
        simp only [hValues]
        exact hCore ▸ hClosed
      · exact allOf_negative_of_member (core_mem kind _ _ _ _) (SchemaTemplate.negative kind _ _ hCore)
    · obtain ⟨i, hi⟩ : ∃ i, (rename kind n input i).map treeValue ≠ some (values (bodySlot i)) := Decidable.not_forall.mp hRenames
      apply allOf_negative_of_member (rename_mem kind _ _ _ _ i)
      rw [target_numeral, ← hTables i]
      exact SchemaObjectGraph.Rename.negative_number _ _ _ _ hi
  · obtain ⟨i, hi⟩ : ∃ i, listValue ((site kind i).table n) ≠ values (tableSlot i) := Decidable.not_forall.mp hTables
    exact allOf_negative_of_member (table_mem kind _ _ _ _ i) (SchemaTable.negative _ _ _ hi)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaJoin
