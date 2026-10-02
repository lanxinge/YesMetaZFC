import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaTable
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaClosure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCodeBounds
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectArithmeticTerm

/-! # 模式流水线的固定槽位和量词见证界 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaJoin
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn ObjectCodeBounds ObjectArithmeticTerm
set_option autoImplicit false

def site (kind : SchemaTemplate.Kind) (i : Fin 3) : SchemaRename.Site :=
  match kind with
  | .separation => .separation
  | .collection => if i.val = 0 then .collectionPremise else .collectionImage
  | .replacement => if i.val = 0 then .replacementFirst else if i.val = 1 then .replacementSecond else .replacementImage

def rename (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) (i : Fin 3) : Option Tree :=
  SchemaRename.run ((site kind i).targetDepth n) ((site kind i).table n) input

def assemble (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) : Option Tree := do
  let first ← rename kind n input 0
  let second ← rename kind n input 1
  let third ← rename kind n input 2
  pure (SchemaClosure.close n (SchemaTemplate.build kind (SchemaTemplate.three first second third)))

theorem assemble_eq (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) :
    assemble kind n input = SchemaClosure.run kind n input := by
  cases kind
  · cases h : SchemaRename.run (SchemaRename.Site.separation.targetDepth n) (SchemaRename.Site.separation.table n) input <;>
      simp [assemble, rename, site, SchemaClosure.run, SchemaTemplate.run, SchemaTemplate.renameInputs,
        h] <;> rfl
  · cases h0 : SchemaRename.run (SchemaRename.Site.collectionPremise.targetDepth n) (SchemaRename.Site.collectionPremise.table n) input <;>
      cases h1 : SchemaRename.run (SchemaRename.Site.collectionImage.targetDepth n) (SchemaRename.Site.collectionImage.table n) input <;>
      simp [assemble, rename, site, SchemaClosure.run, SchemaTemplate.run, SchemaTemplate.renameInputs,
        h0, h1] <;> rfl
  · cases h0 : SchemaRename.run (SchemaRename.Site.replacementFirst.targetDepth n) (SchemaRename.Site.replacementFirst.table n) input <;>
      cases h1 : SchemaRename.run (SchemaRename.Site.replacementSecond.targetDepth n) (SchemaRename.Site.replacementSecond.table n) input <;>
      cases h2 : SchemaRename.run (SchemaRename.Site.replacementImage.targetDepth n) (SchemaRename.Site.replacementImage.table n) input <;>
      simp [assemble, rename, site, SchemaClosure.run, SchemaTemplate.run, SchemaTemplate.renameInputs, h0, h1, h2]

/-- 所有槽位确实来自同一正文的指定重命名位置。 -/
def CorrectInputs (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) (bodies : Fin 3 → Tree) : Prop :=
  ∀ i, rename kind n input i = some (bodies i)

theorem run_of_inputs (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) (bodies : Fin 3 → Tree)
    (h : CorrectInputs kind n input bodies) :
    SchemaClosure.run kind n input = some (SchemaClosure.close n (SchemaTemplate.build kind bodies)) := by
  rw [← assemble_eq, assemble, h 0]
  dsimp only [Bind.bind, Option.bind]
  rw [h 1]
  dsimp only [Bind.bind, Option.bind]
  rw [h 2]
  have hBodies : SchemaTemplate.three (bodies 0) (bodies 1) (bodies 2) = bodies := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> rfl
  simp only [hBodies, Pure.pure]

theorem inputs_of_run (kind : SchemaTemplate.Kind) (n : Nat) (input output : Tree)
    (h : SchemaClosure.run kind n input = some output) :
    ∃ bodies, CorrectInputs kind n input bodies ∧ SchemaClosure.close n (SchemaTemplate.build kind bodies) = output := by
  rw [← assemble_eq] at h
  unfold assemble at h
  obtain ⟨first, hFirst, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨second, hSecond, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨third, hThird, h⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨SchemaTemplate.three first second third, ?_, Option.some.inj h⟩
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact hFirst
  · exact hSecond
  · exact hThird

theorem table_bound (which : SchemaRename.Site) (n : Nat) :
    listValue (which.table n) ≤ tableBoundValue n := by
  have h := list_bound (n + 8) (by omega) (which.table n) (by
    intro value hValue
    have hv := (List.all_eq_true.mp (which.table_valid n)) value hValue
    have hv : value < which.targetDepth n := of_decide_eq_true hv
    cases which <;> simp only [SchemaRename.Site.targetDepth] at hv <;> omega)
  apply Nat.le_trans h
  apply Nat.pow_le_pow_right (by omega)
  apply Nat.pow_le_pow_right (by decide)
  rw [SchemaRename.Site.table_length]
  cases which <;> simp [SchemaRename.Site.sourceDepth]

theorem core_le_close (count core : Nat) : core ≤ ObjectUnaryIteration.value 9 count core := by
  induction count with
  | zero => exact Nat.le_refl _
  | succ count ih => exact Nat.le_trans ih (node_field_le 9 _ _ List.mem_cons_self)

theorem body_le_core (kind : SchemaTemplate.Kind) (n : Nat) (input : Tree) (bodies : Fin 3 → Tree)
    (h : CorrectInputs kind n input bodies) (i : Fin 3) :
    treeValue (bodies i) ≤ treeValue (SchemaTemplate.build kind bodies) := by
  rw [SchemaTemplate.build, ObjectTreeTemplate.Template.value_plug]
  have hSame : ∀ a b, site kind a = site kind b → bodies a = bodies b := by
    intro a b hSite
    have he : rename kind n input a = rename kind n input b := by simp only [rename, hSite]
    rw [h a, h b] at he
    exact Option.some.inj he
  cases kind
  · have he := hSame i 0 rfl
    rw [he]
    exact SchemaTemplate.separation.expr.variable_le (fun j => treeValue (bodies j)) (index := 0) (by decide)
  · by_cases hi : i.val = 0
    · have hi : i = 0 := Fin.ext hi
      subst i
      exact SchemaTemplate.collection.expr.variable_le (fun j => treeValue (bodies j)) (index := 0) (by decide)
    · have he := hSame i 1 (by simp [site, hi])
      rw [he]
      exact SchemaTemplate.collection.expr.variable_le (fun j => treeValue (bodies j)) (index := 1) (by decide)
  · apply SchemaTemplate.replacement.expr.variable_le (fun j => treeValue (bodies j)) (index := i)
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> decide

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaJoin
