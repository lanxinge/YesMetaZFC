import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectTreeTemplate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaRenameInstances

/-!
# 分离、收集与替换的固定核心模板

三个槽位依次接收各模式的重命名正文；分离只使用第零槽，收集使用前两槽。
模板包含模式自身的量词和有界量词展开，不包含随后按参数数目添加的全称闭合。
本层保持 Project 的成员、外延相等原子及十二类正文标签，不使用旧 Hilbert quote。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaTemplate
open Nonlogical.BasicSetTheory NatPacket
open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.Automation.ObjectTreeTemplate
set_option autoImplicit false

inductive Kind where
  | separation | collection | replacement
  deriving DecidableEq, Repr

/-- 此标签只分派模板，不改变 ZFC 公理证书的标签与公理表。 -/
def Kind.tag : Kind → Nat
  | .separation => 0
  | .collection => 1
  | .replacement => 2

def Kind.sourceDepth (kind : Kind) (n : Nat) : Nat :=
  match kind with
  | .separation => n + 1
  | .collection | .replacement => n + 2

def boundTerm (index : Nat) : Template 3 := .unary 0 (.leaf index)
def member (left right : Nat) : Template 3 := .binary 2 (boundTerm left) (boundTerm right)

def separation : Template 3 :=
  .unary 9 <| .unary 10 <| .unary 9 <|
    .binary 8 (member 0 1) (.binary 5 (member 0 2) (.hole 0))

def collection : Template 3 :=
  .unary 9 <| .binary 7
    (.unary 9 (.binary 7 (member 0 1) (.unary 10 (.hole 0))))
    (.unary 10 (.unary 9 (.binary 7 (member 0 2)
      (.unary 10 (.binary 5 (member 0 2) (.hole 1))))))

def replacement : Template 3 :=
  .binary 7
    (.unary 9 (.unary 9 (.unary 9 (.binary 7
      (.binary 5 (.hole 0) (.hole 1)) (.binary 3 (boundTerm 1) (boundTerm 0))))))
    (.unary 9 (.unary 10 (.unary 9 (.binary 8 (member 0 1)
      (.unary 10 (.binary 5 (member 0 3) (.hole 2)))))))

def Kind.shape : Kind → Template 3
  | .separation => SchemaTemplate.separation
  | .collection => SchemaTemplate.collection
  | .replacement => SchemaTemplate.replacement

def build (kind : Kind) (inputs : Fin 3 → Tree) : Tree := kind.shape.plug inputs

def one (body : Tree) : Fin 3 → Tree := fun _ => body
def two (first second : Tree) : Fin 3 → Tree := fun i => if i.val = 0 then first else second
def three (first second third : Tree) : Fin 3 → Tree :=
  fun i => if i.val = 0 then first else if i.val = 1 then second else third

/-- 与实际模式定义的对应是任意参数数目的语法等式，不依赖样例计算。 -/
theorem separation_core {n : Nat} (schema : Project.UnarySchema n) :
    build .separation (one (ProjectEncode.formula
      (schema.body.rename BoundEmbedding.unaryUnderTwo))) =
      ProjectEncode.formula (Axioms.Schema.separationCore schema) := by
  rfl

theorem collection_core {n : Nat} (schema : Project.BinarySchema n) :
    build .collection (two
      (ProjectEncode.formula (schema.body.rename BoundEmbedding.binaryUnderOne))
      (ProjectEncode.formula (schema.body.rename BoundEmbedding.binaryUnderTwo))) =
      ProjectEncode.formula (Axioms.Schema.collectionCore schema) := by
  rfl

theorem replacement_core {n : Nat} (schema : Project.BinarySchema n) :
    build .replacement (three
      (ProjectEncode.formula (schema.body.rename Axioms.Schema.ReplacementEmbedding.firstOutput))
      (ProjectEncode.formula (schema.body.rename Axioms.Schema.ReplacementEmbedding.secondOutput))
      (ProjectEncode.formula (schema.body.rename Axioms.Schema.ReplacementEmbedding.imageBody))) =
      ProjectEncode.formula (Axioms.Schema.replacementCore schema) := by
  rfl

/-- 先消费已有的六个实际重命名位置，再由固定模板装配核心树。 -/
def renameInputs (kind : Kind) (n : Nat) (input : Tree) : Option (Fin 3 → Tree) := do
  let rename (site : SchemaRename.Site) :=
    SchemaRename.run (site.targetDepth n) (site.table n) input
  match kind with
  | .separation =>
    let body ← rename .separation
    pure (one body)
  | .collection =>
    let first ← rename .collectionPremise
    let second ← rename .collectionImage
    pure (two first second)
  | .replacement =>
    let first ← rename .replacementFirst
    let second ← rename .replacementSecond
    let third ← rename .replacementImage
    pure (three first second third)

def run (kind : Kind) (n : Nat) (input : Tree) : Option Tree :=
  (renameInputs kind n input).map (build kind)

theorem run_eq_some_iff (kind : Kind) (n : Nat) (input output : Tree) :
    run kind n input = some output ↔
      ∃ inputs, renameInputs kind n input = some inputs ∧ build kind inputs = output := by
  exact Option.map_eq_some_iff

theorem run_separation {n : Nat} (schema : Project.UnarySchema n) :
    run .separation n (ProjectEncode.formula schema.body) =
      some (ProjectEncode.formula (Axioms.Schema.separationCore schema)) := by
  dsimp only [run, renameInputs, Bind.bind]
  have h := SchemaRename.Site.run_encode .separation n schema.body schema.freeClosed
  dsimp only [SchemaRename.Site.sourceDepth] at h
  rw [h]
  exact congrArg some (separation_core schema)

theorem run_collection {n : Nat} (schema : Project.BinarySchema n) :
    run .collection n (ProjectEncode.formula schema.body) =
      some (ProjectEncode.formula (Axioms.Schema.collectionCore schema)) := by
  dsimp only [run, renameInputs, Bind.bind]
  have h := SchemaRename.Site.run_encode .collectionPremise n schema.body schema.freeClosed
  dsimp only [SchemaRename.Site.sourceDepth] at h
  rw [h]
  dsimp only [Bind.bind, Option.bind]
  have h := SchemaRename.Site.run_encode .collectionImage n schema.body schema.freeClosed
  dsimp only [SchemaRename.Site.sourceDepth] at h
  rw [h]
  exact congrArg some (collection_core schema)

theorem run_replacement {n : Nat} (schema : Project.BinarySchema n) :
    run .replacement n (ProjectEncode.formula schema.body) =
      some (ProjectEncode.formula (Axioms.Schema.replacementCore schema)) := by
  dsimp only [run, renameInputs, Bind.bind]
  have h := SchemaRename.Site.run_encode .replacementFirst n schema.body schema.freeClosed
  dsimp only [SchemaRename.Site.sourceDepth] at h
  rw [h]
  dsimp only [Bind.bind, Option.bind]
  have h := SchemaRename.Site.run_encode .replacementSecond n schema.body schema.freeClosed
  dsimp only [SchemaRename.Site.sourceDepth] at h
  rw [h]
  dsimp only [Bind.bind, Option.bind]
  have h := SchemaRename.Site.run_encode .replacementImage n schema.body schema.freeClosed
  dsimp only [SchemaRename.Site.sourceDepth] at h
  rw [h]
  exact congrArg some (replacement_core schema)

private theorem site_none (site : SchemaRename.Site) (n : Nat) (input : Tree)
    (h : SchemaBody.check (site.sourceDepth n) input = false) :
    SchemaRename.run (site.targetDepth n) (site.table n) input = none := by
  have hSome := site.run_isSome n input
  cases hRun : SchemaRename.run (site.targetDepth n) (site.table n) input with
  | none => rfl
  | some output =>
    rw [hRun, h] at hSome
    contradiction

/-- 装配步骤不修复非法正文，也不引入新的接受条件；源作用域保持精确。 -/
theorem run_isSome (kind : Kind) (n : Nat) (input : Tree) :
    (run kind n input).isSome = SchemaBody.check (kind.sourceDepth n) input := by
  cases kind with
  | separation =>
    change (run .separation n input).isSome = SchemaBody.check (n + 1) input
    cases h : SchemaBody.check (n + 1) input with
    | false =>
      have hNone := site_none .separation n input h
      simp [run, renameInputs, hNone]
    | true =>
      obtain ⟨body, hClosed, rfl⟩ := (SchemaBody.check_eq_true_iff _ _).mp h
      rw [run_separation ⟨body, hClosed⟩]
      rfl
  | collection =>
    change (run .collection n input).isSome = SchemaBody.check (n + 2) input
    cases h : SchemaBody.check (n + 2) input with
    | false =>
      have hNone := site_none .collectionPremise n input h
      simp [run, renameInputs, hNone]
    | true =>
      obtain ⟨body, hClosed, rfl⟩ := (SchemaBody.check_eq_true_iff _ _).mp h
      rw [run_collection ⟨body, hClosed⟩]
      rfl
  | replacement =>
    change (run .replacement n input).isSome = SchemaBody.check (n + 2) input
    cases h : SchemaBody.check (n + 2) input with
    | false =>
      have hNone := site_none .replacementFirst n input h
      simp [run, renameInputs, hNone]
    | true =>
      obtain ⟨body, hClosed, rfl⟩ := (SchemaBody.check_eq_true_iff _ _).mp h
      rw [run_replacement ⟨body, hClosed⟩]
      rfl

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaTemplate
