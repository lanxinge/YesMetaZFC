import YesMetaZFC.Model.ZFC.Pure.PureArithmeticRecurrence
import YesMetaZFC.SetTheory.Ord.NaturalPrime

/-! # 自然数算术复用序数递归的实际纯图

三种运算共享既有 Project 序数递归关系。自然数输入保证输出仍属于内部 ω；
其余输入取空集。后续原规格证明另行连接有限序列见证。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureOrdinalArithmetic
open PureModel PureNaturalInduction
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model Project.FirstOrderSemantics.reduct
universe x
abbrev Operation := PureArithmeticRecurrence.Operation
variable {ℳ : Structure.{0,0,0,x} ℒ}

def schema (operation : Operation) : Project.BinarySchema 1 :=
  match operation with
  | .addition => Project.BinarySchema.ordinalAddition PureKuratowskiProject.convention
  | .multiplication => Project.BinarySchema.ordinalMultiplication PureKuratowskiProject.convention
  | .exponentiation => Project.BinarySchema.ordinalExponentiation PureKuratowskiProject.convention

def OrdinalValue (hℳ : Theory.Models ℳ theory) (operation : Operation) (output left right : Carrier ℳ) : Prop :=
  match operation with
  | .addition => (Project.FirstOrderSemantics.reduct ℳ).IsOrdinalAddition (PureKuratowskiProject.interpretation hℳ) output left right
  | .multiplication => (Project.FirstOrderSemantics.reduct ℳ).IsOrdinalMultiplication (PureKuratowskiProject.interpretation hℳ) output left right
  | .exponentiation => (Project.FirstOrderSemantics.reduct ℳ).IsOrdinalExponentiation (PureKuratowskiProject.interpretation hℳ) output left right

def env (left default : Carrier ℳ) : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 1 where
  bound := fun _ => left
  free := fun _ => default

theorem denote_correct (hℳ : Theory.Models ℳ theory) (operation : Operation) (left right output default : Carrier ℳ) :
    (schema operation).denote (env left default) right output ↔ OrdinalValue hℳ operation output left right := by
  cases operation
  · exact Project.BinarySchema.denote_ordinalAddition_iff (PureKuratowskiProject.interpretation hℳ) (project_models hℳ).1 _ _ _
  · exact Project.BinarySchema.denote_ordinalMultiplication_iff (PureKuratowskiProject.interpretation hℳ) (project_models hℳ).1 _ _ _
  · exact Project.BinarySchema.denote_ordinalExponentiation_iff (PureKuratowskiProject.interpretation hℳ) (project_models hℳ).1 _ _ _

def ordinalGraph (operation : Operation) : Formula ℒ [] [setSort,setSort,setSort] :=
  applyTemplate (PureProjectTemplate.toPure (schema operation).body (schema operation).freeClosed)
    (.cons (.fvar .here) (.cons (.fvar (.there (.there .here))) (.cons (.fvar (.there .here)) .nil)))

theorem ordinal_correct (hℳ : Theory.Models ℳ theory) (operation : Operation) (output left right : Carrier ℳ) :
    (ordinalGraph operation).satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      OrdinalValue hℳ operation output left right := by
  rw [ordinalGraph, applyTemplate_satisfies]
  apply (PureProjectTemplate.correct hℳ (schema operation).body (schema operation).freeClosed
    (.cons output (.cons right (.cons left .nil))) output).trans
  have hEnv : PureProjectTemplate.parameterEnv (count := 3)
      (.cons output (.cons right (.cons left .nil))) output = ((env left output).push right).push output := by
    rw [_root_.YesMetaZFC.SetTheory.Env.mk.injEq]
    constructor
    · funext entry
      exact Fin.cases rfl (fun entry => Fin.cases rfl
        (fun entry => Fin.cases rfl (fun impossible => Fin.elim0 impossible) entry) entry) entry
    · rfl
  rw [hEnv]
  exact denote_correct hℳ operation left right output output

def naturalGuard : Formula ℒ [] [setSort,setSort,setSort] :=
  .existsE setSort <| .conj (applyTemplate PureOmegaAndReverse.omegaGraph (.cons (.bvar .here) .nil)) <|
    .conj (PureRelationDefinitions.mem (.fvar (.there .here)) (.bvar .here))
      (PureRelationDefinitions.mem (.fvar (.there (.there .here))) (.bvar .here))

theorem guard_correct (hℳ : Theory.Models ℳ theory) (output left right : Carrier ℳ) :
    naturalGuard.satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      membership ℳ left (omega hℳ) ∧ membership ℳ right (omega hℳ) := by
  simp only [naturalGuard, Formula.satisfies, applyTemplate_satisfies]
  change (∃ ω, PureOmegaAndReverse.omegaGraph.satisfies (templateEnv (.cons ω .nil)) ∧
    membership ℳ left ω ∧ membership ℳ right ω) ↔ _
  constructor
  · rintro ⟨ω, hω, hLeft, hRight⟩
    have hEqual : ω = omega hℳ := ((PureDifferenceStage.realizes hℳ).function .omega .nil ω).mp hω
    exact hEqual ▸ ⟨hLeft,hRight⟩
  · intro h
    exact ⟨omega hℳ, ((PureDifferenceStage.realizes hℳ).function .omega .nil _).mpr rfl, h⟩

def body (operation : Operation) : Formula ℒ [] [setSort,setSort,setSort] := .conj naturalGuard (ordinalGraph operation)
def graph (operation : Operation) : Formula ℒ [] [setSort,setSort,setSort] :=
  _root_.YesMetaZFC.Automation.TotalizedGraph.formula (body operation) PureRelationFunctions.emptyFallback

theorem body_correct (hℳ : Theory.Models ℳ theory) (operation : Operation) (output left right : Carrier ℳ) :
    (body operation).satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      (membership ℳ left (omega hℳ) ∧ membership ℳ right (omega hℳ)) ∧ OrdinalValue hℳ operation output left right :=
  and_congr (guard_correct hℳ output left right) (ordinal_correct hℳ operation output left right)

/-- 序数递归保证任意自然数输入的实际输出存在唯一。 -/
theorem ordinal_existsUnique (hℳ : Theory.Models ℳ theory) (operation : Operation)
    (left : Carrier ℳ) {right : Carrier ℳ} (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) :
    ∃ output, OrdinalValue hℳ operation output left right ∧
      ∀ other, OrdinalValue hℳ operation other left right → other = output := by
  have hOrdinal := (omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) right hRight
  cases operation
  · exact _root_.YesMetaZFC.SetTheory.ZF.ordinalAddition_existsUnique (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) left hOrdinal
  · exact _root_.YesMetaZFC.SetTheory.ZF.ordinalMultiplication_existsUnique (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) left hOrdinal
  · exact _root_.YesMetaZFC.SetTheory.ZF.ordinalExponentiation_existsUnique (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ)
      ((omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) left hLeft) hOrdinal

theorem ordinal_unique (hℳ : Theory.Models ℳ theory) (operation : Operation)
    {left right first second : Carrier ℳ} (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ))
    (hFirst : OrdinalValue hℳ operation first left right) (hSecond : OrdinalValue hℳ operation second left right) : first = second := by
  obtain ⟨_, _, hUnique⟩ := ordinal_existsUnique hℳ operation left hLeft hRight
  exact (hUnique first hFirst).trans (hUnique second hSecond).symm

theorem closed (hℳ : Theory.Models ℳ theory) (operation : Operation)
    {left right output : Carrier ℳ} (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ))
    (hOutput : OrdinalValue hℳ operation output left right) : membership ℳ output (omega hℳ) := by
  cases operation
  · exact _root_.YesMetaZFC.SetTheory.ZF.ordinalAddition_mem_omega (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) (omega_project hℳ) hLeft hRight hOutput
  · exact _root_.YesMetaZFC.SetTheory.ZF.ordinalMultiplication_mem_omega (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) (omega_project hℳ) hLeft hRight hOutput
  · exact _root_.YesMetaZFC.SetTheory.ZF.ordinalExponentiation_mem_omega (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) (omega_project hℳ) hLeft hRight hOutput

theorem functional (hℳ : Theory.Models ℳ theory) (operation : Operation) (left right : Carrier ℳ) :
    ∃ output, (graph operation).satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ∧
      ∀ other, (graph operation).satisfies (templateEnv (.cons other (.cons left (.cons right .nil)))) → other = output := by
  apply PureRelationFunctions.totalized_functional hℳ (body operation) (.cons left (.cons right .nil))
  intro first second hFirst hSecond
  have hF := (body_correct hℳ operation first left right).mp hFirst
  have hS := (body_correct hℳ operation second left right).mp hSecond
  exact ordinal_unique hℳ operation hF.1.1 hF.1.2 hF.2 hS.2

theorem agrees (hℳ : Theory.Models ℳ theory) (operation : Operation)
    {left right : Carrier ℳ} (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ))
    (output : Carrier ℳ) :
    (graph operation).satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔ OrdinalValue hℳ operation output left right := by
  obtain ⟨witness,hWitness,_⟩ := ordinal_existsUnique hℳ operation left hLeft hRight
  exact (PureRelationFunctions.totalized_agrees (body operation) (.cons left (.cons right .nil))
    ⟨witness, (body_correct hℳ operation witness left right).mpr ⟨⟨hLeft,hRight⟩,hWitness⟩⟩ output).trans
      ((body_correct hℳ operation output left right).trans ⟨And.right,fun h => ⟨⟨hLeft,hRight⟩,h⟩⟩)

/-- 一列序数算术值由替换收集为内部有限函数图。 -/
theorem sequence_exists (hℳ : Theory.Models ℳ theory) (operation : Operation)
    {left length : Carrier ℳ} (hLeft : membership ℳ left (omega hℳ)) (hLength : membership ℳ length (omega hℳ)) :
    ∃ sequence, PureMappingDefinitions.IsMapping ℳ sequence (succ hℳ length) (omega hℳ) ∧
      ∀ input output, PureKuratowski.PairMember ℳ input output sequence ↔
        membership ℳ input (succ hℳ length) ∧ OrdinalValue hℳ operation output left input := by
  have hInputOmega {input : Carrier ℳ} (hInput : membership ℳ input (succ hℳ length)) : membership ℳ input (omega hℳ) := by
    rcases (succ_spec hℳ length input).mp hInput with hLess | rfl
    · exact (omega_project hℳ).transitive (project_modelsZF hℳ) length hLength input hLess
    · exact hLength
  obtain ⟨sequence,hMapping,hValues⟩ := _root_.YesMetaZFC.SetTheory.ZF.exists_setFunctionFromTo_of_denote
    (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) (schema operation) (env left left)
    (source := succ hℳ length) (target := omega hℳ)
    (fun input hInput => by
      obtain ⟨output,hOutput,_⟩ := ordinal_existsUnique hℳ operation left hLeft (hInputOmega hInput)
      exact ⟨output,(denote_correct hℳ operation left input output left).mpr hOutput⟩)
    (fun input hInput first second hFirst hSecond => ordinal_unique hℳ operation hLeft (hInputOmega hInput)
      ((denote_correct hℳ operation left input first left).mp hFirst) ((denote_correct hℳ operation left input second left).mp hSecond))
    (fun input output hInput hOutput => closed hℳ operation hLeft (hInputOmega hInput)
      ((denote_correct hℳ operation left input output left).mp hOutput))
  exact ⟨sequence,hMapping,fun input output => (hValues input output).trans
    (and_congr Iff.rfl (denote_correct hℳ operation left input output left))⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureOrdinalArithmetic
