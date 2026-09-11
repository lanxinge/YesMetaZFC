import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureKuratowskiProject
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRelationDefinitions
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Relation.Core
import YesMetaZFC.SetTheory.Separation

/-! # 定义域和值域的纯隶属定义

两个函数共用坐标筛选。任意集合中的合法有序对坐标均落在其双重并集内，
因此裸 ZFC 的分离公理给出任意输入的输出；不需要预先假定输入是关系。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelationCoordinates
open PureModel PureRelationDefinitions
open Nonlogical.BasicSetTheory (RelationCoordinate)
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature
attribute [local implicit_reducible] PureFunctionDefinitions.parameterSorts
universe x
variable {ℳ : Structure.{0, 0, 0, x} ℒ}

def Member (ℳ : Structure.{0, 0, 0, x} ℒ) (coordinate : RelationCoordinate)
    (relation element : Carrier ℳ) : Prop :=
  match coordinate with
  | .domain => ∃ other, PureKuratowski.PairMember ℳ element other relation
  | .range => ∃ other, PureKuratowski.PairMember ℳ other element relation

def body (coordinate : RelationCoordinate) : Formula ℒ [] [setSort, setSort] :=
  .existsE setSort <| match coordinate with
  | .domain => pairMember (.fvar .here) (.bvar .here) (.fvar (.there .here))
  | .range => pairMember (.bvar .here) (.fvar .here) (.fvar (.there .here))

def coordinateGraph (coordinate : RelationCoordinate) : Formula ℒ [] [setSort, setSort] :=
  PureFunctionDefinitions.comprehension (body coordinate)

theorem coordinate_correct (coordinate : RelationCoordinate) (output relation : Carrier ℳ) :
    (coordinateGraph coordinate).satisfies (templateEnv (.cons output (.cons relation .nil))) ↔
      ∀ element, membership ℳ element output ↔ Member ℳ coordinate relation element := by
  rw [coordinateGraph, PureFunctionDefinitions.comprehension_correct]
  cases coordinate <;> simp only [body, Formula.satisfies, pairMember_satisfies] <;> rfl

/-- 同一坐标条件在 Project 语法中的分离模式。 -/
def coordinateSchema (coordinate : RelationCoordinate) : Project.UnarySchema 1 where
  body := .existsE <| match coordinate with
    | .domain => Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) (.bound 0) (.bound 2)
    | .range => Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 0) (.bound 1) (.bound 2)
  freeClosed := by
    cases coordinate <;> simp -implicitDefEqProofs [_root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]
theorem schema_correct (hℳ : Theory.Models ℳ theory) (coordinate : RelationCoordinate)
    (env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 1) (element : Carrier ℳ) :
    Project.Formula.satisfies (env.push element) (coordinateSchema coordinate).body ↔
      Member ℳ coordinate (env.bound 0) element := by
  cases coordinate <;>
    simp only [coordinateSchema, Project.Formula.satisfies_exists_iff,
      Project.Formula.satisfies_orderedPairMem_iff (PureKuratowskiProject.interpretation hℳ),
      Project.Term.eval_bound_zero_push, Project.Term.eval_bound_one_push, Project.Term.eval_bound_two_push] <;> rfl

/-- 每个合法有序对的两坐标均属于关系的双重并集。 -/
theorem code_mem_double_union (relation union doubleUnion pair left right : Carrier ℳ)
    (hUnion : ∀ element, membership ℳ element union ↔
      ∃ member, membership ℳ member relation ∧ membership ℳ element member)
    (hDoubleUnion : ∀ element, membership ℳ element doubleUnion ↔
      ∃ member, membership ℳ member union ∧ membership ℳ element member)
    (hPair : membership ℳ pair relation) (hCode : PureKuratowski.Code ℳ pair left right) :
    membership ℳ left doubleUnion ∧ membership ℳ right doubleUnion := by
  have hCoordinate (element : Carrier ℳ) (h : element = left ∨ element = right) :
      membership ℳ element doubleUnion := by
    obtain ⟨member, hMember, hElement⟩ := (PureKuratowski.code_union hCode element).mpr h
    exact (hDoubleUnion element).mpr ⟨member, (hUnion member).mpr ⟨pair, hPair, hMember⟩, hElement⟩
  exact ⟨hCoordinate left (Or.inl rfl), hCoordinate right (Or.inr rfl)⟩

theorem member_mem_double_union (coordinate : RelationCoordinate) (relation union doubleUnion element : Carrier ℳ)
    (hUnion : ∀ value, membership ℳ value union ↔
      ∃ member, membership ℳ member relation ∧ membership ℳ value member)
    (hDoubleUnion : ∀ value, membership ℳ value doubleUnion ↔
      ∃ member, membership ℳ member union ∧ membership ℳ value member)
    (hMember : Member ℳ coordinate relation element) : membership ℳ element doubleUnion := by
  cases coordinate with
  | domain =>
    obtain ⟨other, pair, hCode, hPair⟩ := hMember
    exact (code_mem_double_union relation union doubleUnion pair element other hUnion hDoubleUnion hPair hCode).1
  | range =>
    obtain ⟨other, pair, hCode, hPair⟩ := hMember
    exact (code_mem_double_union relation union doubleUnion pair other element hUnion hDoubleUnion hPair hCode).2

/-- 分离得到的坐标集不依赖所选双重并集见证。 -/
theorem exists_coordinate (hℳ : Theory.Models ℳ theory) (coordinate : RelationCoordinate) (relation : Carrier ℳ) :
    ∃ output, (coordinateGraph coordinate).satisfies (templateEnv (.cons output (.cons relation .nil))) := by
  obtain ⟨union, hUnion⟩ := PureModel.union hℳ relation
  obtain ⟨doubleUnion, hDoubleUnion⟩ := PureModel.union hℳ union
  let env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => relation, free := fun _ => relation }
  obtain ⟨output, hOutput⟩ := _root_.YesMetaZFC.SetTheory.ZF.separation_exists_d
    (project_modelsZF hℳ) (coordinateSchema coordinate) env doubleUnion
  refine ⟨output, (coordinate_correct coordinate output relation).mpr ?_⟩
  intro element
  have hCondition := schema_correct hℳ coordinate env element
  change _ ↔ Member ℳ coordinate relation element at hCondition
  exact (hOutput element).trans ⟨fun h => hCondition.mp h.2, fun h =>
    ⟨member_mem_double_union coordinate relation union doubleUnion element hUnion hDoubleUnion h,
      hCondition.mpr h⟩⟩

inductive Primitive : Nonlogical.BasicSetTheory.FunctionSymbol → Type where
  | domain : Primitive .domain
  | range : Primitive .range

def graph {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match primitive with
  | .domain => coordinateGraph .domain
  | .range => coordinateGraph .range

theorem domain_correct (output relation : Carrier ℳ) :
    (graph .domain).satisfies (templateEnv (.cons output (.cons relation .nil))) ↔
      ∀ input, membership ℳ input output ↔ ∃ value, PureKuratowski.PairMember ℳ input value relation :=
  coordinate_correct .domain output relation

theorem range_correct (output relation : Carrier ℳ) :
    (graph .range).satisfies (templateEnv (.cons output (.cons relation .nil))) ↔
      ∀ value, membership ℳ value output ↔ ∃ input, PureKuratowski.PairMember ℳ input value relation :=
  coordinate_correct .range output relation

/-- 原签名的定义域和值域均有任意输入的唯一纯图输出。 -/
theorem functional (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol)
    (args : Values ℳ.Carrier (PureFunctionDefinitions.parameterSorts symbol)) :
    ∃ output : Carrier ℳ, (graph primitive).satisfies (templateEnv (.cons output args)) ∧
      ∀ other, (graph primitive).satisfies (templateEnv (.cons other args)) → other = output := by
  have hCoordinate (coordinate : RelationCoordinate) (relation : Carrier ℳ) :
      ∃ output, (coordinateGraph coordinate).satisfies (templateEnv (.cons output (.cons relation .nil))) ∧
        ∀ other, (coordinateGraph coordinate).satisfies (templateEnv (.cons other (.cons relation .nil))) →
          other = output := by
    obtain ⟨output, hOutput⟩ := exists_coordinate hℳ coordinate relation
    exact ⟨output, hOutput, fun other hOther => PureFunctionDefinitions.comprehension_unique
      hℳ (body coordinate) (.cons relation .nil) other output hOther hOutput⟩
  cases primitive <;> cases args with | cons relation tail =>
    cases tail
    exact hCoordinate _ relation

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRelationCoordinates
