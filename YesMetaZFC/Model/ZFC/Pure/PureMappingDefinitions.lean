import YesMetaZFC.Model.ZFC.Pure.PureKuratowskiProject
import YesMetaZFC.Model.ZFC.Pure.PureRelationDefinitions
import YesMetaZFC.SetTheory.FunctionSpaceConstruction

/-! # 笛卡尔积、映射及映射收集的纯定义

映射谓词直接描述函数图、精确定义域和目标集。笛卡尔积与映射收集的任意参数
存在性复用 Project 的替换、分离构造；输出唯一性统一来自纯模型外延性。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureMappingDefinitions
open PureModel PureRelationDefinitions
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature
attribute [local implicit_reducible] PureFunctionDefinitions.parameterSorts
universe x
variable {ℳ : Structure.{0, 0, 0, x} ℒ}

def IsMapping (ℳ : Structure.{0, 0, 0, x} ℒ) (function source target : Carrier ℳ) : Prop :=
  PureKuratowski.IsFunction ℳ function ∧
    (∀ input, membership ℳ input source ↔ ∃ output, PureKuratowski.PairMember ℳ input output function) ∧
      ∀ input, membership ℳ input source →
        ∃ output, membership ℳ output target ∧ PureKuratowski.PairMember ℳ input output function

def isMappingGraph : Formula ℒ [] [setSort, setSort, setSort] :=
  .conj (isFunction (.fvar .here)) <|
    .conj
      (.forallE setSort <| .iff (mem (.bvar .here) (.fvar (.there .here))) <|
        .existsE setSort <| pairMember (.bvar (.there .here)) (.bvar .here) (.fvar .here))
      (.forallE setSort <| .imp (mem (.bvar .here) (.fvar (.there .here))) <|
        .existsE setSort <| .conj (mem (.bvar .here) (.fvar (.there (.there .here))))
          (pairMember (.bvar (.there .here)) (.bvar .here) (.fvar .here)))

def isMapping {bound free : SortContext ℒ} (function source target : PureTerm bound free) :
    Formula ℒ bound free :=
  applyTemplate isMappingGraph (.cons function (.cons source (.cons target .nil)))

theorem isMapping_correct (function source target : Carrier ℳ) :
    isMappingGraph.satisfies (templateEnv (.cons function (.cons source (.cons target .nil)))) ↔
      IsMapping ℳ function source target := by
  simp only [isMappingGraph, Formula.satisfies, isFunction_satisfies, pairMember_satisfies]
  rfl

theorem isMapping_satisfies {bound free : SortContext ℒ} (env : Env ℳ bound free)
    (function source target : PureTerm bound free) :
    (isMapping function source target).satisfies env ↔
      IsMapping ℳ (function.eval env) (source.eval env) (target.eval env) :=
  (applyTemplate_satisfies env _ _).trans (isMapping_correct _ _ _)

/-- 原支撑映射谓词要求定义域相等、值域包含；这里不额外要求目标集被充满。 -/
theorem mapping_spec (hℳ : Theory.Models ℳ theory) (function source target domain range : Carrier ℳ)
    (hDomain : ∀ input, membership ℳ input domain ↔
      ∃ output, PureKuratowski.PairMember ℳ input output function)
    (hRange : ∀ output, membership ℳ output range ↔
      ∃ input, PureKuratowski.PairMember ℳ input output function) :
    IsMapping ℳ function source target ↔
      PureKuratowski.IsFunction ℳ function ∧ source = domain ∧
        ∀ output, membership ℳ output range → membership ℳ output target := by
  constructor
  · rintro ⟨hFunction, hSource, hTarget⟩
    refine ⟨hFunction, extensionality hℳ source domain (fun input =>
      (hSource input).trans (hDomain input).symm), ?_⟩
    intro output hOutput
    obtain ⟨input, hPair⟩ := (hRange output).mp hOutput
    obtain ⟨value, hValue, hGraph⟩ := hTarget input ((hSource input).mpr ⟨output, hPair⟩)
    exact (hFunction.2 input value output hGraph hPair) ▸ hValue
  · rintro ⟨hFunction, rfl, hTarget⟩
    refine ⟨hFunction, hDomain, ?_⟩
    intro input hInput
    obtain ⟨output, hPair⟩ := (hDomain input).mp hInput
    exact ⟨output, hTarget output ((hRange output).mpr ⟨input, hPair⟩), hPair⟩

def cartesianBody : Formula ℒ [] [setSort, setSort, setSort] :=
  .existsE setSort <| .conj (mem (.bvar .here) (.fvar (.there .here))) <|
    .existsE setSort <| .conj (mem (.bvar .here) (.fvar (.there (.there .here))))
      (code (.fvar .here) (.bvar (.there .here)) (.bvar .here))

def mappingCollectionBody : Formula ℒ [] [setSort, setSort, setSort] :=
  isMapping (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

inductive Primitive : Nonlogical.BasicSetTheory.FunctionSymbol → Type where
  | cartesianProduct : Primitive .cartesianProduct
  | mappingCollection : Primitive .mappingCollection

def body {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  match primitive with
  | .cartesianProduct => cartesianBody
  | .mappingCollection => mappingCollectionBody

def graph {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol) :
    Formula ℒ [] (setSort :: PureFunctionDefinitions.parameterSorts symbol) :=
  PureFunctionDefinitions.comprehension (body primitive)

theorem cartesian_correct (output left right : Carrier ℳ) :
    (graph .cartesianProduct).satisfies (templateEnv (.cons output (.cons left (.cons right .nil)))) ↔
      ∀ pair, membership ℳ pair output ↔
        ∃ leftValue, membership ℳ leftValue left ∧
          ∃ rightValue, membership ℳ rightValue right ∧ PureKuratowski.Code ℳ pair leftValue rightValue := by
  rw [graph, PureFunctionDefinitions.comprehension_correct]
  simp only [body, cartesianBody, Formula.satisfies, code_satisfies]
  rfl

theorem mappingCollection_correct (output source target : Carrier ℳ) :
    (graph .mappingCollection).satisfies (templateEnv (.cons output (.cons source (.cons target .nil)))) ↔
      ∀ function, membership ℳ function output ↔ IsMapping ℳ function source target := by
  rw [graph, PureFunctionDefinitions.comprehension_correct]
  simp only [body, mappingCollectionBody, isMapping_satisfies]
  rfl

/-- 解释已具体化，存在性不再假定抽象的有序对或函数集合同。 -/
theorem exists_output (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol)
    (args : Values ℳ.Carrier (PureFunctionDefinitions.parameterSorts symbol)) :
    ∃ output : Carrier ℳ, (graph primitive).satisfies (templateEnv (.cons output args)) := by
  cases primitive with
  | cartesianProduct =>
    cases args with | cons left tail =>
    cases tail with | cons right tail =>
    cases tail
    obtain ⟨output, hOutput⟩ := _root_.YesMetaZFC.SetTheory.ZF.exists_cartesianProduct
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) left right
    exact ⟨output, (cartesian_correct output left right).mpr hOutput⟩
  | mappingCollection =>
    cases args with | cons source tail =>
    cases tail with | cons target tail =>
    cases tail
    obtain ⟨output, hOutput⟩ := _root_.YesMetaZFC.SetTheory.ZF.exists_functionSpace
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) source target
    exact ⟨output, (mappingCollection_correct output source target).mpr hOutput⟩

/-- 两个原函数符号的纯图均对任意模型对象参数存在唯一输出。 -/
theorem functional (hℳ : Theory.Models ℳ theory)
    {symbol : Nonlogical.BasicSetTheory.FunctionSymbol} (primitive : Primitive symbol)
    (args : Values ℳ.Carrier (PureFunctionDefinitions.parameterSorts symbol)) :
    ∃ output : Carrier ℳ, (graph primitive).satisfies (templateEnv (.cons output args)) ∧
      ∀ other, (graph primitive).satisfies (templateEnv (.cons other args)) → other = output := by
  obtain ⟨output, hOutput⟩ := exists_output hℳ primitive args
  exact ⟨output, hOutput, fun other hOther =>
    PureFunctionDefinitions.comprehension_unique hℳ (body primitive) args other output hOther hOutput⟩

/-- 按原关系符号的参数次序提供映射定义，供全语言解释装配。 -/
inductive RelationPrimitive : Nonlogical.BasicSetTheory.RelationSymbol → Type where
  | isMapping : RelationPrimitive .isMapping

def relationGraph {symbol : Nonlogical.BasicSetTheory.RelationSymbol} (primitive : RelationPrimitive symbol) :
    Formula ℒ [] ((Nonlogical.BasicSetTheory.signature.relDomain symbol).map (fun _ => setSort)) :=
  match primitive with
  | .isMapping => isMappingGraph

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureMappingDefinitions
