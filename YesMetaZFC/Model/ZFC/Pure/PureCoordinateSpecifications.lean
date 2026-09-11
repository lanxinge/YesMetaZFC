import YesMetaZFC.Model.ZFC.Pure.PureRelationCoordinates
import YesMetaZFC.Model.ZFC.Pure.PureRelationFunctions
import YesMetaZFC.Model.ZFC.Pure.PureMappingDefinitions

/-! # 坐标纯图与原投影筛选、映射定义的连接

原定义域和值域公理在关系输入上通过投影筛选双重并集。这里验证该规格，
并用实际坐标图消去映射定义中此前外加的定义域、值域规格前提。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureCoordinateSpecifications
open PureModel PureRelationCoordinates
open Nonlogical.BasicSetTheory (RelationCoordinate)
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature
universe x
variable {ℳ : Structure.{0, 0, 0, x} ℒ}

def projectionGraph (coordinate : RelationCoordinate) : Formula ℒ [] [setSort, setSort] :=
  match coordinate with
  | .domain => PureRelationFunctions.graph .leftProjection
  | .range => PureRelationFunctions.graph .rightProjection

/-- 关系中的成员均有合法编码，因此总化投影与坐标筛选精确一致。 -/
theorem member_iff_projection (coordinate : RelationCoordinate) (relation element : Carrier ℳ)
    (hRelation : PureKuratowski.IsRelation ℳ relation) :
    Member ℳ coordinate relation element ↔
      ∃ pair, membership ℳ pair relation ∧
        (projectionGraph coordinate).satisfies (templateEnv (.cons element (.cons pair .nil))) := by
  cases coordinate with
  | domain =>
    constructor
    · rintro ⟨other, pair, hCode, hPair⟩
      exact ⟨pair, hPair, (PureRelationFunctions.left_value hCode element).mpr rfl⟩
    · rintro ⟨pair, hPair, hProjection⟩
      obtain ⟨left, right, hCode⟩ := hRelation pair hPair
      have hElement := (PureRelationFunctions.left_value hCode element).mp hProjection
      subst element
      exact ⟨right, pair, hCode, hPair⟩
  | range =>
    constructor
    · rintro ⟨other, pair, hCode, hPair⟩
      exact ⟨pair, hPair, (PureRelationFunctions.right_value hCode element).mpr rfl⟩
    · rintro ⟨pair, hPair, hProjection⟩
      obtain ⟨left, right, hCode⟩ := hRelation pair hPair
      have hElement := (PureRelationFunctions.right_value hCode element).mp hProjection
      subst element
      exact ⟨left, pair, hCode, hPair⟩

/-- 合法关系输入上，纯图保留原公理的投影条件和双重并集母集。 -/
theorem coordinate_spec (coordinate : RelationCoordinate) (output relation union doubleUnion : Carrier ℳ)
    (hRelation : PureKuratowski.IsRelation ℳ relation)
    (hUnion : ∀ element, membership ℳ element union ↔
      ∃ member, membership ℳ member relation ∧ membership ℳ element member)
    (hDoubleUnion : ∀ element, membership ℳ element doubleUnion ↔
      ∃ member, membership ℳ member union ∧ membership ℳ element member) :
    (coordinateGraph coordinate).satisfies (templateEnv (.cons output (.cons relation .nil))) ↔
      ∀ element, membership ℳ element output ↔ membership ℳ element doubleUnion ∧
        ∃ pair, membership ℳ pair relation ∧
          (projectionGraph coordinate).satisfies (templateEnv (.cons element (.cons pair .nil))) := by
  rw [coordinate_correct]
  have hCondition (element : Carrier ℳ) : Member ℳ coordinate relation element ↔
      membership ℳ element doubleUnion ∧ ∃ pair, membership ℳ pair relation ∧
        (projectionGraph coordinate).satisfies (templateEnv (.cons element (.cons pair .nil))) :=
    ⟨fun h => ⟨member_mem_double_union coordinate relation union doubleUnion element hUnion hDoubleUnion h,
      (member_iff_projection coordinate relation element hRelation).mp h⟩,
      fun h => (member_iff_projection coordinate relation element hRelation).mpr h.2⟩
  exact ⟨fun h element => (h element).trans (hCondition element),
    fun h element => (h element).trans (hCondition element).symm⟩

/-- 原映射条件在纯语言中显式计算定义域和值域。自由槽顺序为函数、源集、目标集。 -/
def mappingCondition : Formula ℒ [] [setSort, setSort, setSort] :=
  .existsE setSort <| .existsE setSort <|
    .conj (applyTemplate (graph .domain) (.cons (.bvar (.there .here)) (.cons (.fvar .here) .nil))) <|
    .conj (applyTemplate (graph .range) (.cons (.bvar .here) (.cons (.fvar .here) .nil))) <|
    .conj (PureRelationDefinitions.isFunction (.fvar .here)) <|
    .conj (.equal (.fvar (.there .here)) (.bvar (.there .here))) <|
      applyTemplate PureRelationDefinitions.subsetGraph
        (.cons (.bvar .here) (.cons (.fvar (.there (.there .here))) .nil))

/-- 实际坐标图填满原映射定义；此等价仅假定裸 ZFC 模型，不再外加坐标规格。 -/
theorem mapping_definition (hℳ : Theory.Models ℳ theory) (function source target : Carrier ℳ) :
    PureMappingDefinitions.isMappingGraph.satisfies
        (templateEnv (.cons function (.cons source (.cons target .nil)))) ↔
      mappingCondition.satisfies (templateEnv (.cons function (.cons source (.cons target .nil)))) := by
  rw [PureMappingDefinitions.isMapping_correct]
  simp only [mappingCondition, Formula.satisfies, applyTemplate_satisfies,
    PureRelationDefinitions.isFunction_satisfies]
  change PureMappingDefinitions.IsMapping ℳ function source target ↔
    ∃ domain range, (∀ input, membership ℳ input domain ↔ ∃ value, PureKuratowski.PairMember ℳ input value function) ∧
      (∀ value, membership ℳ value range ↔ ∃ input, PureKuratowski.PairMember ℳ input value function) ∧
      PureKuratowski.IsFunction ℳ function ∧ source = domain ∧
        ∀ value, membership ℳ value range → membership ℳ value target
  constructor
  · intro hMapping
    obtain ⟨domain, hDomain⟩ := exists_coordinate hℳ .domain function
    obtain ⟨range, hRange⟩ := exists_coordinate hℳ .range function
    have hDomainSpec := (domain_correct domain function).mp hDomain
    have hRangeSpec := (range_correct range function).mp hRange
    exact ⟨domain, range, hDomainSpec, hRangeSpec,
      (PureMappingDefinitions.mapping_spec hℳ function source target domain range hDomainSpec hRangeSpec).mp hMapping⟩
  · rintro ⟨domain, range, hDomain, hRange, hFunction⟩
    exact (PureMappingDefinitions.mapping_spec hℳ function source target domain range hDomain hRange).mpr hFunction

/-- 函数求值现在直接消费实际定义域图中的成员证据。 -/
theorem application_spec (function domain input output : Carrier ℳ)
    (hFunction : PureKuratowski.IsFunction ℳ function)
    (hDomain : (graph .domain).satisfies (templateEnv (.cons domain (.cons function .nil))))
    (hInput : membership ℳ input domain) :
    (PureRelationFunctions.graph .application).satisfies
        (templateEnv (.cons output (.cons function (.cons input .nil)))) ↔
      PureKuratowski.PairMember ℳ input output function :=
  PureRelationFunctions.application_spec hFunction
    (((domain_correct domain function).mp hDomain input).mp hInput) output

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureCoordinateSpecifications
