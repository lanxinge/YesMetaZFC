import YesMetaZFC.SetTheory.Card.Aleph.Existence
import YesMetaZFC.SetTheory.Ord.OrderType

/-!
# Hartogs 序数

本文件在模型内部收集给定集合各子集上的集合编码良序，并以其序型后继之并构造
Hartogs 序数。整个构造只使用模型内部幂集、笛卡尔积、分离、替换与良序坍缩。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- `code` 编码 `source` 某个子集上的集合编码良序。 -/
def IsHartogsWellOrderCode {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (code source : ℳ.Domain) : Prop :=
  ∃ carrier relation,
    𝕀.Codes code carrier relation ∧
      ℳ.MemberSubset carrier source ∧
        ℳ.IsSetCodedWellOrder 𝕀 relation carrier

/-- `successor` 是某个 Hartogs 良序编码之规范序型的后继。 -/
def IsHartogsSuccessorValue {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (code source successor : ℳ.Domain) : Prop :=
  ∃ carrier relation ordinal,
    𝕀.Codes code carrier relation ∧
      ℳ.MemberSubset carrier source ∧
        ℳ.IsSetCodedWellOrder 𝕀 relation carrier ∧
          ℳ.IsWellOrderType 𝕀 relation carrier ordinal ∧
            ℳ.SuccessorOf successor ordinal

/--
`hartogs` 的成员序数恰好是可模型内部单射进 `source` 的序数。
-/
def IsHartogsNumber {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hartogs source : ℳ.Domain) : Prop :=
  ℳ.IsOrdinal hartogs ∧
    ∀ α, ℳ.IsOrdinal α →
      (ℳ.mem α hartogs ↔
        ℳ.CardinalLessOrEqual 𝕀 α source)

end Structure

namespace Definitional
namespace Project
namespace Formula

/-- `code` 编码 `source` 某个子集上的集合编码良序。 -/
def isHartogsWellOrderCode
    (𝒞 : OrderedPairConvention)
    {depth : Nat} (code source : Term depth) : Formula 1 depth :=
  .existsE <| .existsE <| .conj
    (𝒞.code code.weaken.weaken (.bound 1) (.bound 0)) <| .conj
    (subset (.bound 1) source.weaken.weaken)
    (isSetCodedWellOrder 𝒞 (.bound 0) (.bound 1))

/-- Hartogs 良序编码公式与纸面语义一致。 -/
theorem satisfies_isHartogsWellOrderCode_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (code source : Term depth) :
    satisfies env (isHartogsWellOrderCode 𝒞 code source) ↔
      ℳ.IsHartogsWellOrderCode 𝕀
        (code.eval env) (source.eval env) := by
  simp only [isHartogsWellOrderCode,
    Structure.IsHartogsWellOrderCode,
    satisfies_exists_iff, satisfies_conj_iff,
    𝕀.satisfies_code_iff, satisfies_subset_iff,
    satisfies_isSetCodedWellOrder_iff 𝕀,
    Structure.MemberSubset, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push
    ]

end Formula

namespace UnarySchema

/-- 从统一编码空间中分离全部 Hartogs 良序编码。 -/
def hartogsWellOrderCodeMembership
    (𝒞 : OrderedPairConvention) : UnarySchema 1 where
  body := Formula.isHartogsWellOrderCode 𝒞
    Term.newest (.bound 1)
  freeClosed := by
    simp [Formula.isHartogsWellOrderCode,
      Formula.isSetCodedWellOrder,
      Formula.isWellOrderRelation, Formula.isWellOrderOn,
      Formula.isLinearOrderOn, Formula.isStrictPartialOrderOn,
      Formula.isIrreflexiveOn, Formula.isTransitiveOn,
      Formula.isLeastOf, Formula.lessOrEqual,
      Formula.isRelation, Formula.related,
      Formula.forallMem,
      Formula.subset, Formula.extensionalEq,
      Formula.FreeClosed, Term.newest]
    repeat' constructor
    all_goals
      first
      | exact Formula.related_freeClosed_of_closed
          (relation := _) (parameters := _) (left := _) (right := _)
          (by intro entry; simp [TermVector.singleton])
          (by simp) (by simp)
      | simp [Formula.existsMem, Formula.FreeClosed, Term.newest]

end UnarySchema

namespace BinarySchema

/-- 把 Hartogs 良序编码映到其规范序型的后继。 -/
def hartogsSuccessorValue
    (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body := .existsE <| .existsE <| .existsE <| .conj
    (𝒞.code (.bound 4) (.bound 2) (.bound 1)) <| .conj
    (Formula.subset (.bound 2) (.bound 5)) <| .conj
    (Formula.isSetCodedWellOrder 𝒞 (.bound 1) (.bound 2)) <| .conj
    (Formula.isWellOrderType 𝒞
      (.bound 1) (.bound 2) (.bound 0))
    (Formula.isSuccessor (.bound 3) (.bound 0))
  freeClosed := by
    simp [Formula.isSetCodedWellOrder,
      Formula.isWellOrderRelation, Formula.isWellOrderOn,
      Formula.isLinearOrderOn, Formula.isStrictPartialOrderOn,
      Formula.isIrreflexiveOn, Formula.isTransitiveOn,
      Formula.isLeastOf, Formula.lessOrEqual,
      Formula.isWellOrderType,
      Formula.isWellOrderCollapseFunction,
      Formula.isRelationInitialSegment,
      Formula.isFunction, Formula.isRelation,
      Formula.isDomain, Formula.isRange,
      Formula.orderedPairMem, Formula.related,
      Formula.forallMem, Formula.existsMem,
      Formula.subset, Formula.isSuccessor,
      Formula.extensionalEq, Formula.FreeClosed,
      Term.newest]
    repeat' constructor
    all_goals
      exact Formula.related_freeClosed_of_closed
        (relation := _) (parameters := _) (left := _) (right := _)
        (by intro entry; simp [TermVector.singleton])
        (by simp) (by simp)

end BinarySchema

namespace Formula

/-- Hartogs 序型后继模式与纸面语义一致。 -/
theorem denote_hartogsSuccessorValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 1) (code successor : ℳ.Domain) :
    (BinarySchema.hartogsSuccessorValue 𝒞).denote
        env code successor ↔
      ℳ.IsHartogsSuccessorValue 𝕀
        code (env.bound 0) successor := by
  simp only [BinarySchema.hartogsSuccessorValue,
    BinarySchema.denote, Structure.IsHartogsSuccessorValue,
    satisfies_exists_iff, satisfies_conj_iff,
    𝕀.satisfies_code_iff,
    satisfies_subset_iff,
    satisfies_isSetCodedWellOrder_iff 𝕀,
    satisfies_isWellOrderType_iff 𝕀 hExt,
    satisfies_isSuccessor_iff,
    Structure.MemberSubset,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push]
  rfl

end Formula

end Project
end Definitional

namespace ZF

/-- ZF 中每个集合都具有 Hartogs 序数。 -/
theorem exists_hartogsNumber
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (source : ℳ.Domain) :
    ∃ hartogs, ℳ.IsHartogsNumber 𝕀 hartogs source := by
  rcases exists_powerSet hZF source with
    ⟨carrierPower, hCarrierPower⟩
  rcases exists_cartesianProduct hZF 𝕀 source source with
    ⟨sourceProduct, hSourceProduct⟩
  rcases exists_powerSet hZF sourceProduct with
    ⟨relationPower, hRelationPower⟩
  rcases exists_cartesianProduct hZF 𝕀
      carrierPower relationPower with
    ⟨codeSpace, hCodeSpace⟩
  let sourceEnv : Env ℳ 1 := {
    bound := fun _ => source
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_separation hZF
      (Definitional.Project.UnarySchema.hartogsWellOrderCodeMembership 𝒞)
      sourceEnv codeSpace with
    ⟨wellOrderCodes, hWellOrderCodes⟩
  have hCodeMembership (code : ℳ.Domain) :
      ℳ.mem code wellOrderCodes ↔
        ℳ.mem code codeSpace ∧
          ℳ.IsHartogsWellOrderCode 𝕀 code source := by
    rw [hWellOrderCodes code]
    change
      (ℳ.mem code codeSpace ∧
        Definitional.Project.Formula.satisfies (sourceEnv.push code)
          (Definitional.Project.Formula.isHartogsWellOrderCode 𝒞
            Definitional.Project.Term.newest
            (Definitional.Project.Term.bound 1))) ↔ _
    rw [Definitional.Project.Formula.satisfies_isHartogsWellOrderCode_iff
      𝕀]
    simp only [Definitional.Project.Term.eval_bound_one_push]
    rfl
  have hSuccessorTotal :
      ∀ code, ℳ.mem code wellOrderCodes →
        ∃ successor,
          (Definitional.Project.BinarySchema.hartogsSuccessorValue 𝒞).denote
            sourceEnv code successor := by
    intro code hCode
    rcases (hCodeMembership code).mp hCode |>.2 with
      ⟨carrier, relation, hCodePair, hCarrierSubset, hOrder⟩
    rcases wellOrderType_existsUnique hZF 𝕀 hOrder with
      ⟨ordinal, hType, _⟩
    rcases KP.exists_successor (modelsKP hZF) ordinal with
      ⟨successor, hSuccessor⟩
    refine ⟨successor,
      (Definitional.Project.Formula.denote_hartogsSuccessorValue_iff
        𝕀 hZF.1 sourceEnv code successor).mpr ?_⟩
    exact ⟨carrier, relation, ordinal,
      hCodePair, hCarrierSubset, hOrder, hType, hSuccessor⟩
  have hSuccessorUnique :
      ∀ code, ℳ.mem code wellOrderCodes →
        ∀ first second,
          (Definitional.Project.BinarySchema.hartogsSuccessorValue 𝒞).denote
              sourceEnv code first →
            (Definitional.Project.BinarySchema.hartogsSuccessorValue 𝒞).denote
              sourceEnv code second →
              first = second := by
    intro code _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_hartogsSuccessorValue_iff
      𝕀 hZF.1] at hFirst hSecond
    rcases hFirst with
      ⟨firstCarrier, firstRelation, firstOrdinal,
        hFirstCode, _, hFirstOrder, hFirstType, hFirstSuccessor⟩
    rcases hSecond with
      ⟨secondCarrier, secondRelation, secondOrdinal,
        hSecondCode, _, _, hSecondType, hSecondSuccessor⟩
    rcases 𝕀.injective hFirstCode hSecondCode with
      ⟨hCarrierEq, hRelationEq⟩
    subst secondCarrier
    subst secondRelation
    rcases wellOrderType_existsUnique hZF 𝕀 hFirstOrder with
      ⟨selected, _, hTypeUnique⟩
    have hFirstOrdinalEq := hTypeUnique firstOrdinal hFirstType
    have hSecondOrdinalEq := hTypeUnique secondOrdinal hSecondType
    subst firstOrdinal
    subst secondOrdinal
    exact Structure.SuccessorOf.eq hZF.1
      hFirstSuccessor hSecondSuccessor
  rcases exists_functionalImageOn hZF
      (Definitional.Project.BinarySchema.hartogsSuccessorValue 𝒞)
      sourceEnv wellOrderCodes
      hSuccessorTotal hSuccessorUnique with
    ⟨successors, hSuccessors⟩
  rcases KP.exists_union (modelsKP hZF) successors with
    ⟨hartogs, hHartogsUnion⟩
  have hSuccessorOrdinal :
      ∀ successor, ℳ.mem successor successors →
        ℳ.IsOrdinal successor := by
    intro successor hSuccessor
    rcases (hSuccessors successor).mp hSuccessor with
      ⟨code, hCode, hValue⟩
    rw [Definitional.Project.Formula.denote_hartogsSuccessorValue_iff
      𝕀 hZF.1] at hValue
    rcases hValue with
      ⟨carrier, relation, ordinal, _,
        _, hOrder, hType, hOrdinalSuccessor⟩
    exact KP.successor_isOrdinal (modelsKP hZF)
      (hType.isOrdinal hZF 𝕀 hOrder) hOrdinalSuccessor
  have hHartogsOrdinal : ℳ.IsOrdinal hartogs :=
    Structure.IsOrdinal.of_union (modelsKP hZF)
      hHartogsUnion hSuccessorOrdinal
  have hForward :
      ∀ α, ℳ.IsOrdinal α →
        ℳ.CardinalLessOrEqual 𝕀 α source →
          ℳ.mem α hartogs := by
    intro α hα hαSource
    rcases hαSource with ⟨function, hInjection⟩
    rcases exists_wellOrderRealization_of_ordinalInjection
        hZF 𝕀 hα hInjection with
      ⟨carrier, relation, hCarrierSubset,
        hRelationOn, hOrder, hType⟩
    have hRelationSubsetProduct :
        ℳ.MemberSubset relation sourceProduct := by
      intro pair hPair
      rcases hRelationOn.1 pair hPair with
        ⟨left, right, hCode⟩
      have hPairMember :
          ℳ.PairMember 𝕀 left right relation :=
        ⟨pair, hCode, hPair⟩
      have hCoordinates := hRelationOn.2 left right hPairMember
      exact (hSourceProduct pair).mpr
        ⟨left, hCarrierSubset left hCoordinates.1,
          right, hCarrierSubset right hCoordinates.2, hCode⟩
    rcases 𝕀.total carrier relation with
      ⟨code, hCodePair⟩
    have hCodeSpaceMember : ℳ.mem code codeSpace := by
      apply (hCodeSpace code).mpr
      exact ⟨carrier,
        (hCarrierPower carrier).mpr hCarrierSubset,
        relation,
        (hRelationPower relation).mpr hRelationSubsetProduct,
        hCodePair⟩
    have hCodeMember : ℳ.mem code wellOrderCodes :=
      (hCodeMembership code).mpr
        ⟨hCodeSpaceMember,
          carrier, relation, hCodePair, hCarrierSubset, hOrder⟩
    rcases KP.exists_successor (modelsKP hZF) α with
      ⟨successor, hSuccessor⟩
    have hSuccessorValue :
        (Definitional.Project.BinarySchema.hartogsSuccessorValue 𝒞).denote
          sourceEnv code successor :=
      (Definitional.Project.Formula.denote_hartogsSuccessorValue_iff
        𝕀 hZF.1 sourceEnv code successor).mpr
          ⟨carrier, relation, α,
            hCodePair, hCarrierSubset, hOrder, hType, hSuccessor⟩
    have hSuccessorMember : ℳ.mem successor successors :=
      (hSuccessors successor).mpr
        ⟨code, hCodeMember, hSuccessorValue⟩
    exact (hHartogsUnion α).mpr
      ⟨successor, hSuccessorMember,
        (hSuccessor α).mpr <| Or.inr fun _ => Iff.rfl⟩
  have hBackward :
      ∀ α, ℳ.IsOrdinal α →
        ℳ.mem α hartogs →
          ℳ.CardinalLessOrEqual 𝕀 α source := by
    intro α hα hαHartogs
    rcases (hHartogsUnion α).mp hαHartogs with
      ⟨successor, hSuccessorMember, hαSuccessor⟩
    rcases (hSuccessors successor).mp hSuccessorMember with
      ⟨code, _, hSuccessorValue⟩
    rw [Definitional.Project.Formula.denote_hartogsSuccessorValue_iff
      𝕀 hZF.1] at hSuccessorValue
    rcases hSuccessorValue with
      ⟨carrier, relation, ordinal, _,
        hCarrierSubset, hOrder, hType, hSuccessor⟩
    have hOrdinal : ℳ.IsOrdinal ordinal :=
      hType.isOrdinal hZF 𝕀 hOrder
    have hOrdinalCarrier :
        ℳ.CardinalLessOrEqual 𝕀 ordinal carrier := by
      rcases (hType.equinumerous hZF 𝕀 hOrder).symm hZF 𝕀 with
        ⟨function, hFunction⟩
      exact ⟨function, hFunction.1⟩
    rcases exists_inclusionInjection hZF 𝕀 hCarrierSubset with
      ⟨carrierToSource, hCarrierToSource⟩
    rcases hOrdinalCarrier with
      ⟨ordinalToCarrier, hOrdinalToCarrier⟩
    rcases exists_compositionInjection hZF 𝕀
        hOrdinalToCarrier hCarrierToSource with
      ⟨ordinalToSource, hOrdinalToSource⟩
    rcases (hSuccessor α).mp hαSuccessor with
      hαOrdinal | hSame
    · have hαSubsetOrdinal : ℳ.MemberSubset α ordinal :=
        hOrdinal.transitive α hαOrdinal
      rcases exists_inclusionInjection hZF 𝕀 hαSubsetOrdinal with
        ⟨αToOrdinal, hαToOrdinal⟩
      rcases exists_compositionInjection hZF 𝕀
          hαToOrdinal hOrdinalToSource with
        ⟨αToSource, hαToSource⟩
      exact ⟨αToSource, hαToSource⟩
    · have hαEq :=
        hZF.1.eq_of_same_members α ordinal hSame
      subst ordinal
      exact ⟨ordinalToSource, hOrdinalToSource⟩
  exact ⟨hartogs, hHartogsOrdinal, fun α hα =>
    ⟨hBackward α hα, hForward α hα⟩⟩

end ZF

namespace Structure.IsHartogsNumber

/-- Hartogs 序数不能模型内部单射回其源集。 -/
theorem not_cardinalLessOrEqual
    {ℳ : Structure.{u}} (hKP : ℳ.Models SetTheory.KP)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {hartogs source : ℳ.Domain}
    (hHartogs : ℳ.IsHartogsNumber 𝕀 hartogs source) :
    ¬ ℳ.CardinalLessOrEqual 𝕀 hartogs source := by
  intro hInjection
  exact KP.mem_irrefl hKP hartogs <|
    (hHartogs.2 hartogs hHartogs.1).mpr hInjection

/-- Hartogs 序数本身是基数。 -/
theorem isCardinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {hartogs source : ℳ.Domain}
    (hHartogs : ℳ.IsHartogsNumber 𝕀 hartogs source) :
    ℳ.IsCardinal 𝕀 hartogs := by
  refine ⟨hHartogs.1, ?_⟩
  intro α hαHartogs hEquinumerous
  have hα : ℳ.IsOrdinal α :=
    hHartogs.1.mem hαHartogs
  rcases (hHartogs.2 α hα).mp hαHartogs with
    ⟨αToSource, hαToSource⟩
  rcases hEquinumerous.symm hZF 𝕀 with
    ⟨hartogsToα, hHartogsToα⟩
  rcases ZF.exists_compositionInjection hZF 𝕀
      hHartogsToα.1 hαToSource with
    ⟨hartogsToSource, hHartogsToSource⟩
  exact hHartogs.not_cardinalLessOrEqual
    (ZF.modelsKP hZF) ⟨hartogsToSource, hHartogsToSource⟩

end Structure.IsHartogsNumber

namespace ZF

/-- 每个序数上方都存在一个基数。 -/
theorem exists_cardinalAbove
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {α : ℳ.Domain}
    (hα : ℳ.IsOrdinal α) :
    ∃ κ, ℳ.IsCardinal 𝕀 κ ∧ ℳ.mem α κ := by
  rcases exists_hartogsNumber hZF 𝕀 α with
    ⟨κ, hκ⟩
  rcases exists_inclusionInjection hZF 𝕀
      (fun _ h => h) with
    ⟨identity, hIdentity⟩
  exact ⟨κ, hκ.isCardinal hZF 𝕀,
    (hκ.2 α hα).mpr ⟨identity, hIdentity⟩⟩

end ZF

end SetTheory
end YesMetaZFC
