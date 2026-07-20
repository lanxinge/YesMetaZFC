import YesMetaZFC.SetTheory.Definitional.Project.Definitions

/-!
# 项目原子核中的序关系基础

二元关系继续使用 `BinarySchema` 表示。这里迁移序数定义所需的基础序语法，并保持
外延等同与子集为项目原子。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project

namespace BinarySchema

/-- 用左右项和参数向量实例化一个二元关系 schema。 -/
def instantiate {parameterCount depth : Nat}
    (schema : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (left right : Term depth) : Formula 1 depth :=
  schema.body.bind <| Fin.cases right <| Fin.cases left parameters

end BinarySchema

namespace RelationSchema

/-- 原始隶属关系。 -/
def membership : BinarySchema 0 where
  body := .mem (.bound 1) (.bound 0)
  freeClosed := by
    simp [Formula.FreeClosed]

/-- 由有序对集合编码的二元关系；唯一参数是关系集合。 -/
def setCoded (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body :=
    Formula.orderedPairMem 𝒞 (.bound 1) (.bound 0) (.bound 2)
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed,
      Definitional.Term.newest]

end RelationSchema

namespace Formula

/-- `left` 与 `right` 满足给定二元关系。 -/
def related {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (left right : Term depth) : Formula 1 depth :=
  relation.instantiate parameters left right

/-- 用封闭项实例化封闭二元 schema 后仍然自由闭合。 -/
@[simp] theorem related_freeClosed_of_closed
    {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (left right : Term depth)
    (hParameters : parameters.FreeClosed)
    (hLeft : left.freeSupport = [])
    (hRight : right.freeSupport = []) :
    (related relation parameters left right).FreeClosed := by
  unfold related BinarySchema.instantiate
  let substitution : Fin (parameterCount + 2) → Term depth :=
    fun entry =>
      Fin.cases right
        (fun previous => Fin.cases left parameters.get previous)
        entry
  apply (Formula.freeClosed_bind_iff_of_closed substitution
    (formula := relation.body) ?_).2 relation.freeClosed
  intro entry
  refine Fin.cases hRight ?_ entry
  intro previous
  exact Fin.cases hLeft hParameters previous

@[simp] theorem related_membership {depth : Nat}
    (left right : Term depth) :
    related RelationSchema.membership TermVector.empty left right =
      .mem left right := by
  rfl

/-- 由严格关系导出的非严格关系。 -/
def lessOrEqual {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (left right : Term depth) : Formula 1 depth :=
  .disj (extensionalEq left right)
    (related relation parameters left right)

/-- 关系在 `carrier` 上自反空缺。 -/
def isIrreflexiveOn {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (carrier : Term depth) : Formula 1 depth :=
  Formula.forallMem carrier <|
    .neg (related relation parameters.weaken Term.newest Term.newest)

/-- 关系在 `carrier` 上传递。 -/
def isTransitiveOn {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (carrier : Term depth) : Formula 1 depth :=
  Formula.forallMem carrier <| Formula.forallMem carrier.weaken <|
    Formula.forallMem carrier.weaken.weaken <|
      .imp
        (.conj
          (related relation parameters.weaken.weaken.weaken
            (.bound 2) (.bound 1))
          (related relation parameters.weaken.weaken.weaken
            (.bound 1) (.bound 0)))
        (related relation parameters.weaken.weaken.weaken
          (.bound 2) (.bound 0))

/-- `relation` 是 `carrier` 上的严格偏序。 -/
def isStrictPartialOrderOn {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (carrier : Term depth) : Formula 1 depth :=
  .conj (isIrreflexiveOn relation parameters carrier)
    (isTransitiveOn relation parameters carrier)

/-- `relation` 是 `carrier` 上的严格线序。 -/
def isLinearOrderOn {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (carrier : Term depth) : Formula 1 depth :=
  .conj (isStrictPartialOrderOn relation parameters carrier) <|
    Formula.forallMem carrier <| Formula.forallMem carrier.weaken <|
      .disj (extensionalEq (.bound 1) (.bound 0)) <|
        .disj
          (related relation parameters.weaken.weaken
            (.bound 1) (.bound 0))
          (related relation parameters.weaken.weaken
            (.bound 0) (.bound 1))

/-- `candidate` 是 `carrier` 的最小元。 -/
def isLeastOf {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (carrier candidate : Term depth) : Formula 1 depth :=
  .conj (.mem candidate carrier) <| Formula.forallMem carrier <|
    lessOrEqual relation parameters.weaken candidate.weaken Term.newest

/-- `candidate` 是 `carrier` 的极小元。 -/
def isMinimalOf {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (carrier candidate : Term depth) : Formula 1 depth :=
  .conj (.mem candidate carrier) <| Formula.forallMem carrier <|
    .neg (related relation parameters.weaken Term.newest candidate.weaken)

/-- `candidate` 是 `carrier` 的最大元。 -/
def isGreatestOf {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (carrier candidate : Term depth) : Formula 1 depth :=
  .conj (.mem candidate carrier) <| Formula.forallMem carrier <|
    lessOrEqual relation parameters.weaken Term.newest candidate.weaken

/-- `candidate` 是 `carrier` 的极大元。 -/
def isMaximalOf {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (carrier candidate : Term depth) : Formula 1 depth :=
  .conj (.mem candidate carrier) <| Formula.forallMem carrier <|
    .neg (related relation parameters.weaken candidate.weaken Term.newest)

/-- `candidate` 是 `subset` 在 `carrier` 中的下界。 -/
def isLowerBoundIn {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (carrier subset candidate : Term depth) : Formula 1 depth :=
  .conj (.mem candidate carrier) <|
    .conj (Formula.subset subset carrier) <| Formula.forallMem subset <|
      lessOrEqual relation parameters.weaken candidate.weaken Term.newest

/-- `candidate` 是 `subset` 在 `carrier` 中的上界。 -/
def isUpperBoundIn {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (carrier subset candidate : Term depth) : Formula 1 depth :=
  .conj (.mem candidate carrier) <|
    .conj (Formula.subset subset carrier) <| Formula.forallMem subset <|
      lessOrEqual relation parameters.weaken Term.newest candidate.weaken

/-- `candidate` 是 `subset` 在 `carrier` 中的下确界。 -/
def isInfimumIn {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (carrier subset candidate : Term depth) : Formula 1 depth :=
  .conj (isLowerBoundIn relation parameters carrier subset candidate) <|
    Formula.forallMem carrier <|
      .imp
        (isLowerBoundIn relation parameters.weaken carrier.weaken
          subset.weaken Term.newest)
        (lessOrEqual relation parameters.weaken Term.newest candidate.weaken)

/-- `candidate` 是 `subset` 在 `carrier` 中的上确界。 -/
def isSupremumIn {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (carrier subset candidate : Term depth) : Formula 1 depth :=
  .conj (isUpperBoundIn relation parameters carrier subset candidate) <|
    Formula.forallMem carrier <|
      .imp
        (isUpperBoundIn relation parameters.weaken carrier.weaken
          subset.weaken Term.newest)
        (lessOrEqual relation parameters.weaken candidate.weaken Term.newest)

/-- `segment` 是 `carrier` 的向下闭初段。 -/
def isInitialSegmentOf {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (segment carrier : Term depth) : Formula 1 depth :=
  .conj (Formula.subset segment carrier) <|
    Formula.forallMem segment <| Formula.forallMem carrier.weaken <|
      .imp
        (related relation parameters.weaken.weaken Term.newest (.bound 1))
        (.mem Term.newest segment.weaken.weaken)

/-- `segment` 是 `carrier` 的真初段。 -/
def isProperInitialSegmentOf {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (segment carrier : Term depth) : Formula 1 depth :=
  .conj (isInitialSegmentOf relation parameters segment carrier)
    (Formula.extensionalNe segment carrier)

/-- `relation` 良序 `carrier`。 -/
def isWellOrderOn {parameterCount depth : Nat}
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (carrier : Term depth) : Formula 1 depth :=
  .conj (isLinearOrderOn relation parameters carrier) <|
    .forallE <|
      .imp
        (.conj (Formula.subset Term.newest carrier.weaken)
          (Formula.existsMem Term.newest .truth))
        (.existsE <|
          isLeastOf relation parameters.weaken.weaken
            (.bound 1) Term.newest)

/-- `function` 从 `source` 到 `target` 保序。 -/
def isOrderPreserving {sourceCount targetCount depth : Nat}
    (𝒞 : OrderedPairConvention)
    (sourceRelation : BinarySchema sourceCount)
    (sourceParameters : TermVector sourceCount depth)
    (targetRelation : BinarySchema targetCount)
    (targetParameters : TermVector targetCount depth)
    (function source target : Term depth) : Formula 1 depth :=
  .conj (isFunctionFromTo 𝒞 function source target) <|
    Formula.forallMem source <| Formula.forallMem source.weaken <|
      Formula.forallMem target.weaken.weaken <|
        Formula.forallMem target.weaken.weaken.weaken <|
          .imp
            (.conj
              (orderedPairMem 𝒞 (.bound 3) (.bound 1)
                function.weaken.weaken.weaken.weaken)
              (orderedPairMem 𝒞 (.bound 2) (.bound 0)
                function.weaken.weaken.weaken.weaken))
            (.imp
              (related sourceRelation
                sourceParameters.weaken.weaken.weaken.weaken
                (.bound 3) (.bound 2))
              (related targetRelation
                targetParameters.weaken.weaken.weaken.weaken
                (.bound 1) (.bound 0)))

/-- `function` 反映并保持两个严格关系。 -/
def isOrderEmbedding {sourceCount targetCount depth : Nat}
    (𝒞 : OrderedPairConvention)
    (sourceRelation : BinarySchema sourceCount)
    (sourceParameters : TermVector sourceCount depth)
    (targetRelation : BinarySchema targetCount)
    (targetParameters : TermVector targetCount depth)
    (function source target : Term depth) : Formula 1 depth :=
  .conj (isFunctionFromTo 𝒞 function source target) <|
    Formula.forallMem source <| Formula.forallMem source.weaken <|
      Formula.forallMem target.weaken.weaken <|
        Formula.forallMem target.weaken.weaken.weaken <|
          .imp
            (.conj
              (orderedPairMem 𝒞 (.bound 3) (.bound 1)
                function.weaken.weaken.weaken.weaken)
              (orderedPairMem 𝒞 (.bound 2) (.bound 0)
                function.weaken.weaken.weaken.weaken))
            (.iff
              (related sourceRelation
                sourceParameters.weaken.weaken.weaken.weaken
                (.bound 3) (.bound 2))
              (related targetRelation
                targetParameters.weaken.weaken.weaken.weaken
                (.bound 1) (.bound 0)))

/-- `function` 是两个序之间的同构。 -/
def isOrderIsomorphism {sourceCount targetCount depth : Nat}
    (𝒞 : OrderedPairConvention)
    (sourceRelation : BinarySchema sourceCount)
    (sourceParameters : TermVector sourceCount depth)
    (targetRelation : BinarySchema targetCount)
    (targetParameters : TermVector targetCount depth)
    (function source target : Term depth) : Formula 1 depth :=
  .conj
    (isOrderEmbedding 𝒞 sourceRelation sourceParameters
      targetRelation targetParameters function source target) <|
    .conj (isInjective 𝒞 function)
      (isSurjectiveOnto 𝒞 function source target)

/-- `function` 是一个序的自同构。 -/
def isOrderAutomorphism {parameterCount depth : Nat}
    (𝒞 : OrderedPairConvention)
    (relation : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (function carrier : Term depth) : Formula 1 depth :=
  isOrderIsomorphism 𝒞 relation parameters relation parameters
    function carrier carrier

/-- 集合编码关系是 `carrier` 上的严格偏序。 -/
def isStrictOrderRelation (𝒞 : OrderedPairConvention)
    {depth : Nat} (relation carrier : Term depth) : Formula 1 depth :=
  isStrictPartialOrderOn (RelationSchema.setCoded 𝒞)
    (.singleton relation) carrier

/-- 集合编码关系是 `carrier` 上的严格线序。 -/
def isLinearOrderRelation (𝒞 : OrderedPairConvention)
    {depth : Nat} (relation carrier : Term depth) : Formula 1 depth :=
  isLinearOrderOn (RelationSchema.setCoded 𝒞)
    (.singleton relation) carrier

/-- 集合编码关系良序 `carrier`。 -/
def isWellOrderRelation (𝒞 : OrderedPairConvention)
    {depth : Nat} (relation carrier : Term depth) : Formula 1 depth :=
  isWellOrderOn (RelationSchema.setCoded 𝒞)
    (.singleton relation) carrier

end Formula

end Project
end Definitional
end SetTheory
end YesMetaZFC
