import YesMetaZFC.SetTheory.Definitional.Project.Hierarchy

/-!
# 项目原子核的集合论常用定义

本层只定义项目公式的缩写。纸面上的空集、配对、并、幂集、关系和函数仍然由隶属
关系与项目原子刻画；原子定义体不会在这些构造中重新展开。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project

namespace Formula

/-- `set` 没有元素。 -/
def isEmpty {depth : Nat} (set : Term depth) : Formula 1 depth :=
  .forallE <| .neg (.mem Term.newest set.weaken)

/-- `pair` 恰好包含 `left` 与 `right`。 -/
def isUnorderedPair {depth : Nat} (pair left right : Term depth) :
    Formula 1 depth :=
  .forallE <|
    .iff (.mem Term.newest pair.weaken) <|
      .disj (extensionalEq Term.newest left.weaken)
        (extensionalEq Term.newest right.weaken)

/-- `singleton` 是 `element` 的单元素集。 -/
def isSingleton {depth : Nat} (singleton element : Term depth) :
    Formula 1 depth :=
  isUnorderedPair singleton element element

/-- `union` 是 `family` 的并集。 -/
def isUnion {depth : Nat} (union family : Term depth) : Formula 1 depth :=
  .forallE <|
    .iff (.mem Term.newest union.weaken) <|
      .existsE <|
        .conj (.mem Term.newest family.weaken.weaken)
          (.mem (.bound 1) Term.newest)

/-- `power` 是 `set` 的幂集。 -/
def isPowerSet {depth : Nat} (power set : Term depth) : Formula 1 depth :=
  .forallE <|
    .iff (.mem Term.newest power.weaken)
      (subset Term.newest set.weaken)

/-- `successor` 是 `set ∪ {set}`。 -/
def isSuccessor {depth : Nat} (successor set : Term depth) :
    Formula 1 depth :=
  .forallE <|
    .iff (.mem Term.newest successor.weaken) <|
      .disj (.mem Term.newest set.weaken)
        (extensionalEq Term.newest set.weaken)

/-- `inter` 是两个集合的交。 -/
def isIntersection {depth : Nat} (inter left right : Term depth) :
    Formula 1 depth :=
  .forallE <|
    .iff (.mem Term.newest inter.weaken) <|
      .conj (.mem Term.newest left.weaken)
        (.mem Term.newest right.weaken)

/-- `diff` 是集合差 `left \ right`。 -/
def isDifference {depth : Nat} (diff left right : Term depth) :
    Formula 1 depth :=
  .forallE <|
    .iff (.mem Term.newest diff.weaken) <|
      .conj (.mem Term.newest left.weaken)
        (.neg (.mem Term.newest right.weaken))

/-- `symmDiff` 是两个集合的对称差。 -/
def isSymmetricDifference {depth : Nat}
    (symmDiff left right : Term depth) : Formula 1 depth :=
  .forallE <|
    .iff (.mem Term.newest symmDiff.weaken) <|
      .disj
        (.conj (.mem Term.newest left.weaken)
          (.neg (.mem Term.newest right.weaken)))
        (.conj (.mem Term.newest right.weaken)
          (.neg (.mem Term.newest left.weaken)))

/-- `choice` 与 `member` 的交恰好是单元素集。 -/
def meetsExactlyOnce {depth : Nat}
    (choice member : Term depth) : Formula 1 depth :=
  .existsE <|
    .conj
      (.conj (.mem Term.newest choice.weaken)
        (.mem Term.newest member.weaken)) <|
      .forallE <|
        .imp
          (.conj (.mem Term.newest choice.weaken.weaken)
            (.mem Term.newest member.weaken.weaken))
          (extensionalEq Term.newest (.bound 1))

end Formula

/-- 项目原子核中的有序对编码约定。 -/
structure OrderedPairConvention where
  code : {depth : Nat} → Term depth → Term depth → Term depth → Formula 1 depth
  freeClosed_code :
    ∀ {depth : Nat} (pair left right : Term depth),
      pair.freeSupport = [] →
      left.freeSupport = [] →
      right.freeSupport = [] →
      (code pair left right).FreeClosed

namespace OrderedPairConvention

@[simp] theorem code_freeClosed (𝒞 : OrderedPairConvention)
    {depth : Nat} (pair left right : Term depth)
    (hPair : pair.freeSupport = []) (hLeft : left.freeSupport = [])
    (hRight : right.freeSupport = []) :
    (𝒞.code pair left right).FreeClosed :=
  𝒞.freeClosed_code pair left right hPair hLeft hRight

end OrderedPairConvention

namespace Formula

/-- 纸面命题 `(left, right) ∈ relation` 的项目语法。 -/
def orderedPairMem (𝒞 : OrderedPairConvention)
    {depth : Nat} (left right relation : Term depth) : Formula 1 depth :=
  .existsE <|
    .conj
      (𝒞.code Term.newest left.weaken right.weaken)
      (.mem Term.newest relation.weaken)

/-- `relation` 的每个元素都是约定编码下的有序对。 -/
def isRelation (𝒞 : OrderedPairConvention)
    {depth : Nat} (relation : Term depth) : Formula 1 depth :=
  .forallMem relation <|
    .existsE <| .existsE <|
      𝒞.code (.bound 2) (.bound 1) (.bound 0)

/-- `function` 是单值关系。 -/
def isFunction (𝒞 : OrderedPairConvention)
    {depth : Nat} (function : Term depth) : Formula 1 depth :=
  .conj (isRelation 𝒞 function) <|
    .forallE <| .forallE <| .forallE <|
      .imp
        (.conj
          (orderedPairMem 𝒞 (.bound 2) (.bound 1)
            function.weaken.weaken.weaken)
          (orderedPairMem 𝒞 (.bound 2) (.bound 0)
            function.weaken.weaken.weaken))
        (extensionalEq (.bound 1) (.bound 0))

/-- `domain` 是关系 `relation` 的定义域。 -/
def isDomain (𝒞 : OrderedPairConvention)
    {depth : Nat} (domain relation : Term depth) : Formula 1 depth :=
  .forallE <|
    .iff (.mem Term.newest domain.weaken) <|
      .existsE <|
        orderedPairMem 𝒞 (.bound 1) (.bound 0)
          relation.weaken.weaken

/-- `range` 是关系 `relation` 的值域。 -/
def isRange (𝒞 : OrderedPairConvention)
    {depth : Nat} (range relation : Term depth) : Formula 1 depth :=
  .forallE <|
    .iff (.mem Term.newest range.weaken) <|
      .existsE <|
        orderedPairMem 𝒞 (.bound 0) (.bound 1)
          relation.weaken.weaken

/-- `field` 是关系定义域和值域的并。 -/
def isField (𝒞 : OrderedPairConvention)
    {depth : Nat} (field relation : Term depth) : Formula 1 depth :=
  .existsE <| .existsE <| .existsE <|
    .conj
      (isDomain 𝒞 (.bound 2) relation.weaken.weaken.weaken) <|
      .conj
        (isRange 𝒞 (.bound 1) relation.weaken.weaken.weaken) <|
        .conj
          (isUnorderedPair (.bound 0) (.bound 2) (.bound 1))
          (isUnion field.weaken.weaken.weaken (.bound 0))

/-- `function : source → target`。 -/
def isFunctionFromTo (𝒞 : OrderedPairConvention)
    {depth : Nat} (function source target : Term depth) : Formula 1 depth :=
  .conj (isFunction 𝒞 function) <|
    .conj (isDomain 𝒞 source function) <|
      Formula.forallMem source <|
        Formula.existsMem target.weaken <|
          orderedPairMem 𝒞 (.bound 1) (.bound 0)
            function.weaken.weaken

/-- 函数在其定义域上是单射。 -/
def isInjective (𝒞 : OrderedPairConvention)
    {depth : Nat} (function : Term depth) : Formula 1 depth :=
  .forallE <| .forallE <| .forallE <|
    .imp
      (.conj
        (orderedPairMem 𝒞 (.bound 2) (.bound 0)
          function.weaken.weaken.weaken)
        (orderedPairMem 𝒞 (.bound 1) (.bound 0)
          function.weaken.weaken.weaken))
        (extensionalEq (.bound 2) (.bound 1))

/-- `function` 把 `source` 覆盖到 `target`。 -/
def isSurjectiveOnto (𝒞 : OrderedPairConvention)
    {depth : Nat} (function source target : Term depth) : Formula 1 depth :=
  Formula.forallMem target <|
    Formula.existsMem source.weaken <|
      orderedPairMem 𝒞 Term.newest (.bound 1)
        function.weaken.weaken

/-- `restriction` 是 `function` 在 `source` 上的限制。 -/
def isRestriction (𝒞 : OrderedPairConvention)
    {depth : Nat} (restriction function source : Term depth) :
    Formula 1 depth :=
  .conj (isRelation 𝒞 restriction) <|
    .forallE <| .forallE <|
      .iff
        (orderedPairMem 𝒞 (.bound 1) (.bound 0)
          restriction.weaken.weaken)
        (.conj (.mem (.bound 1) source.weaken.weaken)
          (orderedPairMem 𝒞 (.bound 1) (.bound 0)
            function.weaken.weaken))

/-- `composition` 是 `left ∘ right`。 -/
def isComposition (𝒞 : OrderedPairConvention)
    {depth : Nat} (composition left right : Term depth) :
    Formula 1 depth :=
  .forallE <| .forallE <|
    .iff
      (orderedPairMem 𝒞 (.bound 1) (.bound 0)
        composition.weaken.weaken)
      (.existsE <|
        .conj
          (orderedPairMem 𝒞 (.bound 2) (.bound 0)
            right.weaken.weaken.weaken)
          (orderedPairMem 𝒞 (.bound 0) (.bound 1)
            left.weaken.weaken.weaken))

/-- `image` 是 `function` 在 `source` 上的像。 -/
def isImage (𝒞 : OrderedPairConvention)
    {depth : Nat} (image function source : Term depth) : Formula 1 depth :=
  .forallE <|
    .iff (.mem Term.newest image.weaken) <|
      Formula.existsMem source.weaken <|
        orderedPairMem 𝒞 (.bound 0) (.bound 1)
          function.weaken.weaken

/-- `preimage` 是 `target` 在 `function` 下的逆像。 -/
def isPreimage (𝒞 : OrderedPairConvention)
    {depth : Nat} (preimage function target : Term depth) :
    Formula 1 depth :=
  .forallE <|
    .iff (.mem Term.newest preimage.weaken) <|
      Formula.existsMem target.weaken <|
        orderedPairMem 𝒞 (.bound 1) (.bound 0)
          function.weaken.weaken

/-- `identity` 是 `set` 上的恒等函数。 -/
def isIdentityOn (𝒞 : OrderedPairConvention)
    {depth : Nat} (identity set : Term depth) : Formula 1 depth :=
  .forallE <| .forallE <|
    .iff
      (orderedPairMem 𝒞 (.bound 1) (.bound 0)
        identity.weaken.weaken)
      (.conj (.mem (.bound 1) set.weaken.weaken)
        (extensionalEq (.bound 1) (.bound 0)))

end Formula

end Project
end Definitional
end SetTheory
end YesMetaZFC
