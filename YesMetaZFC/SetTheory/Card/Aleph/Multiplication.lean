import YesMetaZFC.SetTheory.Card.Aleph.Recursion
import YesMetaZFC.SetTheory.Card.Arithmetic.Multiplication
import YesMetaZFC.SetTheory.Ord.CanonicalPairing
import YesMetaZFC.SetTheory.Ord.Natural

/-!
# Aleph 数的乘法

本层沿定理 3.5 的典范序数对良序路线，先补齐良序集取基数所需的初始序数接口，
再把典范方块序型用于无限基数的自乘。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace ZF

/-- 从给定序数的后继中分离与该序数等势的序数。 -/
private def ordinalCardinalCandidate
    (𝒞 : Definitional.Project.OrderedPairConvention) :
    Definitional.Project.UnarySchema 1 where
  body := .conj
    (Definitional.Project.Formula.isOrdinal (.bound 0))
    (Definitional.Project.Formula.equinumerous 𝒞
      (.bound 0) (.bound 1))
  freeClosed := by
    simp [Definitional.Project.Formula.isOrdinal,
      Definitional.Project.Formula.isTransitive,
      Definitional.Project.Formula.isWellOrderOn,
      Definitional.Project.Formula.isLinearOrderOn,
      Definitional.Project.Formula.isStrictPartialOrderOn,
      Definitional.Project.Formula.isIrreflexiveOn,
      Definitional.Project.Formula.isTransitiveOn,
      Definitional.Project.Formula.isLeastOf,
      Definitional.Project.Formula.lessOrEqual,
      Definitional.Project.Formula.equinumerous,
      Definitional.Project.Formula.isBijectionFromTo,
      Definitional.Project.Formula.isInjectionFromTo,
      Definitional.Project.Formula.isFunctionFromTo,
      Definitional.Project.Formula.isFunction,
      Definitional.Project.Formula.isRelation,
      Definitional.Project.Formula.isDomain,
      Definitional.Project.Formula.isSurjectiveOnto,
      Definitional.Project.Formula.isInjective,
      Definitional.Project.Formula.orderedPairMem,
      Definitional.Project.Formula.forallMem,
      Definitional.Project.Formula.existsMem,
      Definitional.Project.Formula.subset,
      Definitional.Project.Formula.extensionalEq,
      Definitional.Formula.FreeClosed,
      Definitional.Term.newest]

/-- “当前无限基数对自乘封闭”的一参数分离模式。 -/
private def infiniteCardinalSelfMultiplicationAt
    (𝒞 : Definitional.Project.OrderedPairConvention) :
    Definitional.Project.UnarySchema 1 where
  body := .imp
    (Definitional.Project.Formula.isInfiniteCardinal 𝒞
      (.bound 1) (.bound 0))
    (Definitional.Project.Formula.isCardinalMultiplication 𝒞
      (.bound 0) (.bound 0) (.bound 0))
  freeClosed := by
    simp [Definitional.Project.Formula.isInfiniteCardinal,
      Definitional.Project.Formula.isCardinalMultiplication,
      Definitional.Project.Formula.isCardinalOf,
      Definitional.Project.Formula.isCardinal,
      Definitional.Project.Formula.cardinalLessOrEqual,
      Definitional.Project.Formula.equinumerous,
      Definitional.Project.Formula.isBijectionFromTo,
      Definitional.Project.Formula.isInjectionFromTo,
      Definitional.Project.Formula.isFunctionFromTo,
      Definitional.Project.Formula.isFunction,
      Definitional.Project.Formula.isRelation,
      Definitional.Project.Formula.isDomain,
      Definitional.Project.Formula.isSurjectiveOnto,
      Definitional.Project.Formula.isInjective,
      Definitional.Project.Formula.isCartesianProduct,
      Definitional.Project.Formula.isOrdinal,
      Definitional.Project.Formula.isTransitive,
      Definitional.Project.Formula.isWellOrderOn,
      Definitional.Project.Formula.isLinearOrderOn,
      Definitional.Project.Formula.isStrictPartialOrderOn,
      Definitional.Project.Formula.isIrreflexiveOn,
      Definitional.Project.Formula.isTransitiveOn,
      Definitional.Project.Formula.isLeastOf,
      Definitional.Project.Formula.lessOrEqual,
      Definitional.Project.Formula.orderedPairMem,
      Definitional.Project.Formula.forallMem,
      Definitional.Project.Formula.existsMem,
      Definitional.Project.Formula.subset,
      Definitional.Project.Formula.extensionalEq,
      Definitional.Formula.FreeClosed,
      Definitional.Term.newest]

/-- 序数基数候选模式的模型语义。 -/
private theorem satisfies_ordinalCardinalCandidate_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 1) (candidate : ℳ.Domain) :
    Definitional.Project.Formula.satisfies
        (env.push candidate) (ordinalCardinalCandidate 𝒞).body ↔
      ℳ.IsOrdinal candidate ∧
        ℳ.Equinumerous 𝕀 candidate (env.bound 0) := by
  simp only [ordinalCardinalCandidate,
    Definitional.Project.Formula.satisfies_conj_iff,
    Definitional.Project.Formula.satisfies_isOrdinal_iff,
    Definitional.Project.Formula.satisfies_equinumerous_iff 𝕀 hExt,
    Definitional.Project.Term.eval_bound_zero_push,
    Definitional.Project.Term.eval_bound_one_push]
  rfl

/-- 无限基数自乘封闭模式的模型语义。 -/
private theorem satisfies_infiniteCardinalSelfMultiplicationAt_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 1) (cardinal : ℳ.Domain) :
    Definitional.Project.Formula.satisfies
        (env.push cardinal)
        (infiniteCardinalSelfMultiplicationAt 𝒞).body ↔
      (ℳ.IsInfiniteCardinal 𝕀 (env.bound 0) cardinal →
        ℳ.IsCardinalMultiplication 𝕀
          cardinal cardinal cardinal) := by
  simp only [infiniteCardinalSelfMultiplicationAt,
    Definitional.Project.Formula.satisfies_imp_iff,
    Definitional.Project.Formula.satisfies_isInfiniteCardinal_iff
      𝕀 hExt,
    Definitional.Project.Formula.satisfies_isCardinalMultiplication_iff
      𝕀 hExt,
    Definitional.Project.Term.eval_bound_zero_push,
    Definitional.Project.Term.eval_bound_one_push]
  change
    (ℳ.IsInfiniteCardinal 𝕀 (env.bound 0) cardinal →
      ℳ.IsCardinalMultiplication 𝕀 cardinal cardinal cardinal) ↔ _
  rfl

/-- 每个序数都有唯一的基数代表。 -/
theorem ordinalCardinal_existsUnique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {α : ℳ.Domain} (hα : ℳ.IsOrdinal α) :
    ∃ κ,
      ℳ.IsCardinalOf 𝕀 κ α ∧
        ∀ μ, ℳ.IsCardinalOf 𝕀 μ α → μ = κ := by
  rcases KP.exists_successor (ZF.modelsKP hZF) α with
    ⟨successor, hSuccessor⟩
  have hSuccessorOrdinal :
      ℳ.IsOrdinal successor :=
    KP.successor_isOrdinal (ZF.modelsKP hZF) hα hSuccessor
  let env : Env ℳ 1 := {
    bound := fun _ => α
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_separation hZF
      (ordinalCardinalCandidate 𝒞) env successor with
    ⟨candidates, hCandidatesRaw⟩
  have hCandidates (candidate : ℳ.Domain) :
      ℳ.mem candidate candidates ↔
        ℳ.mem candidate successor ∧
          ℳ.IsOrdinal candidate ∧
            ℳ.Equinumerous 𝕀 candidate α := by
    rw [hCandidatesRaw candidate,
      satisfies_ordinalCardinalCandidate_iff 𝕀 hZF.1 env candidate]
  have hCandidatesSubset :
      ℳ.MemberSubset candidates successor := by
    intro candidate hCandidate
    exact (hCandidates candidate).mp hCandidate |>.1
  have hαSuccessor : ℳ.mem α successor :=
    (hSuccessor α).mpr <| Or.inr fun _ => Iff.rfl
  have hαCandidate : ℳ.mem α candidates :=
    (hCandidates α).mpr
      ⟨hαSuccessor, hα,
        Structure.Equinumerous.refl hZF 𝕀 α⟩
  rcases hSuccessorOrdinal.wellOrder.least candidates
      hCandidatesSubset ⟨α, hαCandidate⟩ with
    ⟨κ, hκCandidate, hκLeast⟩
  rcases (hCandidates κ).mp hκCandidate with
    ⟨hκSuccessor, hκOrdinal, hκEquinumerous⟩
  have hκCardinal : ℳ.IsCardinal 𝕀 κ := by
    refine ⟨hκOrdinal, ?_⟩
    intro β hβκ hβκEquinumerous
    have hβOrdinal : ℳ.IsOrdinal β :=
      hκOrdinal.mem hβκ
    have hβSuccessor : ℳ.mem β successor := by
      rcases (hSuccessor κ).mp hκSuccessor with
        hκα | hκSame
      · exact (hSuccessor β).mpr <| Or.inl <|
          hα.transitive κ hκα β hβκ
      · have hκEq := hZF.1.eq_of_same_members κ α hκSame
        subst κ
        exact (hSuccessor β).mpr <| Or.inl hβκ
    have hβEquinumerousα :
        ℳ.Equinumerous 𝕀 β α :=
      hβκEquinumerous.trans hZF 𝕀 hκEquinumerous
    have hβCandidate : ℳ.mem β candidates :=
      (hCandidates β).mpr
        ⟨hβSuccessor, hβOrdinal, hβEquinumerousα⟩
    rcases hκLeast β hβCandidate with
      hSame | hκβ
    · have hEq := hZF.1.eq_of_same_members κ β hSame
      subst β
      exact hκOrdinal.wellOrder.linear.irrefl κ hβκ hβκ
    · have hSelf : ℳ.mem κ κ :=
        hκOrdinal.transitive β hβκ κ hκβ
      exact hκOrdinal.wellOrder.linear.irrefl κ hSelf hSelf
  have hκCardinalOf : ℳ.IsCardinalOf 𝕀 κ α :=
    ⟨hκCardinal, hκEquinumerous⟩
  exact ⟨κ, hκCardinalOf, fun μ hμ =>
    hμ.eq hZF 𝕀 hκCardinalOf⟩

/--
无限初始序数是极限序数。

若它是某个序数的后继，则 `ω` 已包含在该前驱中；后继吸收双射会使此前驱与该基数
等势，违反初始序数的最小性。
-/
theorem infiniteCardinal_isLimitOrdinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω κ : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hωCardinal : ℳ.IsCardinal 𝕀 ω)
    (hκ : ℳ.IsInfiniteCardinal 𝕀 ω κ) :
    ℳ.IsLimitOrdinal κ := by
  have hωOrdinal := hω.isOrdinal hZF
  have hκOrdinal := hκ.1.1
  rcases Structure.IsOrdinal.trichotomy hZF.1
      hωOrdinal hκOrdinal
      (KP.exists_difference (ZF.modelsKP hZF))
      (KP.exists_intersection (ZF.modelsKP hZF) ω κ) with
    hSame | hωκ | hκω
  · have hEq := hZF.1.eq_of_same_members ω κ hSame
    simpa [← hEq] using hω.isLimitOrdinal hZF
  · refine ⟨hκOrdinal, ⟨ω, hωκ⟩, ?_⟩
    intro predecessor hPredecessor
    have hPredecessorOrdinal :=
      hκOrdinal.mem hPredecessor
    rcases KP.exists_successor (ZF.modelsKP hZF) predecessor with
      ⟨successor, hSuccessor⟩
    have hSuccessorOrdinal :=
      KP.successor_isOrdinal (ZF.modelsKP hZF)
        hPredecessorOrdinal hSuccessor
    rcases Structure.IsOrdinal.trichotomy hZF.1
        hSuccessorOrdinal hκOrdinal
        (KP.exists_difference (ZF.modelsKP hZF))
        (KP.exists_intersection (ZF.modelsKP hZF)
          successor κ) with
      hSuccessorSame | hSuccessorκ | hκSuccessor
    · have hSuccessorEq :=
        hZF.1.eq_of_same_members successor κ hSuccessorSame
      have hOmegaSubset :
          ℳ.MemberSubset ω predecessor := by
        intro value hValue
        have hOmegaSuccessor : ℳ.mem ω successor := by
          simpa [hSuccessorEq] using hωκ
        rcases (hSuccessor ω).mp hOmegaSuccessor with
          hOmegaPredecessor | hOmegaSame
        · exact hPredecessorOrdinal.transitive
            ω hOmegaPredecessor value hValue
        · have hOmegaEq :=
            hZF.1.eq_of_same_members ω predecessor hOmegaSame
          simpa [hOmegaEq] using hValue
      have hEquinumerous :=
        equinumerous_successor_of_omegaSubset
          hZF 𝕀 hω hOmegaSubset hSuccessor
      exact False.elim <| hκ.1.2 predecessor hPredecessor <| by
        simpa [hSuccessorEq] using
          hEquinumerous.symm hZF 𝕀
    · exact ⟨successor, hSuccessorκ,
        hSuccessor.predecessor_mem⟩
    · rcases (hSuccessor κ).mp hκSuccessor with
        hκPredecessor | hκSame
      · have hSelf : ℳ.mem κ κ :=
          hκOrdinal.transitive predecessor hPredecessor
            κ hκPredecessor
        exact False.elim <|
          hκOrdinal.wellOrder.linear.irrefl κ hSelf hSelf
      · have hEq :=
          hZF.1.eq_of_same_members κ predecessor hκSame
        subst predecessor
        exact False.elim <|
          hκOrdinal.wellOrder.linear.irrefl
            κ hPredecessor hPredecessor
  · have hκToω :
        ℳ.CardinalLessOrEqual 𝕀 κ ω :=
      exists_inclusionInjection hZF 𝕀 <|
        hωOrdinal.transitive κ hκω
    have hEquinumerous :=
      equinumerous_of_cardinalLessOrEqual
        hZF 𝕀 hκ.2 hκToω
    have hEq :=
      hωCardinal.eq_of_equinumerous
        hZF 𝕀 hκ.1 hEquinumerous
    subst κ
    exact False.elim <|
      hωOrdinal.wellOrder.linear.irrefl
        ω hκω hκω

/--
若无限基数方块的典范序型不严格高于该基数，则该基数与自身的笛卡尔积等势。

下界由方块中的固定行给出，上界使用典范序型和 Cantor--Bernstein。
-/
theorem infiniteCardinal_selfMultiplication_of_orderType_not_above
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω κ ordinal : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hκ : ℳ.IsInfiniteCardinal 𝕀 ω κ)
    (hType : ℳ.IsCanonicalOrdinalPairOrderType 𝕀 ordinal κ)
    (hNotAbove : ¬ ℳ.mem κ ordinal) :
    ℳ.IsCardinalMultiplication 𝕀 κ κ κ := by
  rcases hType.equinumerous hZF 𝕀 with
    ⟨carrier, hCarrier, hCarrierOrdinal⟩
  rcases hω.1.1 with ⟨zero, hZero, hZeroOmega⟩
  rcases hκ.2 with ⟨omegaToκ, hOmegaToκ⟩
  rcases hOmegaToκ.1.2.2 zero hZeroOmega with
    ⟨tag, hTagκ, _⟩
  rcases ZF.exists_cartesianRow hZF 𝕀 tag κ with
    ⟨row, hRow⟩
  have hRowSubset : ℳ.MemberSubset row carrier := by
    intro pair hPair
    rcases (hRow pair).mp hPair with
      ⟨value, hValue, hCode⟩
    exact (hCarrier pair).mpr
      ⟨tag, hTagκ, value, hValue, hCode⟩
  rcases ZF.equinumerous_cartesianRow hZF 𝕀 hRow with
    ⟨κToRow, hκToRow⟩
  rcases ZF.exists_inclusionInjection hZF 𝕀 hRowSubset with
    ⟨rowToCarrier, hRowToCarrier⟩
  rcases ZF.exists_compositionInjection hZF 𝕀
      hκToRow.1 hRowToCarrier with
    ⟨κToCarrier, hκToCarrier⟩
  rcases hCarrierOrdinal with
    ⟨carrierToOrdinal, hCarrierToOrdinal⟩
  rcases ZF.exists_compositionInjection hZF 𝕀
      hκToCarrier hCarrierToOrdinal.1 with
    ⟨κToOrdinal, hκToOrdinal⟩
  have hOrdinal : ℳ.IsOrdinal ordinal :=
    hType.isOrdinal hZF 𝕀
  have hOrdinalEq : ordinal = κ := by
    rcases Structure.IsOrdinal.trichotomy hZF.1
        hOrdinal hκ.1.1
        (KP.exists_difference (ZF.modelsKP hZF))
        (KP.exists_intersection (ZF.modelsKP hZF)
          ordinal κ) with
      hSame | hOrdinalκ | hκOrdinal
    · exact hZF.1.eq_of_same_members ordinal κ hSame
    · have hOrdinalToκ :
          ℳ.CardinalLessOrEqual 𝕀 ordinal κ :=
        ZF.exists_inclusionInjection hZF 𝕀 <|
          hκ.1.1.transitive ordinal hOrdinalκ
      have hκToOrdinal :
          ℳ.CardinalLessOrEqual 𝕀 κ ordinal :=
        ⟨κToOrdinal, hκToOrdinal⟩
      have hEquinumerous :=
        ZF.equinumerous_of_cardinalLessOrEqual hZF 𝕀
          hOrdinalToκ hκToOrdinal
      exact False.elim <|
        hκ.1.2 ordinal hOrdinalκ hEquinumerous
    · exact False.elim <| hNotAbove hκOrdinal
  subst ordinal
  have hκCarrier :
      ℳ.Equinumerous 𝕀 κ carrier :=
    Structure.Equinumerous.symm hZF 𝕀
      ⟨carrierToOrdinal, hCarrierToOrdinal⟩
  have hκCardinalOf : ℳ.IsCardinalOf 𝕀 κ κ :=
    ⟨hκ.1, Structure.Equinumerous.refl hZF 𝕀 κ⟩
  exact ⟨κ, κ, carrier,
    hκCardinalOf, hκCardinalOf,
    hCarrier, ⟨hκ.1, hκCarrier⟩⟩

/--
定理 3.5 的前段有界核心。

若每个坐标最大值后继的方块都能单射到 `κ` 中某个更小序数，则典范方块序型不可能
严格高于 `κ`。
-/
theorem infiniteCardinal_selfMultiplication_of_successorSquareBound
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω κ ordinal : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hκ : ℳ.IsInfiniteCardinal 𝕀 ω κ)
    (hType : ℳ.IsCanonicalOrdinalPairOrderType 𝕀 ordinal κ)
    (hBound :
      ∀ maximum, ℳ.mem maximum κ →
        ∀ successor, ℳ.SuccessorOf successor maximum →
          ∀ square,
            ℳ.IsCartesianProduct 𝕀 square successor successor →
              ∃ bound,
                ℳ.mem bound κ ∧
                  ℳ.CardinalLessOrEqual 𝕀 square bound) :
    ℳ.IsCardinalMultiplication 𝕀 κ κ κ := by
  apply infiniteCardinal_selfMultiplication_of_orderType_not_above
    hZF 𝕀 hω hκ hType
  intro hκOrdinal
  rcases
      hType.member_equinumerous_predecessorSet_boundedByMaximumSquare
        hZF 𝕀 hκ.1.1 hκOrdinal with
    ⟨maximum, successor, square, predecessors,
      hMaximumκ, hSuccessor, hSquare,
      hPredecessorsSubset, hPredecessorsκ⟩
  rcases hBound maximum hMaximumκ successor hSuccessor square hSquare with
    ⟨bound, hBoundκ, hSquareBound⟩
  rcases hPredecessorsκ.symm hZF 𝕀 with
    ⟨κToPredecessors, hκToPredecessors⟩
  rcases exists_inclusionInjection hZF 𝕀
      hPredecessorsSubset with
    ⟨predecessorsToSquare, hPredecessorsToSquare⟩
  rcases exists_compositionInjection hZF 𝕀
      hκToPredecessors.1 hPredecessorsToSquare with
    ⟨κToSquare, hκToSquare⟩
  rcases hSquareBound with
    ⟨squareToBound, hSquareToBound⟩
  rcases exists_compositionInjection hZF 𝕀
      hκToSquare hSquareToBound with
    ⟨κToBound, hκToBound⟩
  have hBoundToκ :
      ℳ.CardinalLessOrEqual 𝕀 bound κ :=
    exists_inclusionInjection hZF 𝕀 <|
      hκ.1.1.transitive bound hBoundκ
  have hκToBound :
      ℳ.CardinalLessOrEqual 𝕀 κ bound :=
    ⟨κToBound, hκToBound⟩
  have hκBoundEquinumerous :=
    equinumerous_of_cardinalLessOrEqual
      hZF 𝕀 hκToBound hBoundToκ
  exact hκ.1.2 bound hBoundκ <|
    hκBoundEquinumerous.symm hZF 𝕀

/--
若某个集合由自乘封闭基数表示，则该集合的方块单射到该基数。
-/
theorem cartesianSquare_cardinalLessOrEqual_of_selfMultiplication
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {set square κ : ℳ.Domain}
    (hκSet : ℳ.IsCardinalOf 𝕀 κ set)
    (hSquare : ℳ.IsCartesianProduct 𝕀 square set set)
    (hκMultiplication :
      ℳ.IsCardinalMultiplication 𝕀 κ κ κ) :
    ℳ.CardinalLessOrEqual 𝕀 square κ := by
  rcases hκMultiplication with
    ⟨leftSet, rightSet, product,
      hκLeft, hκRight, hProduct, hκProduct⟩
  have hSetLeft :
      ℳ.Equinumerous 𝕀 set leftSet :=
    hκSet.2.symm hZF 𝕀 |>.trans hZF 𝕀 hκLeft.2
  have hSetRight :
      ℳ.Equinumerous 𝕀 set rightSet :=
    hκSet.2.symm hZF 𝕀 |>.trans hZF 𝕀 hκRight.2
  rcases hSetLeft with
    ⟨leftFunction, hLeftFunction⟩
  rcases hSetRight with
    ⟨rightFunction, hRightFunction⟩
  have hSquareProduct :=
    equinumerous_cartesianProduct hZF 𝕀
      hSquare hProduct hLeftFunction hRightFunction
  have hSquareκ :
      ℳ.Equinumerous 𝕀 square κ :=
    hSquareProduct.trans hZF 𝕀 <|
      hκProduct.2.symm hZF 𝕀
  rcases hSquareκ with
    ⟨squareToκ, hSquareToκ⟩
  exact ⟨squareToκ, hSquareToκ.1⟩

/-- 自然数方块可单射到某个仍属于 `ω` 的序数。 -/
theorem cartesianSquare_bounded_in_omega
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω number square : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hNumber : ℳ.mem number ω)
    (hSquare :
      ℳ.IsCartesianProduct 𝕀 square number number) :
    ∃ bound,
      ℳ.mem bound ω ∧
        ℳ.CardinalLessOrEqual 𝕀 square bound := by
  have hNumberOrdinal :=
    hω.members_areOrdinals hZF number hNumber
  rcases ordinalMultiplication_existsUnique
      hZF 𝕀 number hNumberOrdinal with
    ⟨product, hProduct, _⟩
  have hProductOmega :=
    ordinalMultiplication_mem_omega
      hZF 𝕀 hω hNumber hNumber hProduct
  have hSquareProduct :=
    equinumerous_cartesianProduct_ordinalMultiplication
      hZF 𝕀 hNumberOrdinal hNumberOrdinal hSquare hProduct
  rcases hSquareProduct with
    ⟨squareToProduct, hSquareToProduct⟩
  exact ⟨product, hProductOmega,
    squareToProduct, hSquareToProduct.1⟩

/-- Cantor 配对基例：`ω · ω = ω`。 -/
theorem omega_selfMultiplication
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hωCardinal : ℳ.IsCardinal 𝕀 ω) :
    ℳ.IsCardinalMultiplication 𝕀 ω ω ω := by
  have hωInfinite :
      ℳ.IsInfiniteCardinal 𝕀 ω ω := by
    rcases Structure.Equinumerous.refl hZF 𝕀 ω with
      ⟨identity, hIdentity⟩
    exact ⟨hωCardinal, identity, hIdentity.1⟩
  rcases canonicalOrdinalPairOrderType_existsUnique
      hZF 𝕀 (hω.isOrdinal hZF) with
    ⟨ordinal, hType, _⟩
  apply infiniteCardinal_selfMultiplication_of_successorSquareBound
    hZF 𝕀 hω hωInfinite hType
  intro maximum hMaximum successor hSuccessor square hSquare
  rcases hω.1.2 maximum hMaximum with
    ⟨selected, hSelected, hSelectedOmega⟩
  have hSelectedEq :=
    Structure.SuccessorOf.eq hZF.1 hSelected hSuccessor
  apply cartesianSquare_bounded_in_omega
    hZF 𝕀 hω
  · simpa [hSelectedEq] using hSelectedOmega
  · exact hSquare

/--
定理 3.5 的最小反例递推步。

若 `κ` 以下每个坐标最大值的后继都有一个严格小于 `κ`、且已对自乘闭合的基数代表，
则 `κ` 的典范方块序型不可能严格高于 `κ`。
-/
theorem infiniteCardinal_selfMultiplication_of_successorCardinalClosure
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω κ ordinal : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hκ : ℳ.IsInfiniteCardinal 𝕀 ω κ)
    (hType : ℳ.IsCanonicalOrdinalPairOrderType 𝕀 ordinal κ)
    (hClosure :
      ∀ maximum, ℳ.mem maximum κ →
        ∀ successor, ℳ.SuccessorOf successor maximum →
          ∃ μ,
            ℳ.IsCardinalOf 𝕀 μ successor ∧
              ℳ.mem μ κ ∧
                ℳ.IsCardinalMultiplication 𝕀 μ μ μ) :
    ℳ.IsCardinalMultiplication 𝕀 κ κ κ := by
  apply infiniteCardinal_selfMultiplication_of_successorSquareBound
    hZF 𝕀 hω hκ hType
  intro maximum hMaximumκ successor hSuccessor square hSquare
  rcases hClosure maximum hMaximumκ successor hSuccessor with
    ⟨μ, hμSuccessor, hμκ, hμMultiplication⟩
  exact ⟨μ, hμκ,
    cartesianSquare_cardinalLessOrEqual_of_selfMultiplication
      hZF 𝕀 hμSuccessor hSquare hμMultiplication⟩

/-- 定理 3.5：每个无限基数都满足 `κ · κ = κ`。 -/
theorem infiniteCardinal_selfMultiplication
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω κ : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hωCardinal : ℳ.IsCardinal 𝕀 ω)
    (hκ : ℳ.IsInfiniteCardinal 𝕀 ω κ) :
    ℳ.IsCardinalMultiplication 𝕀 κ κ κ := by
  let env : Env ℳ 1 := {
    bound := fun _ => ω
    free := fun _ => Classical.choice ℳ.nonempty
  }
  let property : ℳ.Domain → Prop := fun current =>
    ℳ.IsInfiniteCardinal 𝕀 ω current →
      ℳ.IsCardinalMultiplication 𝕀 current current current
  have hProperty : property κ := by
    apply hκ.1.1.induction property
    · rcases exists_separation hZF
          (infiniteCardinalSelfMultiplicationAt 𝒞).neg env κ with
        ⟨counterexamples, hCounterexamples⟩
      refine ⟨counterexamples, fun current => ?_⟩
      rw [hCounterexamples current]
      simp only [Definitional.Project.UnarySchema.neg,
        Definitional.Project.Formula.satisfies_neg_iff,
        satisfies_infiniteCardinalSelfMultiplicationAt_iff
          𝕀 hZF.1 env current]
      change
        (ℳ.mem current κ ∧
          ¬ (ℳ.IsInfiniteCardinal 𝕀 ω current →
            ℳ.IsCardinalMultiplication 𝕀
              current current current)) ↔
        ℳ.mem current κ ∧ ¬ property current
      rfl
    · intro current hCurrent hPrevious hCurrentInfinite
      have hωOrdinal := hω.isOrdinal hZF
      rcases Structure.IsOrdinal.trichotomy hZF.1
          hωOrdinal hCurrent
          (KP.exists_difference (ZF.modelsKP hZF))
          (KP.exists_intersection (ZF.modelsKP hZF)
            ω current) with
        hSame | hωCurrent | hCurrentω
      · have hEq :=
          hZF.1.eq_of_same_members ω current hSame
        simpa [← hEq] using
          omega_selfMultiplication hZF 𝕀 hω hωCardinal
      · rcases canonicalOrdinalPairOrderType_existsUnique
            hZF 𝕀 hCurrent with
          ⟨ordinal, hType, _⟩
        apply infiniteCardinal_selfMultiplication_of_successorSquareBound
          hZF 𝕀 hω hCurrentInfinite hType
        intro maximum hMaximum successor hSuccessor square hSquare
        have hCurrentLimit :=
          infiniteCardinal_isLimitOrdinal
            hZF 𝕀 hω hωCardinal hCurrentInfinite
        rcases hCurrentLimit.2.2 maximum hMaximum with
          ⟨larger, hLargerCurrent, hMaximumLarger⟩
        have hMaximumOrdinal :=
          hCurrent.mem hMaximum
        have hSuccessorOrdinal :=
          KP.successor_isOrdinal (ZF.modelsKP hZF)
            hMaximumOrdinal hSuccessor
        have hLargerOrdinal :=
          hCurrent.mem hLargerCurrent
        have hSuccessorCurrent : ℳ.mem successor current := by
          rcases Structure.IsOrdinal.trichotomy hZF.1
              hSuccessorOrdinal hLargerOrdinal
              (KP.exists_difference (ZF.modelsKP hZF))
              (KP.exists_intersection (ZF.modelsKP hZF)
                successor larger) with
            hSame | hSuccessorLarger | hLargerSuccessor
          · have hEq :=
              hZF.1.eq_of_same_members successor larger hSame
            simpa [hEq] using hLargerCurrent
          · exact hCurrent.transitive
              larger hLargerCurrent successor hSuccessorLarger
          · rcases (hSuccessor larger).mp hLargerSuccessor with
              hLargerMaximum | hLargerSame
            · have hSelf : ℳ.mem larger larger :=
                hLargerOrdinal.transitive
                  maximum hMaximumLarger larger hLargerMaximum
              exact False.elim <|
                hLargerOrdinal.wellOrder.linear.irrefl
                  larger hSelf hSelf
            · have hEq :=
                hZF.1.eq_of_same_members larger maximum hLargerSame
              subst larger
              exact False.elim <|
                hMaximumOrdinal.wellOrder.linear.irrefl
                  maximum hMaximumLarger hMaximumLarger
        rcases ordinalCardinal_existsUnique
            hZF 𝕀 hSuccessorOrdinal with
          ⟨μ, hμSuccessor, _⟩
        have hμCurrent : ℳ.mem μ current := by
          rcases Structure.IsOrdinal.trichotomy hZF.1
              hμSuccessor.1.1 hSuccessorOrdinal
              (KP.exists_difference (ZF.modelsKP hZF))
              (KP.exists_intersection (ZF.modelsKP hZF)
                μ successor) with
            hSame | hμSuccessorMem | hSuccessorμ
          · have hEq :=
              hZF.1.eq_of_same_members μ successor hSame
            simpa [hEq] using hSuccessorCurrent
          · exact hCurrent.transitive
              successor hSuccessorCurrent μ hμSuccessorMem
          · exact False.elim <|
              hμSuccessor.1.2 successor hSuccessorμ <|
                hμSuccessor.2.symm hZF 𝕀
        rcases Structure.IsOrdinal.trichotomy hZF.1
            hμSuccessor.1.1 hωOrdinal
            (KP.exists_difference (ZF.modelsKP hZF))
            (KP.exists_intersection (ZF.modelsKP hZF)
              μ ω) with
          hμSame | hμω | hωμ
        · have hμEq :=
            hZF.1.eq_of_same_members μ ω hμSame
          have hμInfinite :
              ℳ.IsInfiniteCardinal 𝕀 ω μ := by
            simpa [hμEq] using
              (show ℳ.IsInfiniteCardinal 𝕀 ω ω from
                ⟨hωCardinal,
                  exists_inclusionInjection hZF 𝕀 fun _ h => h⟩)
          exact ⟨μ, hμCurrent,
            cartesianSquare_cardinalLessOrEqual_of_selfMultiplication
              hZF 𝕀 hμSuccessor hSquare <|
                hPrevious μ hμCurrent hμInfinite⟩
        · rcases exists_cartesianProduct hZF 𝕀 μ μ with
            ⟨μSquare, hμSquare⟩
          rcases hμSuccessor.2.symm hZF 𝕀 with
            ⟨successorToμ, hSuccessorToμ⟩
          have hSquareμSquare :=
            equinumerous_cartesianProduct
              hZF 𝕀 hSquare hμSquare
                hSuccessorToμ hSuccessorToμ
          rcases ordinalMultiplication_existsUnique
              hZF 𝕀 μ hμSuccessor.1.1 with
            ⟨product, hProduct, _⟩
          have hμSquareProduct :=
            equinumerous_cartesianProduct_ordinalMultiplication
              hZF 𝕀 hμSuccessor.1.1 hμSuccessor.1.1
                hμSquare hProduct
          have hProductOmega :=
            ordinalMultiplication_mem_omega
              hZF 𝕀 hω hμω hμω hProduct
          have hProductCurrent :=
            hCurrent.transitive ω hωCurrent product hProductOmega
          have hSquareProduct :=
            hSquareμSquare.trans hZF 𝕀 hμSquareProduct
          rcases hSquareProduct with
            ⟨squareToProduct, hSquareToProduct⟩
          exact ⟨product, hProductCurrent,
            squareToProduct, hSquareToProduct.1⟩
        · have hμInfinite :
              ℳ.IsInfiniteCardinal 𝕀 ω μ :=
            ⟨hμSuccessor.1,
              exists_inclusionInjection hZF 𝕀 <|
                hμSuccessor.1.1.transitive ω hωμ⟩
          exact ⟨μ, hμCurrent,
            cartesianSquare_cardinalLessOrEqual_of_selfMultiplication
              hZF 𝕀 hμSuccessor hSquare <|
                hPrevious μ hμCurrent hμInfinite⟩
      · have hCurrentToω :
            ℳ.CardinalLessOrEqual 𝕀 current ω :=
          exists_inclusionInjection hZF 𝕀 <|
            hωOrdinal.transitive current hCurrentω
        have hEquinumerous :=
          equinumerous_of_cardinalLessOrEqual
            hZF 𝕀 hCurrentInfinite.2 hCurrentToω
        have hEq :=
          hωCardinal.eq_of_equinumerous
            hZF 𝕀 hCurrentInfinite.1 hEquinumerous
        subst current
        exact False.elim <|
          hωOrdinal.wellOrder.linear.irrefl
            ω hCurrentω hCurrentω
  exact hProperty hκ

/-- 每个 Aleph 数都满足定理 3.5 的自乘方程。 -/
theorem aleph_selfMultiplication
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω index value : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hωCardinal : ℳ.IsCardinal 𝕀 ω)
    (hIndex : ℳ.IsOrdinal index)
    (hValue : ℳ.IsAlephNumber 𝕀 ω index value) :
    ℳ.IsCardinalMultiplication 𝕀 value value value :=
  infiniteCardinal_selfMultiplication
    hZF 𝕀 hω hωCardinal <|
      aleph_isInfiniteCardinal
        hZF 𝕀 hωCardinal hIndex hValue

end ZF

end SetTheory
end YesMetaZFC
