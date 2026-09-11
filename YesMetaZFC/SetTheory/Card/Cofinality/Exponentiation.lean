import YesMetaZFC.SetTheory.Card.Cofinality.Comparison
import YesMetaZFC.SetTheory.Card.Cofinality.LimitLength
import YesMetaZFC.SetTheory.Card.Arithmetic.Exponentiation
import YesMetaZFC.SetTheory.Separation
/-!
# 共尾度指数的严格下界
本层形式化定理 3.11。核心是模型内部对角化：给定一个以 `κ` 为定义域、取值于
`cf(κ) → κ` 函数空间的函数族，在每个坐标只观察共尾序列给出的一个严格较小初段，
并选择该初段尚未使用的最小值。所得函数不属于原函数族的值域。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Definitional
namespace Project
namespace BinarySchema
/--
在坐标 `index` 处，选择由共尾序列给出的初段尚未被函数族使用的最小 `κ` 成员。
-/
private def leastUnusedDiagonalValue (𝒞 : OrderedPairConvention) : BinarySchema 3 where
  body := .existsE <|
    .conj (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 0) (.bound 3)) <|
    .conj (.mem (.bound 1) (.bound 5)) <|
    .conj (.neg <| .existsE <|
        .conj (.mem (.bound 0) (.bound 1)) <|
          .existsE <| .conj (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 0) (.bound 6)) (Formula.orderedPairMem 𝒞 (.bound 4) (.bound 3) (.bound 0))) <|
      Formula.forallMem (.bound 1) <|
        .existsE <|
          .conj (.mem (.bound 0) (.bound 2)) <|
            .existsE <| .conj (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 0) (.bound 7)) (Formula.orderedPairMem 𝒞 (.bound 5) (.bound 2) (.bound 0))
end BinarySchema
namespace Formula
/-- 最小未用对角值模式的纸面解释。 -/
private theorem denote_leastUnusedDiagonalValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (env : Env ℳ 3) (index output : ℳ.Domain) :
    (BinarySchema.leastUnusedDiagonalValue 𝒞).denote
        env index output ↔
      ∃ stage,
        ℳ.PairMember 𝕀 index stage (env.bound 0) ∧
          ℳ.mem output (env.bound 2) ∧ (¬ ∃ row,
              ℳ.mem row stage ∧
                ∃ function,
                  ℳ.PairMember 𝕀 row function (env.bound 1) ∧
                    ℳ.PairMember 𝕀 index output function) ∧
              ∀ earlier, ℳ.mem earlier output →
                ∃ row,
                  ℳ.mem row stage ∧
                    ∃ function,
                      ℳ.PairMember 𝕀 row function (env.bound 1) ∧
                        ℳ.PairMember 𝕀 index earlier function := by
  simp only [BinarySchema.leastUnusedDiagonalValue,
    BinarySchema.denote, satisfies_exists_iff,
    satisfies_conj_iff, satisfies_neg_iff,
    satisfies_forallMem_iff, satisfies_mem_iff,
    satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push,
    Term.eval_bound_six_push, Term.eval_bound_seven_push]
  rfl
end Formula
end Project
end Definitional
namespace Structure.IsCofinalOrdinalSequence
/--
给定 `κ` 个 `cf → κ` 函数，构造一个与其中每个函数都不同的模型内部对角函数。
-/
private theorem exists_diagonalFunction
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {cofinalSequence cf κ space enumeration : ℳ.Domain} (hκ : ℳ.IsCardinal 𝕀 κ) (hCofinal :
      ℳ.IsCofinalOrdinalSequence 𝕀
        cofinalSequence cf κ) (hSpace :
      ℳ.IsFunctionSpace 𝕀 space cf κ) (hEnumeration :
      ℳ.IsSetFunctionFromTo 𝕀 enumeration κ space) :
    ∃ diagonal,
      ℳ.IsSetFunctionFromTo 𝕀 diagonal cf κ ∧
        ∀ row function,
          ℳ.mem row κ →
            ℳ.PairMember 𝕀 row function enumeration →
              diagonal ≠ function := by
  let env : Env ℳ 3 := {
    bound := Fin.cases cofinalSequence <|
      Fin.cases enumeration <| Fin.cases κ Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases ZF.exists_setFunctionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.leastUnusedDiagonalValue 𝒞)
      env (by
        intro index hIndex
        rcases hCofinal.isSetFunctionFromTo.2.2 index hIndex with
          ⟨stage, hStageκ, hIndexStage⟩
        have hStageSubset :
            ℳ.MemberSubset stage κ :=
          hκ.1.transitive stage hStageκ
        rcases ZF.exists_functionFamilyEvaluation
            hZF 𝕀 hEnumeration hStageSubset hSpace hIndex with
          ⟨evaluation, hEvaluation, hEvaluationPairs⟩
        rcases ZF.exists_range_of_setFunction
            hZF 𝕀 hEvaluation.1 hEvaluation.2.1 with
          ⟨evaluationRange, hEvaluationRange⟩
        have hNotSurjective :
            ¬ ℳ.IsSetSurjectiveOnto
              𝕀 evaluation stage κ := by
          intro hSurjective
          rcases ZF.exists_rightInverseInjection_of_surjection_from_ordinal
              hZF 𝕀 (hκ.1.mem hStageκ)
              hEvaluation hSurjective with
            ⟨κToStage, hκToStage⟩
          rcases ZF.exists_inclusionInjection
              hZF 𝕀 hStageSubset with
            ⟨stageToκ, hStageToκ⟩
          have hEquinumerous :=
            ZF.equinumerous_of_injections
              hZF 𝕀 hStageToκ hκToStage
          exact hκ.2 stage hStageκ hEquinumerous
        have hMissing :
            ∃ value,
              ℳ.mem value κ ∧
                ¬ ℳ.mem value evaluationRange := by
          apply Classical.byContradiction
          intro hNoMissing
          apply hNotSurjective
          intro value hValue
          have hValueRange :
              ℳ.mem value evaluationRange := by
            apply Classical.byContradiction
            intro hNotRange
            exact hNoMissing ⟨value, hValue, hNotRange⟩
          rcases (hEvaluationRange value).mp hValueRange with
            ⟨row, hRowValue⟩
          exact ⟨row,
            hEvaluation.input_mem_of_pairMember hRowValue,
            hRowValue⟩
        rcases KP.difference_exists_d (ZF.modelsKP hZF) evaluationRange κ with
          ⟨unused, hUnused⟩
        have hUnusedSubset :
            ℳ.MemberSubset unused κ := by
          intro value hValue
          exact ((hUnused value).mp hValue).1
        have hUnusedNonempty :
            ∃ value, ℳ.mem value unused := by
          rcases hMissing with
            ⟨value, hValueκ, hValueMissing⟩
          exact ⟨value, (hUnused value).mpr
              ⟨hValueκ, hValueMissing⟩⟩
        rcases hκ.1.wellOrder.least
            unused hUnusedSubset hUnusedNonempty with
          ⟨least, hLeastUnused, hLeast⟩
        have hLeastData := (hUnused least).mp hLeastUnused
        refine ⟨least, (Definitional.Project.Formula.denote_leastUnusedDiagonalValue_iff
            𝕀 env index least).mpr
              ⟨stage, hIndexStage, hLeastData.1, ?_, ?_⟩⟩
        · rintro ⟨row, hRowStage, function,
            hRowFunction, hIndexLeast⟩
          have hEvaluationPair :
              ℳ.PairMember 𝕀 row least evaluation := (hEvaluationPairs row least).mpr
              ⟨hRowStage, function,
                hRowFunction, hIndexLeast⟩
          exact hLeastData.2 <| (hEvaluationRange least).mpr
              ⟨row, hEvaluationPair⟩
        · intro earlier hEarlier
          apply Classical.byContradiction
          intro hEarlierUnused
          have hEarlierκ :
              ℳ.mem earlier κ :=
            hκ.1.transitive least hLeastData.1
              earlier hEarlier
          have hEarlierNotRange :
              ¬ ℳ.mem earlier evaluationRange := by
            intro hEarlierRange
            rcases (hEvaluationRange earlier).mp hEarlierRange with
              ⟨row, hRowEarlier⟩
            have hRowData := (hEvaluationPairs row earlier).mp hRowEarlier
            exact hEarlierUnused
              ⟨row, hRowData.1, hRowData.2⟩
          have hEarlierDifference :
              ℳ.mem earlier unused := (hUnused earlier).mpr
              ⟨hEarlierκ, hEarlierNotRange⟩
          rcases hLeast earlier hEarlierDifference with
            hSame | hLeastEarlier
          · have hEq :=
              hZF.1.eq_of_same_members least earlier hSame
            have hSelf : ℳ.mem least least := by
              simpa [hEq] using hEarlier
            exact hκ.1.wellOrder.linear.irrefl
              least hLeastData.1 hSelf
          · have hSelf : ℳ.mem least least := (hκ.1.mem hLeastData.1).transitive
                earlier hEarlier least hLeastEarlier
            exact hκ.1.wellOrder.linear.irrefl
              least hLeastData.1 hSelf) (by
        intro index _ first second hFirst hSecond
        rw [Definitional.Project.Formula.denote_leastUnusedDiagonalValue_iff
          𝕀] at hFirst hSecond
        rcases hFirst with
          ⟨firstStage, hFirstStage, hFirstκ,
            hFirstUnused, hFirstEarlier⟩
        rcases hSecond with
          ⟨secondStage, hSecondStage, hSecondκ,
            hSecondUnused, hSecondEarlier⟩
        have hStageEq :=
          hCofinal.isSetFunctionFromTo.1.2
            index firstStage secondStage
            hFirstStage hSecondStage
        subst secondStage
        rcases Structure.IsOrdinal.trichotomy hZF.1 (hκ.1.mem hFirstκ) (hκ.1.mem hSecondκ) (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d
              (ZF.modelsKP hZF) first second) with
          hSame | hFirstSecond | hSecondFirst
        · exact hZF.1.eq_of_same_members first second hSame
        · exact False.elim <|
            hFirstUnused <| hSecondEarlier first hFirstSecond
        · exact False.elim <|
            hSecondUnused <| hFirstEarlier second hSecondFirst) (by
        intro index output _ hOutput
        rw [Definitional.Project.Formula.denote_leastUnusedDiagonalValue_iff
          𝕀] at hOutput
        rcases hOutput with
          ⟨_, _, hOutputκ, _, _⟩
        exact hOutputκ) with
    ⟨diagonal, hDiagonal, hDiagonalPairs⟩
  refine ⟨diagonal, hDiagonal, ?_⟩
  intro row function hRowκ hRowFunction
  rcases hCofinal.isLimit.2.2 with
    ⟨sequenceRange, hSequenceRange, hSequenceUnion⟩
  rcases (hSequenceUnion row).mp hRowκ with
    ⟨stage, hStageRange, hRowStage⟩
  rcases (hSequenceRange stage).mp hStageRange with
    ⟨index, hIndexStage⟩
  have hIndex :
      ℳ.mem index cf :=
    hCofinal.isSetFunctionFromTo.input_mem_of_pairMember
      hIndexStage
  rcases hDiagonal.2.2 index hIndex with
    ⟨value, _, hIndexValue⟩
  have hValueData := ((hDiagonalPairs index value).mp hIndexValue).2
  rw [Definitional.Project.Formula.denote_leastUnusedDiagonalValue_iff
    𝕀] at hValueData
  rcases hValueData with
    ⟨selectedStage, hIndexSelectedStage, _,
      hValueUnused, _⟩
  have hStageEq :=
    hCofinal.isSetFunctionFromTo.1.2
      index stage selectedStage
      hIndexStage hIndexSelectedStage
  subst selectedStage
  intro hEq
  have hFunctionValue :
      ℳ.PairMember 𝕀 index value function := by
    simpa [hEq] using hIndexValue
  exact hValueUnused
    ⟨row, hRowStage, function,
      hRowFunction, hFunctionValue⟩
/--
任意以 `κ` 为定义域的内部函数族都不能满射到 `cf(κ) → κ` 的函数空间。
-/
theorem not_surjectiveOnto_functionSpace
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {cofinalSequence cf κ space enumeration : ℳ.Domain} (hκ : ℳ.IsCardinal 𝕀 κ) (hCofinal :
      ℳ.IsCofinalOrdinalSequence 𝕀
        cofinalSequence cf κ) (hSpace :
      ℳ.IsFunctionSpace 𝕀 space cf κ) (hEnumeration :
      ℳ.IsSetFunctionFromTo 𝕀 enumeration κ space) :
    ¬ ℳ.IsSetSurjectiveOnto 𝕀 enumeration κ space := by
  intro hSurjective
  rcases hCofinal.exists_diagonalFunction
      hZF 𝕀 hκ hSpace hEnumeration with
    ⟨diagonal, hDiagonal, hDifferent⟩
  have hDiagonalSpace :
      ℳ.mem diagonal space := (hSpace diagonal).mpr hDiagonal
  rcases hSurjective diagonal hDiagonalSpace with
    ⟨row, hRowκ, hRowDiagonal⟩
  exact hDifferent row diagonal hRowκ hRowDiagonal rfl
end Structure.IsCofinalOrdinalSequence
namespace Structure.IsCofinality
/--
定理 3.11：若 `cf` 是基数 `κ` 的共尾度，且 `power = κ ^ cf`，则
`κ < power`。当前 `IsCofinality` 接口已保证目标 `κ` 是极限序数，因而覆盖文献中的
无限性前提。
-/
theorem cardinalLess_exponentiation
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {κ cf power : ℳ.Domain} (hCofinality : ℳ.IsCofinality 𝕀 cf κ) (hκ : ℳ.IsCardinal 𝕀 κ) (hPower :
      ℳ.IsCardinalExponentiation 𝕀 power κ cf) :
    ℳ.CardinalLess 𝕀 κ power := by
  rcases hCofinality.hasCofinalSequence with
    ⟨cofinalSequence, hCofinalSequence⟩
  rcases hPower with
    ⟨baseSet, exponentSet, representedSpace,
      hBase, hExponent, hRepresentedSpace, hPowerCardinal⟩
  rcases ZF.exists_functionSpace hZF 𝕀 cf κ with
    ⟨space, hSpace⟩
  have hRepresentedToCanonical :=
    ZF.equinumerous_functionSpace hZF 𝕀
      hRepresentedSpace hSpace (hExponent.2.symm hZF 𝕀) (hBase.2.symm hZF 𝕀)
  have hPowerToSpace :
      ℳ.Equinumerous 𝕀 power space :=
    hPowerCardinal.2.trans hZF 𝕀
      hRepresentedToCanonical
  have hCfNonempty :
      ∃ index, ℳ.mem index cf :=
    hCofinalSequence.length_isLimitOrdinal hZF |>.2.1
  rcases ZF.exists_constantFunctionInjection
      hZF 𝕀 hSpace hCfNonempty with
    ⟨κToSpace, hκToSpace⟩
  rcases hPowerToSpace.symm hZF 𝕀 with
    ⟨spaceToPower, hSpaceToPower⟩
  rcases ZF.exists_compositionInjection hZF 𝕀
      hκToSpace hSpaceToPower.1 with
    ⟨κToPower, hκToPower⟩
  refine ⟨⟨κToPower, hκToPower⟩, ?_⟩
  intro hκPower
  have hκSpace :
      ℳ.Equinumerous 𝕀 κ space :=
    hκPower.trans hZF 𝕀 hPowerToSpace
  rcases hκSpace with
    ⟨enumeration, hEnumeration⟩
  exact hCofinalSequence.not_surjectiveOnto_functionSpace
    hZF 𝕀 hκ hSpace hEnumeration.1.1 hEnumeration.2
end Structure.IsCofinality
end SetTheory
end YesMetaZFC
