import YesMetaZFC.SetTheory.Card.Arithmetic.Exponentiation
import YesMetaZFC.SetTheory.Card.Cantor
import YesMetaZFC.SetTheory.FunctionSpaceConstruction

/-!
# 幂集与二元函数集

本层构造子集到 `{zero, one}` 值特征函数的模型内部双射，并由此形式化
`|𝒫(A)| = 2 ^ |A|` 的核心集合等势结论。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- `function` 是 `subset` 关于 `source` 的 `{zero, one}` 值特征函数。 -/
def IsCharacteristicFunctionOf {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (source two zero one subset function : ℳ.Domain) : Prop :=
  ℳ.IsSetFunctionFromTo 𝕀 function source two ∧
    ∀ input output,
      ℳ.PairMember 𝕀 input output function ↔
        ℳ.mem input source ∧
          ((ℳ.mem input subset ∧ output = one) ∨
            (¬ ℳ.mem input subset ∧ output = zero))

end Structure

namespace Definitional
namespace Project

namespace BinarySchema

/-- 固定子集后，特征函数在单个输入上的值关系。 -/
def characteristicValue : BinarySchema 3 where
  body := .disj
    (.conj
      (.mem (.bound 1) (.bound 2))
      (Formula.extensionalEq (.bound 0) (.bound 4)))
    (.conj
      (.neg <| .mem (.bound 1) (.bound 2))
      (Formula.extensionalEq (.bound 0) (.bound 3)))
  freeClosed := by
    simp [Formula.extensionalEq, Formula.FreeClosed]

/-- 把幂集成员映到其特征函数图。 -/
def characteristicFunction
    (𝒞 : OrderedPairConvention) : BinarySchema 4 where
  body := .conj
    (Formula.isFunctionFromTo 𝒞
      (.bound 0) (.bound 2) (.bound 3)) <|
    .forallE <| .forallE <|
      .iff
        (Formula.orderedPairMem 𝒞
          (.bound 1) (.bound 0) (.bound 2)) <|
        .conj (.mem (.bound 1) (.bound 4)) <|
          .disj
            (.conj
              (.mem (.bound 1) (.bound 3))
              (Formula.extensionalEq (.bound 0) (.bound 7)))
            (.conj
              (.neg <| .mem (.bound 1) (.bound 3))
              (Formula.extensionalEq (.bound 0) (.bound 6)))
  freeClosed := by
    simp [Formula.isFunctionFromTo, Formula.isFunction,
      Formula.isRelation, Formula.isDomain,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.extensionalEq,
      Formula.FreeClosed]

end BinarySchema

namespace UnarySchema

/-- 从函数图中分离取值为 `one` 的输入。 -/
def oneFiber
    (𝒞 : OrderedPairConvention) : UnarySchema 2 where
  body := Formula.orderedPairMem 𝒞
    (.bound 0) (.bound 2) (.bound 1)
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed]

end UnarySchema

namespace Formula

/-- 单点特征值关系的纸面解释。 -/
theorem denote_characteristicValue_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    (env : Env ℳ 3) (input output : ℳ.Domain) :
    BinarySchema.characteristicValue.denote env input output ↔
      (ℳ.mem input (env.bound 0) ∧ output = env.bound 2) ∨
      (¬ ℳ.mem input (env.bound 0) ∧ output = env.bound 1) := by
  simp only [BinarySchema.characteristicValue, BinarySchema.denote,
    Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push]
  rfl

/-- 整体特征函数模式的纸面解释。 -/
theorem denote_characteristicFunction_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 4) (subset function : ℳ.Domain) :
    (BinarySchema.characteristicFunction 𝒞).denote
        env subset function ↔
      ℳ.IsCharacteristicFunctionOf 𝕀
        (env.bound 0) (env.bound 1)
        (env.bound 2) (env.bound 3) subset function := by
  simp only [BinarySchema.characteristicFunction, BinarySchema.denote,
    Structure.IsCharacteristicFunctionOf,
    Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isFunctionFromTo_iff 𝕀 hExt,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    Formula.satisfies_extensionalEq_iff_eq hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push,
    Term.eval_bound_six_push, Term.eval_bound_seven_push]
  rfl

/-- `one`-纤维模式的纸面解释。 -/
theorem satisfies_oneFiber_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 2) (input : ℳ.Domain) :
    satisfies (env.push input) (UnarySchema.oneFiber 𝒞).body ↔
      ℳ.PairMember 𝕀 input (env.bound 1) (env.bound 0) := by
  simp only [UnarySchema.oneFiber,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push]
  rfl

end Formula

end Project
end Definitional

namespace ZF

/-- 幂集与相应的 `{zero, one}` 值函数集等势。 -/
theorem equinumerous_powerSet_functionSpace
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {source power two zero one space : ℳ.Domain}
    (hPower : ℳ.IsPowerSetOf power source)
    (hTwo : ∀ value, ℳ.mem value two ↔
      value = zero ∨ value = one)
    (hDistinct : zero ≠ one)
    (hSpace : ℳ.IsFunctionSpace 𝕀 space source two) :
    ℳ.Equinumerous 𝕀 power space := by
  let env : Env ℳ 4 := {
    bound := Fin.cases source <|
      Fin.cases two <|
        Fin.cases zero <|
          Fin.cases one Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setBijectionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.characteristicFunction 𝒞) env
  · intro subset hSubsetPower
    have hSubset := (hPower subset).mp hSubsetPower
    let valueEnv : Env ℳ 3 := {
      bound := Fin.cases subset <|
        Fin.cases zero <|
          Fin.cases one Fin.elim0
      free := fun _ => Classical.choice ℳ.nonempty
    }
    rcases exists_setFunctionFromTo_of_denote
        hZF 𝕀 Definitional.Project.BinarySchema.characteristicValue valueEnv
        (source := source) (target := two)
        (by
          intro input _
          classical
          by_cases hInput : ℳ.mem input subset
          · exact ⟨one,
              (Definitional.Project.Formula.denote_characteristicValue_iff
                hZF.1 valueEnv input one).mpr <|
                  Or.inl ⟨hInput, rfl⟩⟩
          · exact ⟨zero,
              (Definitional.Project.Formula.denote_characteristicValue_iff
                hZF.1 valueEnv input zero).mpr <|
                  Or.inr ⟨hInput, rfl⟩⟩)
        (by
          intro input _ first second hFirst hSecond
          rw [Definitional.Project.Formula.denote_characteristicValue_iff hZF.1]
            at hFirst hSecond
          rcases hFirst with hFirst | hFirst <;>
            rcases hSecond with hSecond | hSecond
          · exact hFirst.2.trans hSecond.2.symm
          · exact False.elim <| hSecond.1 hFirst.1
          · exact False.elim <| hFirst.1 hSecond.1
          · exact hFirst.2.trans hSecond.2.symm)
        (by
          intro input output _ hValue
          rw [Definitional.Project.Formula.denote_characteristicValue_iff hZF.1]
            at hValue
          rcases hValue with hValue | hValue
          · exact (hTwo output).mpr <| Or.inr hValue.2
          · exact (hTwo output).mpr <| Or.inl hValue.2) with
      ⟨function, hFunction, hPairs⟩
    refine ⟨function,
      (Definitional.Project.Formula.denote_characteristicFunction_iff
        𝕀 hZF.1 env subset function).mpr ?_⟩
    refine ⟨hFunction, fun input output => ?_⟩
    rw [hPairs input output,
      Definitional.Project.Formula.denote_characteristicValue_iff hZF.1]
    constructor
    · rintro ⟨hInput, hValue⟩
      exact ⟨hInput, hValue⟩
    · rintro ⟨hInput, hValue⟩
      exact ⟨hInput, hValue⟩
  · intro subset _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_characteristicFunction_iff 𝕀 hZF.1]
      at hFirst hSecond
    apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
      hFirst.1.1.1 hSecond.1.1.1
    intro input output
    rw [hFirst.2 input output, hSecond.2 input output]
  · intro subset function _ hValue
    rw [Definitional.Project.Formula.denote_characteristicFunction_iff 𝕀 hZF.1]
      at hValue
    exact (hSpace function).mpr hValue.1
  · intro first second function hFirstPower hSecondPower hFirst hSecond
    rw [Definitional.Project.Formula.denote_characteristicFunction_iff 𝕀 hZF.1]
      at hFirst hSecond
    apply hZF.1.eq_of_same_members
    intro input
    constructor
    · intro hInputFirst
      have hInputSource :=
        (hPower first).mp hFirstPower input hInputFirst
      have hPair :
          ℳ.PairMember 𝕀 input one function :=
        (hFirst.2 input one).mpr
          ⟨hInputSource, Or.inl ⟨hInputFirst, rfl⟩⟩
      rcases (hSecond.2 input one).mp hPair with
        ⟨_, hSecondValue⟩
      rcases hSecondValue with hInputSecond | hInputSecond
      · exact hInputSecond.1
      · exact False.elim <| hDistinct hInputSecond.2.symm
    · intro hInputSecond
      have hInputSource :=
        (hPower second).mp hSecondPower input hInputSecond
      have hPair :
          ℳ.PairMember 𝕀 input one function :=
        (hSecond.2 input one).mpr
          ⟨hInputSource, Or.inl ⟨hInputSecond, rfl⟩⟩
      rcases (hFirst.2 input one).mp hPair with
        ⟨_, hFirstValue⟩
      rcases hFirstValue with hInputFirst | hInputFirst
      · exact hInputFirst.1
      · exact False.elim <| hDistinct hInputFirst.2.symm
  · intro function hFunctionSpace
    have hFunction := (hSpace function).mp hFunctionSpace
    let fiberEnv : Env ℳ 2 := {
      bound := Fin.cases function <| Fin.cases one Fin.elim0
      free := fun _ => Classical.choice ℳ.nonempty
    }
    rcases exists_separation hZF
        (Definitional.Project.UnarySchema.oneFiber 𝒞) fiberEnv source with
      ⟨subset, hSubset⟩
    have hSubsetPower : ℳ.mem subset power := by
      apply (hPower subset).mpr
      intro input hInput
      exact ((hSubset input).mp hInput).1
    refine ⟨subset, hSubsetPower,
      (Definitional.Project.Formula.denote_characteristicFunction_iff
        𝕀 hZF.1 env subset function).mpr ?_⟩
    refine ⟨hFunction, fun input output => ?_⟩
    constructor
    · intro hPair
      have hInputSource :=
        hFunction.input_mem_of_pairMember hPair
      have hOutputTwo :=
        hFunction.output_mem_of_pairMember hPair
      rcases (hTwo output).mp hOutputTwo with
        hOutputZero | hOutputOne
      · refine ⟨hInputSource, Or.inr ⟨?_, hOutputZero⟩⟩
        intro hInputSubset
        have hOnePair :=
          (Definitional.Project.Formula.satisfies_oneFiber_iff
            𝕀 fiberEnv input).mp <|
            ((hSubset input).mp hInputSubset).2
        have hEq := hFunction.1.2 input output one hPair hOnePair
        exact hDistinct <| hOutputZero.symm.trans hEq
      · refine ⟨hInputSource, Or.inl ⟨?_, hOutputOne⟩⟩
        apply (hSubset input).mpr
        exact ⟨hInputSource,
          (Definitional.Project.Formula.satisfies_oneFiber_iff
            𝕀 fiberEnv input).mpr <| by simpa [hOutputOne] using hPair⟩
    · rintro ⟨hInputSource, hValue⟩
      rcases hValue with hInputSubset | hInputNotSubset
      · have hOnePair :=
          (Definitional.Project.Formula.satisfies_oneFiber_iff
            𝕀 fiberEnv input).mp <|
            ((hSubset input).mp hInputSubset.1).2
        simpa [hInputSubset.2] using hOnePair
      · rcases hFunction.2.2 input hInputSource with
          ⟨selected, hSelectedTwo, hSelectedPair⟩
        rcases (hTwo selected).mp hSelectedTwo with
          hSelectedZero | hSelectedOne
        · simpa [hInputNotSubset.2, hSelectedZero] using hSelectedPair
        · exact False.elim <| hInputNotSubset.1 <|
            (hSubset input).mpr
              ⟨hInputSource,
                (Definitional.Project.Formula.satisfies_oneFiber_iff
                  𝕀 fiberEnv input).mpr <| by
                    simpa [hSelectedOne] using hSelectedPair⟩

/-- 二元基数指数是相应幂集的基数。 -/
theorem twoExponentiation_isCardinalOf_powerSet
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {source power κ two twoSet zero one result : ℳ.Domain}
    (hPower : ℳ.IsPowerSetOf power source)
    (hκ : ℳ.IsCardinalOf 𝕀 κ source)
    (hTwoCardinal : ℳ.IsCardinalOf 𝕀 two twoSet)
    (hTwo : ∀ value, ℳ.mem value twoSet ↔
      value = zero ∨ value = one)
    (hDistinct : zero ≠ one)
    (hExponentiation :
      ℳ.IsCardinalExponentiation 𝕀 result two κ) :
    ℳ.IsCardinalOf 𝕀 result power := by
  rcases hExponentiation with
    ⟨baseSet, exponentSet, space,
      hBase, hExponent, hSpace, hResult⟩
  rcases exists_functionSpace hZF 𝕀 source twoSet with
    ⟨normalizedSpace, hNormalizedSpace⟩
  have hExponentEquinumerous :
      ℳ.Equinumerous 𝕀 exponentSet source :=
    hExponent.2.symm hZF 𝕀 |>.trans hZF 𝕀 hκ.2
  have hBaseEquinumerous :
      ℳ.Equinumerous 𝕀 baseSet twoSet :=
    hBase.2.symm hZF 𝕀 |>.trans hZF 𝕀 hTwoCardinal.2
  have hSpaceEquinumerous :=
    equinumerous_functionSpace hZF 𝕀
      hSpace hNormalizedSpace
      hExponentEquinumerous hBaseEquinumerous
  have hCharacteristic :=
    equinumerous_powerSet_functionSpace hZF 𝕀
      hPower hTwo hDistinct hNormalizedSpace
  exact ⟨hResult.1,
    hResult.2.trans hZF 𝕀 <|
      hSpaceEquinumerous.trans hZF 𝕀 <|
        hCharacteristic.symm hZF 𝕀⟩

/-- 引理 3.3：`κ < 2^κ`。 -/
theorem cardinalLess_twoExponentiation
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {source power κ two twoSet zero one result : ℳ.Domain}
    (hPower : ℳ.IsPowerSetOf power source)
    (hκ : ℳ.IsCardinalOf 𝕀 κ source)
    (hTwoCardinal : ℳ.IsCardinalOf 𝕀 two twoSet)
    (hTwo : ∀ value, ℳ.mem value twoSet ↔
      value = zero ∨ value = one)
    (hDistinct : zero ≠ one)
    (hExponentiation :
      ℳ.IsCardinalExponentiation 𝕀 result two κ) :
    ℳ.CardinalLess 𝕀 κ result := by
  have hResultPower :=
    twoExponentiation_isCardinalOf_powerSet hZF 𝕀
      hPower hκ hTwoCardinal hTwo hDistinct hExponentiation
  have hCantor := cardinalLess_powerSet hZF 𝕀 hPower
  constructor
  · rcases hκ.2 with ⟨sourceBijection, hSourceBijection⟩
    rcases hCantor.1 with ⟨cantorInjection, hCantorInjection⟩
    rcases hResultPower.2 with ⟨resultBijection, hResultBijection⟩
    rcases exists_inverseBijection hZF 𝕀 hResultBijection with
      ⟨powerToResult, hPowerToResult⟩
    rcases exists_compositionInjection hZF 𝕀
        hSourceBijection.1 hCantorInjection with
      ⟨toPower, hToPower⟩
    exact exists_compositionInjection hZF 𝕀
      hToPower hPowerToResult.1
  · intro hEquinumerous
    apply hCantor.2
    exact hκ.2.symm hZF 𝕀 |>.trans hZF 𝕀 <|
      hEquinumerous.trans hZF 𝕀 hResultPower.2

end ZF

end SetTheory
end YesMetaZFC
