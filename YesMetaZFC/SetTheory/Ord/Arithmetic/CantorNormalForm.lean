import YesMetaZFC.SetTheory.Ord.Arithmetic.Comparison
import YesMetaZFC.SetTheory.Ord.Natural

/-!
# Cantor 正规形

本文件形式化非零序数的 Cantor 正规形。证明首先在模型内选出唯一首指数区间，
随后用序数除法抽取有限非零系数与严格更小的余项，最后把归纳所得的对象层有限序列
扩展一个末项。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- Cantor 正规形在一个索引处的递推方程。 -/
def IsCantorNormalFormStep {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (ω α exponents coefficients values index : ℳ.Domain) :
    Prop :=
  ∀ exponent coefficient previous,
    ℳ.PairMember 𝕀 index exponent exponents →
    ℳ.PairMember 𝕀 index coefficient coefficients →
    ℳ.PairMember 𝕀 index previous values →
      (∃ member, ℳ.mem member coefficient) ∧
        ∃ next power monomial output,
          ℳ.SuccessorOf next index ∧
          ℳ.IsOrdinalExponentiation 𝕀
            power ω exponent ∧
          ℳ.mem previous power ∧
          (power = α ∨ ℳ.mem power α) ∧
          ℳ.IsOrdinalMultiplication 𝕀
            monomial power coefficient ∧
          ℳ.IsOrdinalAddition 𝕀
            output monomial previous ∧
          (power = output ∨ ℳ.mem power output) ∧
          ℳ.PairMember 𝕀 next output values

/--
带环境上界的对象层有限 Cantor 正规形。

指数按从低到高的顺序存储，使归纳构造可以在末尾追加新的首项；`values` 在索引
`0` 处取 `0`，并在每个后继位置保存加入当前单项式后的部分值。
-/
def IsCantorNormalFormBelow {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (ω bound α length exponents coefficients values : ℳ.Domain) :
    Prop :=
  ℳ.mem length ω ∧
    ℳ.IsIncreasingOrdinalSequence 𝕀 exponents length ∧
    ℳ.IsSequenceIn 𝕀 coefficients length ω ∧
    ∃ valueLength,
      ℳ.SuccessorOf valueLength length ∧
      ℳ.IsOrdinalValuedSequence 𝕀 values valueLength ∧
      (∃ zero,
        (∀ member, ¬ ℳ.mem member zero) ∧
        ℳ.PairMember 𝕀 zero zero values) ∧
      ℳ.PairMember 𝕀 length α values ∧
      ∀ index, ℳ.mem index length →
        ℳ.IsCantorNormalFormStep 𝕀
          ω bound exponents coefficients values index

/-- 环境上界取表示值本身时，得到普通对象层有限 Cantor 正规形。 -/
def IsCantorNormalForm {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (ω α length exponents coefficients values : ℳ.Domain) :
    Prop :=
  ℳ.IsCantorNormalFormBelow 𝕀
    ω α α length exponents coefficients values

/-- 序列追加后，旧定义域中的坐标仍只能来自旧序列。 -/
theorem pairMember_old_of_append {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence appended length appendedValue index value : ℳ.Domain}
    (hLength : ℳ.IsOrdinal length)
    (hIndex : ℳ.mem index length)
    (hPairs : ∀ input output,
      ℳ.PairMember 𝕀 input output appended ↔
        ℳ.PairMember 𝕀 input output sequence ∨
          (input = length ∧ output = appendedValue))
    (hValue :
      ℳ.PairMember 𝕀 index value appended) :
    ℳ.PairMember 𝕀 index value sequence := by
  prove_auto

/-- 序列追加后，新末索引上的坐标值等于追加值。 -/
theorem pairMember_new_eq_of_append {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence appended length appendedValue value : ℳ.Domain}
    (hSequence :
      ℳ.IsSequenceOfLength 𝕀 sequence length)
    (hPairs : ∀ input output,
      ℳ.PairMember 𝕀 input output appended ↔
        ℳ.PairMember 𝕀 input output sequence ∨
          (input = length ∧ output = appendedValue))
    (hValue :
      ℳ.PairMember 𝕀 length value appended) :
    value = appendedValue := by
  prove_auto

end Structure

namespace Definitional
namespace Project
namespace Formula

/-- Cantor 正规形在给定索引处的对象语言递推方程。 -/
def isCantorNormalFormStep (𝒞 : OrderedPairConvention)
    {depth : Nat}
    (ω α exponents coefficients values index : Term depth) :
    Formula 1 depth :=
  .forallE <| .forallE <| .forallE <| .imp
    (.conj
      (orderedPairMem 𝒞 index.weaken.weaken.weaken
        (.bound 2) exponents.weaken.weaken.weaken) <|
      .conj
        (orderedPairMem 𝒞 index.weaken.weaken.weaken
          (.bound 1) coefficients.weaken.weaken.weaken)
        (orderedPairMem 𝒞 index.weaken.weaken.weaken
          Term.newest values.weaken.weaken.weaken)) <|
    .conj (.neg <| isEmpty (.bound 1)) <|
      .existsE <| .conj
        (isSuccessor Term.newest index.weaken.weaken.weaken.weaken) <|
        .existsE <| .conj
          (isOrdinalExponentiation 𝒞 Term.newest
            ω.weaken.weaken.weaken.weaken.weaken (.bound 4)) <|
          .conj
            (.mem (.bound 2) Term.newest) <|
          .conj
            (.disj
              (extensionalEq Term.newest
                α.weaken.weaken.weaken.weaken.weaken)
              (.mem Term.newest
                α.weaken.weaken.weaken.weaken.weaken)) <|
            .existsE <| .conj
              (isOrdinalMultiplication 𝒞 Term.newest
                (.bound 1) (.bound 4)) <|
              .existsE <| .conj
              (isOrdinalAddition 𝒞 Term.newest
                  (.bound 1) (.bound 4))
                (.conj
                  (.disj
                    (extensionalEq (.bound 2) Term.newest)
                    (.mem (.bound 2) Term.newest))
                  (orderedPairMem 𝒞 (.bound 3) Term.newest
                    values.weaken.weaken.weaken.weaken.weaken.weaken.weaken))

/-- 带环境上界的对象层有限 Cantor 正规形。 -/
def isCantorNormalFormBelow (𝒞 : OrderedPairConvention)
    {depth : Nat}
    (ω bound α length exponents coefficients values : Term depth) :
    Formula 1 depth :=
  .conj (.mem length ω) <|
    .conj
      (isIncreasingOrdinalSequence 𝒞 exponents length) <|
    .conj
      (isSequenceIn 𝒞 coefficients length ω) <|
    .existsE <| .conj
      (isSuccessor Term.newest length.weaken) <|
    .conj
      (isOrdinalValuedSequence 𝒞 values.weaken Term.newest) <|
    .conj
      (.existsE <| .conj (isEmpty Term.newest)
        (orderedPairMem 𝒞 Term.newest Term.newest
          values.weaken.weaken)) <|
    .conj
      (orderedPairMem 𝒞 length.weaken α.weaken
        values.weaken) <|
      forallMem length.weaken <|
        isCantorNormalFormStep 𝒞
          ω.weaken.weaken bound.weaken.weaken
          exponents.weaken.weaken coefficients.weaken.weaken
          values.weaken.weaken Term.newest

/-- 环境上界取表示值本身时，得到普通对象层有限 Cantor 正规形。 -/
def isCantorNormalForm (𝒞 : OrderedPairConvention)
    {depth : Nat}
    (ω α length exponents coefficients values : Term depth) :
    Formula 1 depth :=
  isCantorNormalFormBelow 𝒞
    ω α α length exponents coefficients values

/-- 单个正规形递推步骤的公式语义。 -/
@[prove_auto_norm semantic]
theorem satisfies_isCantorNormalFormStep_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (ω α exponents coefficients values index : Term depth) :
    satisfies env
        (isCantorNormalFormStep 𝒞
          ω α exponents coefficients values index) ↔
      ℳ.IsCantorNormalFormStep 𝕀
        (ω.eval env) (α.eval env)
        (exponents.eval env) (coefficients.eval env)
        (values.eval env) (index.eval env) := by
  simp only [isCantorNormalFormStep,
    Structure.IsCantorNormalFormStep,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_conj_iff, satisfies_neg_iff,
    satisfies_exists_iff, satisfies_mem_iff,
    satisfies_disj_iff,
    satisfies_orderedPairMem_iff 𝕀,
    satisfies_isEmpty_iff,
    satisfies_isSuccessor_iff,
    satisfies_isOrdinalExponentiation_iff 𝕀 hExt,
    satisfies_extensionalEq_iff_eq hExt,
    satisfies_isOrdinalMultiplication_iff 𝕀 hExt,
    satisfies_isOrdinalAddition_iff 𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    and_imp]
  constructor
  · intro hStep exponent coefficient previous
      hExponent hCoefficient hPrevious
    rcases hStep exponent coefficient previous
        hExponent hCoefficient hPrevious with
      ⟨hCoefficientNonempty,
        next, hNext, power, hPower, hPreviousPower,
        hPowerLe, monomial, hMonomial,
        output, hOutput, hPowerOutput, hPair⟩
    have hCoefficientNonempty' :
        ∃ member, ℳ.mem member coefficient := by
      apply Classical.byContradiction
      intro hNoMember
      apply hCoefficientNonempty
      intro member hMember
      exact hNoMember ⟨member, hMember⟩
    exact
      ⟨hCoefficientNonempty',
        next, power, monomial, output,
        hNext, hPower, hPreviousPower, hPowerLe,
        hMonomial, hOutput, hPowerOutput, hPair⟩
  · intro hStep exponent coefficient previous
      hExponent hCoefficient hPrevious
    rcases hStep exponent coefficient previous
        hExponent hCoefficient hPrevious with
      ⟨hCoefficientNonempty,
        next, power, monomial, output,
        hNext, hPower, hPreviousPower, hPowerLe,
        hMonomial, hOutput, hPowerOutput, hPair⟩
    refine
      ⟨?_, next, hNext, power, hPower, hPreviousPower,
        hPowerLe, monomial, hMonomial,
        output, hOutput, hPowerOutput, hPair⟩
    intro hEmpty
    rcases hCoefficientNonempty with ⟨member, hMember⟩
    exact hEmpty member hMember

/-- 带环境上界的有限 Cantor 正规形公式与纸面结构一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isCantorNormalFormBelow_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (ω bound α length exponents coefficients values : Term depth) :
    satisfies env
        (isCantorNormalFormBelow 𝒞
          ω bound α length exponents coefficients values) ↔
      ℳ.IsCantorNormalFormBelow 𝕀
        (ω.eval env) (bound.eval env)
        (α.eval env) (length.eval env)
        (exponents.eval env) (coefficients.eval env)
        (values.eval env) := by
  simp only [isCantorNormalFormBelow,
    Structure.IsCantorNormalFormBelow,
    satisfies_conj_iff, satisfies_mem_iff,
    satisfies_exists_iff,
    satisfies_isIncreasingOrdinalSequence_iff 𝕀 hExt,
    satisfies_isSequenceIn_iff 𝕀 hExt,
    satisfies_isSuccessor_iff,
    satisfies_isOrdinalValuedSequence_iff 𝕀 hExt,
    satisfies_isEmpty_iff,
    satisfies_orderedPairMem_iff 𝕀,
    satisfies_forallMem_iff,
    satisfies_isCantorNormalFormStep_iff 𝕀 hExt,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 普通有限 Cantor 正规形公式与纸面结构一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isCantorNormalForm_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (ω α length exponents coefficients values : Term depth) :
    satisfies env
        (isCantorNormalForm 𝒞
          ω α length exponents coefficients values) ↔
      ℳ.IsCantorNormalForm 𝕀
        (ω.eval env) (α.eval env) (length.eval env)
        (exponents.eval env) (coefficients.eval env)
        (values.eval env) := by
  simp [isCantorNormalForm, Structure.IsCantorNormalForm,
    satisfies_isCantorNormalFormBelow_iff 𝕀 hExt]

end Formula

namespace UnarySchema

/-- 当前序数存在以固定 `ω` 为底的有限 Cantor 正规形。 -/
private def cantorNormalFormExistence
    (𝒞 : OrderedPairConvention) : UnarySchema 1 where
  body := .existsE <| .existsE <| .existsE <| .existsE <|
    Formula.isCantorNormalForm 𝒞
      (.bound 5) (.bound 4) (.bound 3)
      (.bound 2) (.bound 1) Term.newest
  freeClosed := by
    simp [Formula.isCantorNormalForm,
      Formula.isCantorNormalFormBelow,
      Formula.isCantorNormalFormStep,
      Formula.isIncreasingOrdinalSequence,
      Formula.isOrdinalValuedSequence,
      Formula.isSequenceOfLength, Formula.isSequenceIn,
      Formula.isOrdinal, Formula.isTransitive,
      Formula.isWellOrderOn, Formula.isLinearOrderOn,
      Formula.isStrictPartialOrderOn,
      Formula.isIrreflexiveOn, Formula.isTransitiveOn,
      Formula.isLeastOf, Formula.lessOrEqual,
      Formula.isFunctionFromTo, Formula.isFunction,
      Formula.isRelation, Formula.isDomain,
      Formula.orderedPairMem, Formula.isEmpty,
      Formula.isSuccessor, Formula.isOrdinalExponentiation,
      Formula.isOrdinalMultiplication,
      Formula.isOrdinalAddition, Formula.related,
      Formula.forallMem, Formula.existsMem,
      Formula.subset, Formula.extensionalEq,
      Formula.FreeClosed,
      Term.newest, Term.weaken]
    all_goals repeat' constructor
    all_goals
      apply Formula.related_freeClosed_of_closed <;>
        simp [TermVector.FreeClosed, TermVector.singleton]

/-- 当前指数的 `ω` 幂严格越过固定序数。 -/
private def ordinalExponentiationStrictUpperBound
    (𝒞 : OrderedPairConvention) : UnarySchema 2 where
  body := .existsE <| .conj
    (Formula.isOrdinalExponentiation 𝒞
      Term.newest (.bound 2) (.bound 1))
    (.mem (.bound 3) Term.newest)
  freeClosed := by
    simp [Formula.isOrdinalExponentiation, Formula.related,
      Formula.FreeClosed, Term.newest]
    apply Formula.related_freeClosed_of_closed <;>
      simp [TermVector.FreeClosed, TermVector.singleton]

/-- 当前序数的任意两套同上界 Cantor 正规形完全相等。 -/
private def cantorNormalFormBelowUniqueness
    (𝒞 : OrderedPairConvention) : UnarySchema 1 where
  body := .forallE <| .forallE <| .forallE <| .forallE <|
    .forallE <| .forallE <| .forallE <| .forallE <|
    .forallE <| .imp
      (.conj
        (Formula.isCantorNormalFormBelow 𝒞
          (.bound 10) (.bound 8) (.bound 9) (.bound 7)
          (.bound 6) (.bound 5) (.bound 4))
        (Formula.isCantorNormalFormBelow 𝒞
          (.bound 10) (.bound 8) (.bound 9) (.bound 3)
          (.bound 2) (.bound 1) Term.newest)) <|
      .conj
        (Formula.extensionalEq (.bound 7) (.bound 3)) <|
      .conj
        (Formula.extensionalEq (.bound 6) (.bound 2)) <|
      .conj
        (Formula.extensionalEq (.bound 5) (.bound 1))
        (Formula.extensionalEq (.bound 4) Term.newest)
  freeClosed := by
    simp [Formula.isCantorNormalFormBelow,
      Formula.isCantorNormalFormStep,
      Formula.isIncreasingOrdinalSequence,
      Formula.isOrdinalValuedSequence,
      Formula.isSequenceOfLength, Formula.isSequenceIn,
      Formula.isOrdinal, Formula.isTransitive,
      Formula.isWellOrderOn, Formula.isLinearOrderOn,
      Formula.isStrictPartialOrderOn,
      Formula.isIrreflexiveOn, Formula.isTransitiveOn,
      Formula.isLeastOf, Formula.lessOrEqual,
      Formula.isFunctionFromTo, Formula.isFunction,
      Formula.isRelation, Formula.isDomain,
      Formula.orderedPairMem, Formula.isEmpty,
      Formula.isSuccessor, Formula.isOrdinalExponentiation,
      Formula.isOrdinalMultiplication,
      Formula.isOrdinalAddition, Formula.related,
      Formula.forallMem, Formula.existsMem,
      Formula.subset, Formula.extensionalEq,
      Formula.FreeClosed,
      Term.newest, Term.weaken]
    all_goals repeat' constructor
    all_goals
      apply Formula.related_freeClosed_of_closed <;>
        simp [TermVector.FreeClosed, TermVector.singleton]

end UnarySchema

namespace Formula

private theorem satisfies_cantorNormalFormExistence_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 1)
    (α : ℳ.Domain) :
    satisfies (env.push α)
        (UnarySchema.cantorNormalFormExistence 𝒞).body ↔
      ∃ length exponents coefficients values,
        ℳ.IsCantorNormalForm 𝕀
          (env.bound 0) α length
          exponents coefficients values := by
  simp [UnarySchema.cantorNormalFormExistence,
    satisfies_exists_iff,
    satisfies_isCantorNormalForm_iff 𝕀 hExt,
    Term.eval_newest]
  rfl

private theorem satisfies_ordinalExponentiationStrictUpperBound_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 2)
    (candidate : ℳ.Domain) :
    satisfies (env.push candidate)
        (UnarySchema.ordinalExponentiationStrictUpperBound
          𝒞).body ↔
      ∃ power,
        ℳ.IsOrdinalExponentiation 𝕀
            power (env.bound 0) candidate ∧
          ℳ.mem (env.bound 1) power := by
  simp [UnarySchema.ordinalExponentiationStrictUpperBound,
    satisfies_exists_iff, satisfies_conj_iff, satisfies_mem_iff,
    satisfies_isOrdinalExponentiation_iff 𝕀 hExt,
    Term.eval_newest]
  rfl

private theorem satisfies_cantorNormalFormBelowUniqueness_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 1)
    (α : ℳ.Domain) :
    satisfies (env.push α)
        (UnarySchema.cantorNormalFormBelowUniqueness
          𝒞).body ↔
      ∀ bound
          firstLength firstExponents firstCoefficients firstValues
          secondLength secondExponents secondCoefficients secondValues,
        (ℳ.IsCantorNormalFormBelow 𝕀
            (env.bound 0) bound α firstLength
            firstExponents firstCoefficients firstValues ∧
          ℳ.IsCantorNormalFormBelow 𝕀
            (env.bound 0) bound α secondLength
            secondExponents secondCoefficients secondValues) →
          firstLength = secondLength ∧
            firstExponents = secondExponents ∧
            firstCoefficients = secondCoefficients ∧
            firstValues = secondValues := by
  simp [UnarySchema.cantorNormalFormBelowUniqueness,
    satisfies_forall_iff, satisfies_imp_iff, satisfies_conj_iff,
    satisfies_isCantorNormalFormBelow_iff 𝕀 hExt,
    satisfies_extensionalEq_iff_eq hExt,
    Term.eval, Env.push, and_imp]
  rfl

end Formula

end Project
end Definitional

namespace ZF

/-- 零序数具有空项列的内部 Cantor 正规形。 -/
theorem exists_cantorNormalForm_of_empty
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω zero : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hZero : ∀ value, ¬ ℳ.mem value zero) :
    ∃ length exponents coefficients values,
      ℳ.IsCantorNormalForm 𝕀
        ω zero length exponents coefficients values := by
  have hZeroOrdinal := Structure.IsOrdinal.of_no_members hZero
  rcases hω.1.1 with
    ⟨omegaZero, hωZero, hωZeroMem⟩
  have hZeroEq : zero = omegaZero := by
    apply hZF.1.eq_of_same_members
    intro value
    exact iff_of_false (hZero value) (hωZero value)
  have hZeroOmega : ℳ.mem zero ω := by
    simpa [hZeroEq] using hωZeroMem
  have hZeroSequence :=
    Structure.IsSequenceOfLength.empty 𝕀 hZero
  have hIncreasing :
      ℳ.IsIncreasingOrdinalSequence 𝕀 zero zero := by
    refine ⟨⟨hZeroSequence, ?_⟩, ?_⟩
    · intro index hIndex
      exact False.elim (hZero index hIndex)
    · intro left hLeft
      exact False.elim (hZero left hLeft)
  have hCoefficients :
      ℳ.IsSequenceIn 𝕀 zero zero ω := by
    refine ⟨hZeroOrdinal, hZeroSequence.2.1, hZeroSequence.2.2, ?_⟩
    intro input hInput
    exact False.elim (hZero input hInput)
  rcases hω.1.2 zero hZeroOmega with
    ⟨one, hOneSuccessor, hOneOmega⟩
  have hOneOrdinal :=
    KP.successor_isOrdinal (ZF.modelsKP hZF)
      hZeroOrdinal hOneSuccessor
  rcases Structure.IsSequenceOfLength.exists_append
      (ZF.modelsKP hZF) 𝕀
      hZeroSequence hOneOrdinal hOneSuccessor with
    ⟨values, hValuesLength, hValuesPairs⟩
  have hValuesOrdinal :
      ℳ.IsOrdinalValuedSequence 𝕀 values one := by
    refine ⟨hValuesLength, ?_⟩
    intro index hIndex value hValue
    rcases (hValuesPairs index value).mp hValue with
      hOld | ⟨_, hValueZero⟩
    · have hIndexZero :=
        (hZeroSequence.2.2 index).mpr ⟨value, hOld⟩
      exact False.elim (hZero index hIndexZero)
    · subst value
      exact hZeroOrdinal
  have hZeroValue :
      ℳ.PairMember 𝕀 zero zero values :=
    (hValuesPairs zero zero).mpr (Or.inr ⟨rfl, rfl⟩)
  exact
    ⟨zero, zero, zero, values,
      hZeroOmega,
      hIncreasing, hCoefficients,
      one, hOneSuccessor, hValuesOrdinal,
      ⟨zero, hZero, hZeroValue⟩,
      hZeroValue,
      fun index hIndex => False.elim (hZero index hIndex)⟩

/--
每个非零序数恰好落在相邻两个 `ω` 幂之间。

这里先构造一个首指数；其唯一性将在正规形唯一性证明中由幂值严格单调性直接推出。
-/
theorem ordinalExponentiation_exists_leadingExponent
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω α : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hα : ℳ.IsOrdinal α)
    (hαNonempty : ∃ value, ℳ.mem value α) :
    ∃ exponent successor power successorPower,
      ℳ.IsOrdinal exponent ∧
        ℳ.SuccessorOf successor exponent ∧
        ℳ.IsOrdinalExponentiation 𝕀
          power ω exponent ∧
        ℳ.IsOrdinalExponentiation 𝕀
          successorPower ω successor ∧
        (power = α ∨ ℳ.mem power α) ∧
        ℳ.mem α successorPower := by
  have hωOrdinal := hω.isOrdinal hZF
  rcases hω.exists_ordinalOne_mem with
    ⟨one, hOne, hOneOmega⟩
  rcases KP.exists_successor (ZF.modelsKP hZF) α with
    ⟨ordinalSuccessor, hαSuccessor⟩
  have hαSuccessorOrdinal :=
    KP.successor_isOrdinal (ZF.modelsKP hZF)
      hα hαSuccessor
  rcases KP.exists_successor (ZF.modelsKP hZF)
      ordinalSuccessor with
    ⟨candidateBound, hCandidateBound⟩
  have hCandidateBoundOrdinal :=
    KP.successor_isOrdinal (ZF.modelsKP hZF)
      hαSuccessorOrdinal hCandidateBound
  rcases ordinalExponentiation_existsUnique hZF
      𝕀 hωOrdinal hαSuccessorOrdinal with
    ⟨upperPower, hUpperPower, _⟩
  have hαSuccessorPower :=
    ordinalExponentiation_exponent_eq_or_mem
      hZF 𝕀 hωOrdinal hOne hOneOmega
      hαSuccessorOrdinal hUpperPower
  have hαOrdinalSuccessor :
      ℳ.mem α ordinalSuccessor :=
    (hαSuccessor α).mpr
      (Or.inr fun _ => Iff.rfl)
  have hαUpperPower : ℳ.mem α upperPower := by
    rcases hαSuccessorPower with hEqual | hMember
    · simpa [hEqual] using hαOrdinalSuccessor
    · exact
        (ordinalExponentiation_isOrdinal hZF 𝕀
          hωOrdinal hαSuccessorOrdinal hUpperPower).transitive
          ordinalSuccessor hMember α hαOrdinalSuccessor
  let env : Env ℳ 2 := {
    bound := fun
      | 0 => ω
      | 1 => α
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_separation hZF
      (Definitional.Project.UnarySchema.ordinalExponentiationStrictUpperBound 𝒞)
      env candidateBound with
    ⟨candidates, hCandidates⟩
  have hCandidatesSemantic :
      ∀ candidate,
        ℳ.mem candidate candidates ↔
          ℳ.mem candidate candidateBound ∧
            ∃ power,
              ℳ.IsOrdinalExponentiation 𝕀
                  power ω candidate ∧
                ℳ.mem α power := by
    intro candidate
    rw [hCandidates candidate]
    constructor
    · rintro ⟨hCandidateBound, hCandidate⟩
      exact ⟨hCandidateBound,
        (Definitional.Project.Formula.satisfies_ordinalExponentiationStrictUpperBound_iff
          𝕀 hZF.1 env candidate).mp hCandidate⟩
    · rintro ⟨hCandidateBound, hCandidate⟩
      exact ⟨hCandidateBound,
        (Definitional.Project.Formula.satisfies_ordinalExponentiationStrictUpperBound_iff
          𝕀 hZF.1 env candidate).mpr hCandidate⟩
  have hCandidatesSubset :
      ℳ.MemberSubset candidates candidateBound := by
    intro candidate hCandidate
    exact (hCandidatesSemantic candidate).mp hCandidate |>.1
  have hCandidatesNonempty :
      ∃ candidate, ℳ.mem candidate candidates := by
    have hαSuccessorBound :
        ℳ.mem ordinalSuccessor candidateBound :=
      (hCandidateBound ordinalSuccessor).mpr
        (Or.inr fun _ => Iff.rfl)
    exact
      ⟨ordinalSuccessor,
        (hCandidatesSemantic ordinalSuccessor).mpr
          ⟨hαSuccessorBound,
            upperPower, hUpperPower, hαUpperPower⟩⟩
  rcases hCandidateBoundOrdinal.wellOrder.least
      candidates hCandidatesSubset hCandidatesNonempty with
    ⟨least, hLeastCandidate, hLeast⟩
  have hLeastData := (hCandidatesSemantic least).mp hLeastCandidate
  rcases hLeastData.2 with
    ⟨leastPower, hLeastPower, hαLeastPower⟩
  have hLeastOrdinal :=
    hCandidateBoundOrdinal.mem hLeastData.1
  rcases hLeastOrdinal.classify hZF.1 with
    hLeastEmpty | hLeastSuccessor | hLeastLimit
  · have hLeastPowerOne :=
      (ordinalExponentiation_zero_iff
        hZF 𝕀 hωOrdinal hLeastEmpty).mp
        hLeastPower
    rcases hLeastPowerOne with
      ⟨zero, hZero, hLeastPowerSuccessor⟩
    rcases (hLeastPowerSuccessor α).mp
        hαLeastPower with hαZero | hαSame
    · exact False.elim (hZero α hαZero)
    · have hαEq :=
        hZF.1.eq_of_same_members α zero hαSame
      subst α
      rcases hαNonempty with ⟨value, hValue⟩
      exact False.elim (hZero value hValue)
  · rcases hLeastSuccessor with
      ⟨exponent, hExponentOrdinal, hLeastSuccessor⟩
    have hExponentLeast : ℳ.mem exponent least :=
      (hLeastSuccessor exponent).mpr
        (Or.inr fun _ => Iff.rfl)
    rcases ordinalExponentiation_existsUnique hZF
        𝕀 hωOrdinal hExponentOrdinal with
      ⟨power, hPower, _⟩
    have hNotOrdinalPower : ¬ ℳ.mem α power := by
      intro hαPower
      have hExponentBound :
          ℳ.mem exponent candidateBound :=
        hCandidateBoundOrdinal.transitive
          least hLeastData.1 exponent hExponentLeast
      have hExponentCandidate : ℳ.mem exponent candidates :=
        (hCandidatesSemantic exponent).mpr
          ⟨hExponentBound, power, hPower, hαPower⟩
      rcases hLeast exponent hExponentCandidate with
        hLeastSame | hLeastExponent
      · have hLeastEq :=
          hZF.1.eq_of_same_members least exponent hLeastSame
        subst least
        exact hExponentOrdinal.wellOrder.linear.irrefl
          exponent hExponentLeast hExponentLeast
      · have hSelf :=
          hLeastOrdinal.transitive exponent hExponentLeast
            least hLeastExponent
        exact hLeastOrdinal.wellOrder.linear.irrefl
          least hSelf hSelf
    have hPowerOrdinal :=
      ordinalExponentiation_isOrdinal hZF 𝕀
        hωOrdinal hExponentOrdinal hPower
    have hPowerLeOrdinal :
        power = α ∨ ℳ.mem power α := by
      rcases Structure.IsOrdinal.trichotomy hZF.1
          hPowerOrdinal hα
          (KP.exists_difference (ZF.modelsKP hZF))
          (KP.exists_intersection (ZF.modelsKP hZF)
            power α) with
        hSame | hPowerOrdinalOrder | hαPower
      · exact Or.inl <|
          hZF.1.eq_of_same_members power α hSame
      · exact Or.inr hPowerOrdinalOrder
      · exact False.elim (hNotOrdinalPower hαPower)
    exact
      ⟨exponent, least, power, leastPower,
        hExponentOrdinal, hLeastSuccessor,
        hPower, hLeastPower, hPowerLeOrdinal,
        hαLeastPower⟩
  · rcases (ordinalExponentiation_limit_iff
        hZF 𝕀 hωOrdinal hLeastLimit).mp
        hLeastPower with
      ⟨range, hRange, hUnion⟩
    rcases (hUnion α).mp hαLeastPower with
      ⟨earlierPower, hEarlierPowerRange, hαEarlierPower⟩
    rcases (hRange earlierPower).mp hEarlierPowerRange with
      ⟨earlier, hEarlierLeast, hEarlierPower⟩
    have hEarlierBound :
        ℳ.mem earlier candidateBound :=
      hCandidateBoundOrdinal.transitive
        least hLeastData.1 earlier hEarlierLeast
    have hEarlierCandidate : ℳ.mem earlier candidates :=
      (hCandidatesSemantic earlier).mpr
        ⟨hEarlierBound, earlierPower, hEarlierPower,
          hαEarlierPower⟩
    rcases hLeast earlier hEarlierCandidate with
      hLeastSame | hLeastEarlier
    · have hLeastEq :=
        hZF.1.eq_of_same_members least earlier hLeastSame
      subst least
      exact False.elim <|
        (hLeastLimit.1.mem hEarlierLeast).wellOrder.linear.irrefl
          earlier hEarlierLeast hEarlierLeast
    · have hSelf :=
        hLeastOrdinal.transitive earlier hEarlierLeast
          least hLeastEarlier
      exact False.elim <|
        hLeastOrdinal.wellOrder.linear.irrefl least hSelf hSelf

/-- 同一非零序数的相邻 `ω` 幂区间具有唯一指数。 -/
theorem ordinalExponentiation_leadingExponent_unique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω α
      firstExponent firstSuccessor firstPower firstSuccessorPower
      secondExponent secondSuccessor secondPower
      secondSuccessorPower : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hFirstExponent : ℳ.IsOrdinal firstExponent)
    (hFirstSuccessor :
      ℳ.SuccessorOf firstSuccessor firstExponent)
    (hFirstPower :
      ℳ.IsOrdinalExponentiation 𝕀
        firstPower ω firstExponent)
    (hFirstSuccessorPower :
      ℳ.IsOrdinalExponentiation 𝕀
        firstSuccessorPower ω firstSuccessor)
    (hFirstPowerLe :
      firstPower = α ∨ ℳ.mem firstPower α)
    (hαFirstSuccessorPower :
      ℳ.mem α firstSuccessorPower)
    (hSecondExponent : ℳ.IsOrdinal secondExponent)
    (hSecondSuccessor :
      ℳ.SuccessorOf secondSuccessor secondExponent)
    (hSecondPower :
      ℳ.IsOrdinalExponentiation 𝕀
        secondPower ω secondExponent)
    (hSecondSuccessorPower :
      ℳ.IsOrdinalExponentiation 𝕀
        secondSuccessorPower ω secondSuccessor)
    (hSecondPowerLe :
      secondPower = α ∨ ℳ.mem secondPower α)
    (hαSecondSuccessorPower :
      ℳ.mem α secondSuccessorPower) :
    firstExponent = secondExponent := by
  have hωOrdinal := hω.isOrdinal hZF
  rcases hω.exists_ordinalOne_mem with
    ⟨one, hOne, hOneOmega⟩
  have hFirstSuccessorOrdinal :=
    KP.successor_isOrdinal (ZF.modelsKP hZF)
      hFirstExponent hFirstSuccessor
  have hSecondSuccessorOrdinal :=
    KP.successor_isOrdinal (ZF.modelsKP hZF)
      hSecondExponent hSecondSuccessor
  have hFirstSuccessorPowerOrdinal :=
    ordinalExponentiation_isOrdinal hZF 𝕀
      hωOrdinal hFirstSuccessorOrdinal hFirstSuccessorPower
  have hSecondSuccessorPowerOrdinal :=
    ordinalExponentiation_isOrdinal hZF 𝕀
      hωOrdinal hSecondSuccessorOrdinal hSecondSuccessorPower
  have hα :=
    hFirstSuccessorPowerOrdinal.mem
      hαFirstSuccessorPower
  have hContradictionOfFirstSecond
      (hFirstSecond : ℳ.mem firstExponent secondExponent) :
      False := by
    have hFirstSuccessorLeSecond :
        firstSuccessor = secondExponent ∨
          ℳ.mem firstSuccessor secondExponent := by
      rcases Structure.IsOrdinal.trichotomy hZF.1
          hFirstSuccessorOrdinal hSecondExponent
          (KP.exists_difference (ZF.modelsKP hZF))
          (KP.exists_intersection (ZF.modelsKP hZF)
            firstSuccessor secondExponent) with
        hSame | hFirstSuccessorSecond | hSecondFirstSuccessor
      · exact Or.inl <|
          hZF.1.eq_of_same_members
            firstSuccessor secondExponent hSame
      · exact Or.inr hFirstSuccessorSecond
      · rcases (hFirstSuccessor secondExponent).mp
            hSecondFirstSuccessor with
          hSecondFirst | hSecondFirst
        · have hSelf :=
            hFirstExponent.transitive
              secondExponent hSecondFirst
              firstExponent hFirstSecond
          exact False.elim <|
            hFirstExponent.wellOrder.linear.irrefl
              firstExponent hSelf hSelf
        · have hSecondEq :=
            hZF.1.eq_of_same_members
              secondExponent firstExponent hSecondFirst
          subst secondExponent
          exact False.elim <|
            hFirstExponent.wellOrder.linear.irrefl
              firstExponent hFirstSecond hFirstSecond
    have hFirstSuccessorPowerLeSecondPower :
        firstSuccessorPower = secondPower ∨
          ℳ.mem firstSuccessorPower secondPower := by
      rcases hFirstSuccessorLeSecond with hEqual | hMember
      · subst secondExponent
        rcases ordinalExponentiation_existsUnique hZF
            𝕀 hωOrdinal hFirstSuccessorOrdinal with
          ⟨_, _, hUnique⟩
        exact Or.inl <|
          (hUnique firstSuccessorPower
              hFirstSuccessorPower).trans
            (hUnique secondPower hSecondPower).symm
      · exact Or.inr <|
          ordinalExponentiation_isIncreasingOnOrdinals
            hZF 𝕀 hωOrdinal
            hOne hOneOmega
            firstSuccessor secondExponent
            hFirstSuccessorOrdinal hSecondExponent hMember
            firstSuccessorPower secondPower
            hFirstSuccessorPower hSecondPower
    have hFirstSuccessorPowerLeOrdinal :=
      eqOrMem_trans
        hα
        hFirstSuccessorPowerLeSecondPower hSecondPowerLe
    rcases hFirstSuccessorPowerLeOrdinal with hEqual | hMember
    · subst α
      exact hFirstSuccessorPowerOrdinal.wellOrder.linear.irrefl
        firstSuccessorPower hαFirstSuccessorPower
        hαFirstSuccessorPower
    · have hSelf :=
        hFirstSuccessorPowerOrdinal.transitive
          α hαFirstSuccessorPower
          firstSuccessorPower hMember
      exact hFirstSuccessorPowerOrdinal.wellOrder.linear.irrefl
        firstSuccessorPower hSelf hSelf
  have hContradictionOfSecondFirst
      (hSecondFirst : ℳ.mem secondExponent firstExponent) :
      False := by
    have hSecondSuccessorLeFirst :
        secondSuccessor = firstExponent ∨
          ℳ.mem secondSuccessor firstExponent := by
      rcases Structure.IsOrdinal.trichotomy hZF.1
          hSecondSuccessorOrdinal hFirstExponent
          (KP.exists_difference (ZF.modelsKP hZF))
          (KP.exists_intersection (ZF.modelsKP hZF)
            secondSuccessor firstExponent) with
        hSame | hSecondSuccessorFirst | hFirstSecondSuccessor
      · exact Or.inl <|
          hZF.1.eq_of_same_members
            secondSuccessor firstExponent hSame
      · exact Or.inr hSecondSuccessorFirst
      · rcases (hSecondSuccessor firstExponent).mp
            hFirstSecondSuccessor with
          hFirstSecond | hFirstSecond
        · have hSelf :=
            hSecondExponent.transitive
              firstExponent hFirstSecond
              secondExponent hSecondFirst
          exact False.elim <|
            hSecondExponent.wellOrder.linear.irrefl
              secondExponent hSelf hSelf
        · have hFirstEq :=
            hZF.1.eq_of_same_members
              firstExponent secondExponent hFirstSecond
          subst firstExponent
          exact False.elim <|
            hSecondExponent.wellOrder.linear.irrefl
              secondExponent hSecondFirst hSecondFirst
    have hSecondSuccessorPowerLeFirstPower :
        secondSuccessorPower = firstPower ∨
          ℳ.mem secondSuccessorPower firstPower := by
      rcases hSecondSuccessorLeFirst with hEqual | hMember
      · subst firstExponent
        rcases ordinalExponentiation_existsUnique hZF
            𝕀 hωOrdinal hSecondSuccessorOrdinal with
          ⟨_, _, hUnique⟩
        exact Or.inl <|
          (hUnique secondSuccessorPower
              hSecondSuccessorPower).trans
            (hUnique firstPower hFirstPower).symm
      · exact Or.inr <|
          ordinalExponentiation_isIncreasingOnOrdinals
            hZF 𝕀 hωOrdinal
            hOne hOneOmega
            secondSuccessor firstExponent
            hSecondSuccessorOrdinal hFirstExponent hMember
            secondSuccessorPower firstPower
            hSecondSuccessorPower hFirstPower
    have hSecondSuccessorPowerLeOrdinal :=
      eqOrMem_trans
        hα
        hSecondSuccessorPowerLeFirstPower hFirstPowerLe
    rcases hSecondSuccessorPowerLeOrdinal with hEqual | hMember
    · subst α
      exact hSecondSuccessorPowerOrdinal.wellOrder.linear.irrefl
        secondSuccessorPower hαSecondSuccessorPower
        hαSecondSuccessorPower
    · have hSelf :=
        hSecondSuccessorPowerOrdinal.transitive
          α hαSecondSuccessorPower
          secondSuccessorPower hMember
      exact hSecondSuccessorPowerOrdinal.wellOrder.linear.irrefl
        secondSuccessorPower hSelf hSelf
  rcases Structure.IsOrdinal.trichotomy hZF.1
      hFirstExponent hSecondExponent
      (KP.exists_difference (ZF.modelsKP hZF))
      (KP.exists_intersection (ZF.modelsKP hZF)
        firstExponent secondExponent) with
    hSame | hFirstSecond | hSecondFirst
  · exact hZF.1.eq_of_same_members
      firstExponent secondExponent hSame
  · exact False.elim (hContradictionOfFirstSecond hFirstSecond)
  · exact False.elim (hContradictionOfSecondFirst hSecondFirst)

/--
首指数幂作除数时，商是非零自然数。

上界 `α < ω^(exponent+1)` 排除商达到 `ω`，下界
`ω^exponent ≤ α` 排除零商。
-/
theorem ordinalDivision_omegaPower_quotient_mem_omega
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω α exponent successor power successorPower
      quotient remainder : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hExponent : ℳ.IsOrdinal exponent)
    (hSuccessor : ℳ.SuccessorOf successor exponent)
    (hPower :
      ℳ.IsOrdinalExponentiation 𝕀 power ω exponent)
    (hSuccessorPower :
      ℳ.IsOrdinalExponentiation 𝕀
        successorPower ω successor)
    (hPowerLeOrdinal : power = α ∨ ℳ.mem power α)
    (hαSuccessorPower : ℳ.mem α successorPower)
    (hDivision :
      ℳ.IsOrdinalDivision 𝕀
        α power quotient remainder) :
    ℳ.mem quotient ω ∧
      ∃ member, ℳ.mem member quotient := by
  have hωOrdinal := hω.isOrdinal hZF
  have hSuccessorOrdinal :=
    KP.successor_isOrdinal (ZF.modelsKP hZF)
      hExponent hSuccessor
  have hPowerOrdinal :=
    ordinalExponentiation_isOrdinal hZF 𝕀
      hωOrdinal hExponent hPower
  rcases hω.exists_ordinalOne_mem with
    ⟨one, _, hOneOmega⟩
  have hPowerNonempty :=
    ordinalExponentiation_isNonemptyOnOrdinals
      hZF 𝕀 hωOrdinal
      ⟨one, hOneOmega⟩ exponent hExponent power hPower
  rcases hDivision with
    ⟨hQuotientOrdinal, hRemainderPower,
      product, hProduct, hDecomposition⟩
  have hRemainderOrdinal := hPowerOrdinal.mem hRemainderPower
  have hProductOrdinal :=
    ordinalMultiplication_isOrdinal hZF 𝕀
      hPowerOrdinal hQuotientOrdinal hProduct
  have hα :=
    ordinalAddition_isOrdinal hZF 𝕀
      hProductOrdinal hRemainderOrdinal hDecomposition
  have hProductLeOrdinal :=
    ordinalAddition_left_eq_or_mem
      hZF 𝕀 hRemainderOrdinal hDecomposition
  have hαNotMemProduct : ¬ ℳ.mem α product := by
    intro hαProduct
    rcases hProductLeOrdinal with hProductEq | hProductOrdinalOrder
    · subst product
      exact hα.wellOrder.linear.irrefl
        α hαProduct hαProduct
    · have hSelf :=
        hα.transitive product hProductOrdinalOrder
          α hαProduct
      exact hα.wellOrder.linear.irrefl α hSelf hSelf
  rcases (ordinalExponentiation_successor_iff
      hZF 𝕀 hωOrdinal
      hExponent hSuccessor).mp hSuccessorPower with
    ⟨previousPower, hPreviousPower, hSuccessorProduct⟩
  rcases ordinalExponentiation_existsUnique hZF
      𝕀 hωOrdinal hExponent with
    ⟨_, _, hUniquePower⟩
  have hPreviousPowerEq : previousPower = power :=
    (hUniquePower previousPower hPreviousPower).trans
      (hUniquePower power hPower).symm
  subst previousPower
  have hQuotientOmega : ℳ.mem quotient ω := by
    rcases Structure.IsOrdinal.trichotomy hZF.1
        hQuotientOrdinal hωOrdinal
        (KP.exists_difference (ZF.modelsKP hZF))
        (KP.exists_intersection (ZF.modelsKP hZF)
          quotient ω) with
      hSame | hQuotientOmega | hωQuotient
    · have hQuotientEq :=
        hZF.1.eq_of_same_members quotient ω hSame
      subst quotient
      rcases ordinalMultiplication_existsUnique hZF
          𝕀 power hωOrdinal with
        ⟨_, _, hUniqueProduct⟩
      have hProductEq : product = successorPower :=
        (hUniqueProduct product hProduct).trans
          (hUniqueProduct successorPower hSuccessorProduct).symm
      exact False.elim <|
        hαNotMemProduct <| by
          simpa [hProductEq] using hαSuccessorPower
    · exact hQuotientOmega
    · have hSuccessorPowerProduct :
          ℳ.mem successorPower product :=
        ordinalMultiplication_isIncreasingOnOrdinals
          hZF 𝕀 hPowerOrdinal hPowerNonempty
          ω quotient hωOrdinal hQuotientOrdinal
          hωQuotient successorPower product
          hSuccessorProduct hProduct
      have hαProduct : ℳ.mem α product :=
        hProductOrdinal.transitive
          successorPower hSuccessorPowerProduct
          α hαSuccessorPower
      exact False.elim (hαNotMemProduct hαProduct)
  have hQuotientNonempty :
      ∃ member, ℳ.mem member quotient := by
    apply Classical.byContradiction
    intro hNoMember
    have hQuotientEmpty : ∀ member, ¬ ℳ.mem member quotient := by
      simpa only [not_exists] using hNoMember
    have hProductEmpty :=
      (ordinalMultiplication_zero_iff
        hZF 𝕀 hPowerOrdinal hQuotientEmpty).mp
        hProduct
    have hαEqRemainder :=
      ordinalAddition_empty_left hZF 𝕀
        hProductEmpty remainder hRemainderOrdinal
        α hDecomposition
    subst α
    rcases hPowerLeOrdinal with hPowerEq | hPowerRemainder
    · subst power
      exact hRemainderOrdinal.wellOrder.linear.irrefl
        remainder hRemainderPower hRemainderPower
    · have hSelf :=
        hPowerOrdinal.transitive
          remainder hRemainderPower power hPowerRemainder
      exact hPowerOrdinal.wellOrder.linear.irrefl power hSelf hSelf
  exact ⟨hQuotientOmega, hQuotientNonempty⟩

/-- 表示非零序数的有界 Cantor 正规形具有非零长度。 -/
theorem cantorNormalFormBelow_length_nonempty
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω bound α length exponents coefficients values : ℳ.Domain}
    (hαNonempty : ∃ member, ℳ.mem member α)
    (hForm :
      ℳ.IsCantorNormalFormBelow 𝕀
        ω bound α length exponents coefficients values) :
    ∃ index, ℳ.mem index length := by
  rcases hForm with
    ⟨_, hExponents, _, _,
      _, hValues, hInitial, hFinal, _⟩
  apply Classical.byContradiction
  intro hLengthEmpty
  have hNoLengthMember :
      ∀ member, ¬ ℳ.mem member length := by
    simpa only [not_exists] using hLengthEmpty
  rcases hInitial with ⟨zero, hZero, hZeroValue⟩
  have hLengthEqZero : length = zero := by
    apply hZF.1.eq_of_same_members
    intro member
    exact iff_of_false (hNoLengthMember member) (hZero member)
  subst length
  have hαEqZero :=
    hValues.1.2.1.2 zero α zero hFinal hZeroValue
  subst α
  rcases hαNonempty with ⟨member, hMember⟩
  exact hZero member hMember

/-- 非零序数的普通 Cantor 正规形具有非零长度。 -/
theorem cantorNormalForm_length_nonempty
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω α length exponents coefficients values : ℳ.Domain}
    (hαNonempty : ∃ member, ℳ.mem member α)
    (hForm :
      ℳ.IsCantorNormalForm 𝕀
        ω α length exponents coefficients values) :
    ∃ index, ℳ.mem index length :=
  cantorNormalFormBelow_length_nonempty
    hZF hαNonempty hForm

/--
从表示非零序数的有界 Cantor 正规形读出最高次项。

返回的 `previous` 是去掉最高次项后的余项，`coefficient` 是非零自然数，并且最高
指数给出相邻幂区间 `power ≤ α < successorPower`。
-/
theorem cantorNormalFormBelow_exists_leadingTerm_of_length_nonempty
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω bound α length exponents coefficients values : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hLengthNonempty : ∃ index, ℳ.mem index length)
    (hForm :
      ℳ.IsCantorNormalFormBelow 𝕀
        ω bound α length exponents coefficients values) :
    ∃ previousLength exponent coefficient previous
        power successor successorPower,
      ℳ.mem previousLength ω ∧
        ℳ.SuccessorOf length previousLength ∧
        ℳ.PairMember 𝕀
          previousLength exponent exponents ∧
        ℳ.PairMember 𝕀
          previousLength coefficient coefficients ∧
        ℳ.PairMember 𝕀
          previousLength previous values ∧
        ℳ.IsOrdinal exponent ∧
        ℳ.mem coefficient ω ∧
        (∃ member, ℳ.mem member coefficient) ∧
        ℳ.IsOrdinalExponentiation 𝕀
          power ω exponent ∧
        ℳ.IsOrdinalDivision 𝕀
          α power coefficient previous ∧
        ℳ.SuccessorOf successor exponent ∧
        ℳ.IsOrdinalExponentiation 𝕀
          successorPower ω successor ∧
        (power = α ∨ ℳ.mem power α) ∧
        ℳ.mem α successorPower := by
  rcases hForm with
    ⟨hLengthOmega, hExponents, hCoefficients,
      valueLength, hValueLengthSuccessor, hValues,
      _, hFinal, hSteps⟩
  rcases hω.exists_predecessor_of_mem_of_nonempty
      hZF hLengthOmega hLengthNonempty with
    ⟨previousLength, hPreviousLengthOmega, hLengthSuccessor⟩
  have hPreviousLengthLength :
      ℳ.mem previousLength length :=
    (hLengthSuccessor previousLength).mpr
      (Or.inr fun _ => Iff.rfl)
  rcases (hExponents.1.1.2.2 previousLength).mp
      hPreviousLengthLength with
    ⟨exponent, hExponentValue⟩
  rcases hCoefficients.2.2.2
      previousLength hPreviousLengthLength with
    ⟨coefficient, hCoefficientOmega, hCoefficientValue⟩
  have hLengthValueLength :
      ℳ.mem length valueLength :=
    (hValueLengthSuccessor length).mpr
      (Or.inr fun _ => Iff.rfl)
  have hPreviousLengthValueLength :
      ℳ.mem previousLength valueLength :=
    hValues.1.1.transitive
      length hLengthValueLength
      previousLength hPreviousLengthLength
  rcases (hValues.1.2.2 previousLength).mp
      hPreviousLengthValueLength with
    ⟨previous, hPreviousValue⟩
  rcases hSteps previousLength hPreviousLengthLength
      exponent coefficient previous
      hExponentValue hCoefficientValue hPreviousValue with
    ⟨hCoefficientNonempty,
      next, power, monomial, output,
      hNext, hPower, hPreviousPower, _,
      hMonomial, hOutput, hPowerLeOutput, hNextOutput⟩
  have hNextEq : next = length :=
    Structure.SuccessorOf.eq hZF.1 hNext hLengthSuccessor
  subst next
  have hOutputEq :=
    hValues.1.2.1.2 length output α hNextOutput hFinal
  subst output
  have hExponentOrdinal :=
    hExponents.1.2 previousLength hPreviousLengthLength
      exponent hExponentValue
  have hCoefficientOrdinal :=
    hω.members_areOrdinals hZF
      coefficient hCoefficientOmega
  have hDivision :
      ℳ.IsOrdinalDivision 𝕀
        α power coefficient previous :=
    ⟨hCoefficientOrdinal, hPreviousPower,
      monomial, hMonomial, hOutput⟩
  rcases KP.exists_successor (ZF.modelsKP hZF) exponent with
    ⟨successor, hSuccessor⟩
  have hSuccessorOrdinal :=
    KP.successor_isOrdinal (ZF.modelsKP hZF)
      hExponentOrdinal hSuccessor
  have hωOrdinal := hω.isOrdinal hZF
  rcases ordinalExponentiation_existsUnique hZF
      𝕀 hωOrdinal hSuccessorOrdinal with
    ⟨successorPower, hSuccessorPower, _⟩
  rcases (ordinalExponentiation_successor_iff
      hZF 𝕀 hωOrdinal
      hExponentOrdinal hSuccessor).mp hSuccessorPower with
    ⟨previousPower, hPreviousPower',
      hSuccessorPowerProduct⟩
  rcases ordinalExponentiation_existsUnique hZF
      𝕀 hωOrdinal hExponentOrdinal with
    ⟨_, _, hUniquePower⟩
  have hPreviousPowerEq : previousPower = power :=
    (hUniquePower previousPower hPreviousPower').trans
      (hUniquePower power hPower).symm
  subst previousPower
  have hPowerOrdinal :=
    ordinalExponentiation_isOrdinal hZF 𝕀
      hωOrdinal hExponentOrdinal hPower
  have hαSuccessorPower :
      ℳ.mem α successorPower :=
    (ordinalMultiplication_mem_iff
      hZF 𝕀 hPowerOrdinal
      hωOrdinal hSuccessorPowerProduct).mpr
      ⟨coefficient, hCoefficientOmega,
        monomial, hMonomial,
        previous, hPreviousPower, hOutput⟩
  exact
    ⟨previousLength, exponent, coefficient, previous,
      power, successor, successorPower,
      hPreviousLengthOmega, hLengthSuccessor,
      hExponentValue, hCoefficientValue, hPreviousValue,
      hExponentOrdinal, hCoefficientOmega,
      hCoefficientNonempty, hPower, hDivision,
      hSuccessor, hSuccessorPower, hPowerLeOutput,
      hαSuccessorPower⟩

/-- 从表示非零序数的有界 Cantor 正规形读出最高次项。 -/
theorem cantorNormalFormBelow_exists_leadingTerm
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω bound α length exponents coefficients values : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hαNonempty : ∃ member, ℳ.mem member α)
    (hForm :
      ℳ.IsCantorNormalFormBelow 𝕀
        ω bound α length exponents coefficients values) :
    ∃ previousLength exponent coefficient previous
        power successor successorPower,
      ℳ.mem previousLength ω ∧
        ℳ.SuccessorOf length previousLength ∧
        ℳ.PairMember 𝕀
          previousLength exponent exponents ∧
        ℳ.PairMember 𝕀
          previousLength coefficient coefficients ∧
        ℳ.PairMember 𝕀
          previousLength previous values ∧
        ℳ.IsOrdinal exponent ∧
        ℳ.mem coefficient ω ∧
        (∃ member, ℳ.mem member coefficient) ∧
        ℳ.IsOrdinalExponentiation 𝕀
          power ω exponent ∧
        ℳ.IsOrdinalDivision 𝕀
          α power coefficient previous ∧
        ℳ.SuccessorOf successor exponent ∧
        ℳ.IsOrdinalExponentiation 𝕀
          successorPower ω successor ∧
        (power = α ∨ ℳ.mem power α) ∧
        ℳ.mem α successorPower :=
  cantorNormalFormBelow_exists_leadingTerm_of_length_nonempty
    hZF 𝕀 hω
      (cantorNormalFormBelow_length_nonempty
        hZF hαNonempty hForm)
      hForm

/-- 从非零序数的普通 Cantor 正规形读出最高次项。 -/
theorem cantorNormalForm_exists_leadingTerm
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω α length exponents coefficients values : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hαNonempty : ∃ member, ℳ.mem member α)
    (hForm :
      ℳ.IsCantorNormalForm 𝕀
        ω α length exponents coefficients values) :
    ∃ previousLength exponent coefficient previous
        power successor successorPower,
      ℳ.mem previousLength ω ∧
        ℳ.SuccessorOf length previousLength ∧
        ℳ.PairMember 𝕀
          previousLength exponent exponents ∧
        ℳ.PairMember 𝕀
          previousLength coefficient coefficients ∧
        ℳ.PairMember 𝕀
          previousLength previous values ∧
        ℳ.IsOrdinal exponent ∧
        ℳ.mem coefficient ω ∧
        (∃ member, ℳ.mem member coefficient) ∧
        ℳ.IsOrdinalExponentiation 𝕀
          power ω exponent ∧
        ℳ.IsOrdinalDivision 𝕀
          α power coefficient previous ∧
        ℳ.SuccessorOf successor exponent ∧
        ℳ.IsOrdinalExponentiation 𝕀
          successorPower ω successor ∧
        (power = α ∨ ℳ.mem power α) ∧
        ℳ.mem α successorPower :=
  cantorNormalFormBelow_exists_leadingTerm
    hZF 𝕀 hω hαNonempty hForm

/--
去掉有界 Cantor 正规形的最高次项后，函数图限制给出同一环境上界下的余项正规形。
-/
theorem cantorNormalFormBelow_exists_prefix
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω bound α length exponents coefficients values : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hαNonempty : ∃ member, ℳ.mem member α)
    (hForm :
      ℳ.IsCantorNormalFormBelow 𝕀
        ω bound α length exponents coefficients values) :
    ∃ previousLength exponent coefficient previous
        power successor successorPower
        previousExponents previousCoefficients previousValues,
      ℳ.mem previousLength ω ∧
        ℳ.SuccessorOf length previousLength ∧
        ℳ.PairMember 𝕀
          previousLength exponent exponents ∧
        ℳ.PairMember 𝕀
          previousLength coefficient coefficients ∧
        ℳ.PairMember 𝕀
          previousLength previous values ∧
        ℳ.IsOrdinal exponent ∧
        ℳ.mem coefficient ω ∧
        (∃ member, ℳ.mem member coefficient) ∧
        ℳ.IsOrdinalExponentiation 𝕀
          power ω exponent ∧
        ℳ.IsOrdinalDivision 𝕀
          α power coefficient previous ∧
        ℳ.SuccessorOf successor exponent ∧
        ℳ.IsOrdinalExponentiation 𝕀
          successorPower ω successor ∧
        (power = α ∨ ℳ.mem power α) ∧
        ℳ.mem α successorPower ∧
        ℳ.IsRestrictionOf 𝕀
          previousExponents exponents previousLength ∧
        ℳ.IsRestrictionOf 𝕀
          previousCoefficients coefficients previousLength ∧
        ℳ.IsRestrictionOf 𝕀
          previousValues values length ∧
        ℳ.IsCantorNormalFormBelow 𝕀
          ω bound previous previousLength
          previousExponents previousCoefficients previousValues := by
  rcases cantorNormalFormBelow_exists_leadingTerm
      hZF 𝕀 hω hαNonempty hForm with
    ⟨previousLength, exponent, coefficient, previous,
      power, successor, successorPower,
      hPreviousLengthOmega, hLengthSuccessor,
      hExponentValue, hCoefficientValue, hPreviousValue,
      hExponentOrdinal, hCoefficientOmega,
      hCoefficientNonempty, hPower, hDivision,
      hSuccessor, hSuccessorPower, hPowerLeOrdinal,
      hαSuccessorPower⟩
  rcases hForm with
    ⟨hLengthOmega, hExponents, hCoefficients,
      valueLength, hValueLengthSuccessor, hValues,
      hInitial, hFinal, hSteps⟩
  have hLengthOrdinal := hExponents.1.1.1
  have hPreviousLengthLength :
      ℳ.mem previousLength length :=
    (hLengthSuccessor previousLength).mpr
      (Or.inr fun _ => Iff.rfl)
  have hPreviousLengthOrdinal :=
    hLengthOrdinal.mem hPreviousLengthLength
  have hLengthValueLength :
      ℳ.mem length valueLength :=
    (hValueLengthSuccessor length).mpr
      (Or.inr fun _ => Iff.rfl)
  rcases exists_restriction hZF 𝕀
      exponents previousLength with
    ⟨previousExponents, hPreviousExponentsRestriction⟩
  rcases exists_restriction hZF 𝕀
      coefficients previousLength with
    ⟨previousCoefficients, hPreviousCoefficientsRestriction⟩
  rcases exists_restriction hZF 𝕀
      values length with
    ⟨previousValues, hPreviousValuesRestriction⟩
  have hPreviousExponentsSequence :
      ℳ.IsSequenceOfLength 𝕀
        previousExponents previousLength :=
    hExponents.1.1.restriction
      hPreviousLengthLength hPreviousExponentsRestriction
  have hPreviousExponentsOrdinalValued :
      ℳ.IsOrdinalValuedSequence 𝕀
        previousExponents previousLength := by
    refine ⟨hPreviousExponentsSequence, ?_⟩
    intro index hIndex value hValue
    have hIndexLength :=
      hLengthOrdinal.transitive
        previousLength hPreviousLengthLength index hIndex
    exact hExponents.1.2 index hIndexLength value
      ((hPreviousExponentsRestriction.2 index value).mp hValue).2
  have hPreviousExponents :
      ℳ.IsIncreasingOrdinalSequence 𝕀
        previousExponents previousLength := by
    refine ⟨hPreviousExponentsOrdinalValued, ?_⟩
    intro left hLeft right hRight hLeftRight
        leftValue rightValue hLeftValue hRightValue
    have hLeftLength :=
      hLengthOrdinal.transitive
        previousLength hPreviousLengthLength left hLeft
    have hRightLength :=
      hLengthOrdinal.transitive
        previousLength hPreviousLengthLength right hRight
    exact hExponents.2 left hLeftLength right hRightLength
      hLeftRight leftValue rightValue
      ((hPreviousExponentsRestriction.2
        left leftValue).mp hLeftValue).2
      ((hPreviousExponentsRestriction.2
        right rightValue).mp hRightValue).2
  let coefficientSequence :
      ℳ.IsSequenceOfLength 𝕀 coefficients length :=
    ⟨hCoefficients.1, hCoefficients.2.1,
      hCoefficients.2.2.1⟩
  have hPreviousCoefficientsSequence :
      ℳ.IsSequenceOfLength 𝕀
        previousCoefficients previousLength :=
    coefficientSequence.restriction
      hPreviousLengthLength hPreviousCoefficientsRestriction
  have hPreviousCoefficients :
      ℳ.IsSequenceIn 𝕀
        previousCoefficients previousLength ω := by
    refine
      ⟨hPreviousCoefficientsSequence.1,
        hPreviousCoefficientsSequence.2.1,
        hPreviousCoefficientsSequence.2.2, ?_⟩
    intro index hIndex
    have hIndexLength :=
      hLengthOrdinal.transitive
        previousLength hPreviousLengthLength index hIndex
    rcases hCoefficients.2.2.2 index hIndexLength with
      ⟨value, hValueOmega, hValue⟩
    exact
      ⟨value, hValueOmega,
        (hPreviousCoefficientsRestriction.2 index value).mpr
          ⟨hIndex, hValue⟩⟩
  have hPreviousValuesSequence :
      ℳ.IsSequenceOfLength 𝕀 previousValues length :=
    hValues.1.restriction
      hLengthValueLength hPreviousValuesRestriction
  have hPreviousValues :
      ℳ.IsOrdinalValuedSequence 𝕀 previousValues length := by
    refine ⟨hPreviousValuesSequence, ?_⟩
    intro index hIndex value hValue
    have hIndexValueLength :=
      hValues.1.1.transitive
        length hLengthValueLength index hIndex
    exact hValues.2 index hIndexValueLength value
      ((hPreviousValuesRestriction.2 index value).mp hValue).2
  have hPreviousInitial :
      ∃ zero,
        (∀ member, ¬ ℳ.mem member zero) ∧
        ℳ.PairMember 𝕀 zero zero previousValues := by
    rcases hInitial with ⟨zero, hZero, hZeroValue⟩
    have hZeroLength :
        ℳ.mem zero length :=
      hLengthOrdinal.empty_mem_of_nonempty
        (ZF.modelsKP hZF)
        ⟨previousLength, hPreviousLengthLength⟩ hZero
    exact
      ⟨zero, hZero,
        (hPreviousValuesRestriction.2 zero zero).mpr
          ⟨hZeroLength, hZeroValue⟩⟩
  have hPreviousFinal :
      ℳ.PairMember 𝕀
        previousLength previous previousValues :=
    (hPreviousValuesRestriction.2
      previousLength previous).mpr
      ⟨hPreviousLengthLength, hPreviousValue⟩
  have hPreviousSteps :
      ∀ index, ℳ.mem index previousLength →
        ℳ.IsCantorNormalFormStep 𝕀
          ω bound previousExponents
          previousCoefficients previousValues index := by
    intro index hIndex
    have hIndexLength :=
      hLengthOrdinal.transitive
        previousLength hPreviousLengthLength index hIndex
    intro oldExponent oldCoefficient oldPrevious
        hOldExponent hOldCoefficient hOldPrevious
    have hOldExponent' :=
      (hPreviousExponentsRestriction.2
        index oldExponent).mp hOldExponent |>.2
    have hOldCoefficient' :=
      (hPreviousCoefficientsRestriction.2
        index oldCoefficient).mp hOldCoefficient |>.2
    have hOldPrevious' :=
      (hPreviousValuesRestriction.2
        index oldPrevious).mp hOldPrevious |>.2
    rcases hSteps index hIndexLength
        oldExponent oldCoefficient oldPrevious
        hOldExponent' hOldCoefficient' hOldPrevious' with
      ⟨hOldCoefficientNonempty,
        next, oldPower, monomial, output,
        hNext, hOldPower, hOldPreviousPower,
        hOldPowerBound, hMonomial, hOutput,
        hOldPowerOutput, hNextOutput⟩
    have hIndexOrdinal :=
      hPreviousLengthOrdinal.mem hIndex
    have hNextOrdinal :=
      KP.successor_isOrdinal (ZF.modelsKP hZF)
        hIndexOrdinal hNext
    have hNextLePreviousLength :
        next = previousLength ∨ ℳ.mem next previousLength := by
      rcases Structure.IsOrdinal.trichotomy hZF.1
          hNextOrdinal hPreviousLengthOrdinal
          (KP.exists_difference (ZF.modelsKP hZF))
          (KP.exists_intersection (ZF.modelsKP hZF)
            next previousLength) with
        hSame | hNextPrevious | hPreviousNext
      · exact Or.inl <|
          hZF.1.eq_of_same_members
            next previousLength hSame
      · exact Or.inr hNextPrevious
      · rcases (hNext previousLength).mp hPreviousNext with
          hPreviousIndex | hPreviousIndex
        · have hSelf :=
            hPreviousLengthOrdinal.transitive
              index hIndex previousLength hPreviousIndex
          exact False.elim <|
            hPreviousLengthOrdinal.wellOrder.linear.irrefl
              previousLength hSelf hSelf
        · have hPreviousEq :=
            hZF.1.eq_of_same_members
              previousLength index hPreviousIndex
          subst previousLength
          exact False.elim <|
            hIndexOrdinal.wellOrder.linear.irrefl
              index hIndex hIndex
    have hNextLength : ℳ.mem next length :=
      (hLengthSuccessor next).mpr <| by
        rcases hNextLePreviousLength with hEqual | hMember
        · subst next
          exact Or.inr fun _ => Iff.rfl
        · exact Or.inl hMember
    exact
      ⟨hOldCoefficientNonempty,
        next, oldPower, monomial, output,
        hNext, hOldPower, hOldPreviousPower,
        hOldPowerBound, hMonomial, hOutput,
        hOldPowerOutput,
        (hPreviousValuesRestriction.2 next output).mpr
          ⟨hNextLength, hNextOutput⟩⟩
  have hPreviousForm :
      ℳ.IsCantorNormalFormBelow 𝕀
        ω bound previous previousLength
        previousExponents previousCoefficients previousValues :=
    ⟨hPreviousLengthOmega,
      hPreviousExponents, hPreviousCoefficients,
      length, hLengthSuccessor, hPreviousValues,
      hPreviousInitial, hPreviousFinal, hPreviousSteps⟩
  exact
    ⟨previousLength, exponent, coefficient, previous,
      power, successor, successorPower,
      previousExponents, previousCoefficients, previousValues,
      hPreviousLengthOmega, hLengthSuccessor,
      hExponentValue, hCoefficientValue, hPreviousValue,
      hExponentOrdinal, hCoefficientOmega,
      hCoefficientNonempty, hPower, hDivision,
      hSuccessor, hSuccessorPower, hPowerLeOrdinal,
      hαSuccessorPower,
      hPreviousExponentsRestriction,
      hPreviousCoefficientsRestriction,
      hPreviousValuesRestriction,
      hPreviousForm⟩

/-- 有界 Cantor 正规形若表示空序数，则其长度为空。 -/
theorem cantorNormalFormBelow_length_empty_of_ordinal_empty
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω bound α length exponents coefficients values : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hαEmpty : ∀ member, ¬ ℳ.mem member α)
    (hForm :
      ℳ.IsCantorNormalFormBelow 𝕀
        ω bound α length exponents coefficients values) :
    ∀ index, ¬ ℳ.mem index length := by
  intro index hIndex
  rcases cantorNormalFormBelow_exists_leadingTerm_of_length_nonempty
      hZF 𝕀 hω ⟨index, hIndex⟩ hForm with
    ⟨_, exponent, _, _, power, _, _,
      _, _, _, _, _, hExponent, _, _, hPower, _,
      _, _, hPowerLeOrdinal, _⟩
  have hωOrdinal := hω.isOrdinal hZF
  rcases hω.exists_ordinalOne_mem with
    ⟨one, _, hOneOmega⟩
  have hPowerNonempty :=
    ordinalExponentiation_isNonemptyOnOrdinals
      hZF 𝕀 hωOrdinal
      ⟨one, hOneOmega⟩ exponent hExponent power hPower
  rcases hPowerLeOrdinal with hEqual | hMember
  · rcases hPowerNonempty with ⟨member, hMember⟩
    exact hαEmpty member (by simpa [hEqual] using hMember)
  · exact hαEmpty power hMember

/-- 同一空序数的两个有界 Cantor 正规形完全相等。 -/
theorem cantorNormalFormBelow_unique_of_ordinal_empty
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω bound α
      firstLength firstExponents firstCoefficients firstValues
      secondLength secondExponents secondCoefficients secondValues :
        ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hαEmpty : ∀ member, ¬ ℳ.mem member α)
    (hFirst :
      ℳ.IsCantorNormalFormBelow 𝕀
        ω bound α firstLength
        firstExponents firstCoefficients firstValues)
    (hSecond :
      ℳ.IsCantorNormalFormBelow 𝕀
        ω bound α secondLength
        secondExponents secondCoefficients secondValues) :
    firstLength = secondLength ∧
      firstExponents = secondExponents ∧
      firstCoefficients = secondCoefficients ∧
      firstValues = secondValues := by
  have hFirstLengthEmpty :=
    cantorNormalFormBelow_length_empty_of_ordinal_empty
      hZF 𝕀 hω hαEmpty hFirst
  have hSecondLengthEmpty :=
    cantorNormalFormBelow_length_empty_of_ordinal_empty
      hZF 𝕀 hω hαEmpty hSecond
  rcases hFirst with
    ⟨_, hFirstExponents, hFirstCoefficients,
      firstValueLength, hFirstValueLengthSuccessor,
      hFirstValues, _, hFirstFinal, _⟩
  rcases hSecond with
    ⟨_, hSecondExponents, hSecondCoefficients,
      secondValueLength, hSecondValueLengthSuccessor,
      hSecondValues, _, hSecondFinal, _⟩
  have hLengthEq : firstLength = secondLength := by
    apply hZF.1.eq_of_same_members
    intro member
    exact iff_of_false
      (hFirstLengthEmpty member) (hSecondLengthEmpty member)
  subst secondLength
  have hExponentsEq : firstExponents = secondExponents := by
    apply hFirstExponents.1.1.2.1.1.eq_of_pairMember_iff
      hZF.1 hSecondExponents.1.1.2.1.1
    intro input output
    constructor
    · intro hValue
      have hInput :=
        (hFirstExponents.1.1.2.2 input).mpr
          ⟨output, hValue⟩
      exact False.elim (hFirstLengthEmpty input hInput)
    · intro hValue
      have hInput :=
        (hSecondExponents.1.1.2.2 input).mpr
          ⟨output, hValue⟩
      exact False.elim (hSecondLengthEmpty input hInput)
  have hCoefficientsEq :
      firstCoefficients = secondCoefficients := by
    apply hFirstCoefficients.2.1.1.eq_of_pairMember_iff
      hZF.1 hSecondCoefficients.2.1.1
    intro input output
    constructor
    · intro hValue
      have hInput :=
        (hFirstCoefficients.2.2.1 input).mpr
          ⟨output, hValue⟩
      exact False.elim (hFirstLengthEmpty input hInput)
    · intro hValue
      have hInput :=
        (hSecondCoefficients.2.2.1 input).mpr
          ⟨output, hValue⟩
      exact False.elim (hSecondLengthEmpty input hInput)
  have hValuesEq : firstValues = secondValues := by
    apply hFirstValues.1.2.1.1.eq_of_pairMember_iff
      hZF.1 hSecondValues.1.2.1.1
    intro input output
    have transfer
        {left right leftValueLength : ℳ.Domain}
        (hLeftValues :
          ℳ.IsOrdinalValuedSequence 𝕀
            left leftValueLength)
        (hLeftValueLengthSuccessor :
          ℳ.SuccessorOf leftValueLength firstLength)
        (hLeftFinal :
          ℳ.PairMember 𝕀
            firstLength α left)
        (hRightFinal :
          ℳ.PairMember 𝕀
            firstLength α right)
        (hValue :
          ℳ.PairMember 𝕀 input output left) :
        ℳ.PairMember 𝕀 input output right := by
      have hInputValueLength :=
        (hLeftValues.1.2.2 input).mpr
          ⟨output, hValue⟩
      rcases (hLeftValueLengthSuccessor input).mp
          hInputValueLength with
        hInputLength | hInputSame
      · exact False.elim
          (hFirstLengthEmpty input hInputLength)
      · have hInputEq :=
          hZF.1.eq_of_same_members
            input firstLength hInputSame
        subst input
        have hOutputEq :=
          hLeftValues.1.2.1.2
            firstLength output α hValue hLeftFinal
        subst output
        exact hRightFinal
    constructor
    · exact transfer
        hFirstValues hFirstValueLengthSuccessor
        hFirstFinal hSecondFinal
    · exact transfer
        hSecondValues hSecondValueLengthSuccessor
        hSecondFinal hFirstFinal
  exact ⟨rfl, hExponentsEq, hCoefficientsEq, hValuesEq⟩

/-- 将新的最高次单项式追加到余项的对象层正规形。 -/
theorem exists_cantorNormalForm_of_remainder
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω α remainder length exponents coefficients values
      exponent successor power successorPower quotient : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hRemainderForm :
      ℳ.IsCantorNormalForm 𝕀
        ω remainder length exponents coefficients values)
    (hExponent : ℳ.IsOrdinal exponent)
    (hSuccessor : ℳ.SuccessorOf successor exponent)
    (hPower :
      ℳ.IsOrdinalExponentiation 𝕀 power ω exponent)
    (hSuccessorPower :
      ℳ.IsOrdinalExponentiation 𝕀
        successorPower ω successor)
    (hPowerLeOrdinal : power = α ∨ ℳ.mem power α)
    (hαSuccessorPower : ℳ.mem α successorPower)
    (hDivision :
      ℳ.IsOrdinalDivision 𝕀
        α power quotient remainder) :
    ∃ newLength newExponents newCoefficients newValues,
      ℳ.IsCantorNormalForm 𝕀
        ω α newLength
        newExponents newCoefficients newValues := by
  have hωOrdinal := hω.isOrdinal hZF
  rcases hω.exists_ordinalOne_mem with
    ⟨one, hOne, hOneOmega⟩
  have hQuotientData :=
    ordinalDivision_omegaPower_quotient_mem_omega
      hZF 𝕀 hω hExponent hSuccessor
      hPower hSuccessorPower hPowerLeOrdinal
      hαSuccessorPower hDivision
  rcases hQuotientData with
    ⟨hQuotientOmega, hQuotientNonempty⟩
  rcases hDivision with
    ⟨hQuotientOrdinal, hRemainderPower,
      product, hProduct, hDecomposition⟩
  have hPowerOrdinal :=
    ordinalExponentiation_isOrdinal hZF 𝕀
      hωOrdinal hExponent hPower
  have hRemainderOrdinal := hPowerOrdinal.mem hRemainderPower
  have hProductOrdinal :=
    ordinalMultiplication_isOrdinal hZF 𝕀
      hPowerOrdinal hQuotientOrdinal hProduct
  have hα :=
    ordinalAddition_isOrdinal hZF 𝕀
      hProductOrdinal hRemainderOrdinal hDecomposition
  rcases hRemainderForm with
    ⟨hLengthOmega, hExponents, hCoefficients,
      valueLength, hValueLengthSuccessor, hValues,
      hInitial, hFinal, hSteps⟩
  have hLengthOrdinal := hExponents.1.1.1
  rcases hω.1.2 length hLengthOmega with
    ⟨newLength, hNewLengthSuccessor, hNewLengthOmega⟩
  have hNewLengthOrdinal := hωOrdinal.mem hNewLengthOmega
  have hValueLengthEq : valueLength = newLength :=
    Structure.SuccessorOf.eq hZF.1
      hValueLengthSuccessor hNewLengthSuccessor
  subst valueLength
  rcases hω.1.2 newLength hNewLengthOmega with
    ⟨newValueLength, hNewValueLengthSuccessor,
      hNewValueLengthOmega⟩
  have hNewValueLengthOrdinal :=
    hωOrdinal.mem hNewValueLengthOmega
  rcases Structure.IsSequenceOfLength.exists_append
      (ZF.modelsKP hZF) 𝕀
      hExponents.1.1 hNewLengthOrdinal
      hNewLengthSuccessor with
    ⟨newExponents, hNewExponentsLength, hNewExponentsPairs⟩
  let coefficientSequence :
      ℳ.IsSequenceOfLength 𝕀 coefficients length :=
    ⟨hCoefficients.1, hCoefficients.2.1,
      hCoefficients.2.2.1⟩
  rcases Structure.IsSequenceOfLength.exists_append
      (ZF.modelsKP hZF) 𝕀
      coefficientSequence hNewLengthOrdinal
      hNewLengthSuccessor with
    ⟨newCoefficients, hNewCoefficientsLength,
      hNewCoefficientsPairs⟩
  rcases Structure.IsSequenceOfLength.exists_append
      (ZF.modelsKP hZF) 𝕀
      hValues.1 hNewValueLengthOrdinal
      hNewValueLengthSuccessor with
    ⟨newValues, hNewValuesLength, hNewValuesPairs⟩
  have hOldExponentMem :
      ∀ index, ℳ.mem index length →
        ∀ oldExponent,
          ℳ.PairMember 𝕀
              index oldExponent exponents →
            ℳ.mem oldExponent exponent := by
    intro index hIndex oldExponent hOldExponent
    rcases hCoefficients.2.2.2 index hIndex with
      ⟨coefficient, _, hCoefficient⟩
    have hIndexNewLength :
        ℳ.mem index newLength :=
      (hNewLengthSuccessor index).mpr (Or.inl hIndex)
    rcases (hValues.1.2.2 index).mp hIndexNewLength with
      ⟨previous, hPrevious⟩
    rcases hSteps index hIndex oldExponent coefficient previous
        hOldExponent hCoefficient hPrevious with
      ⟨_, next, oldPower, monomial, output,
        _, hOldPower, _, hOldPowerLeRemainder, _, _, _, _⟩
    have hOldPowerPower : ℳ.mem oldPower power := by
      rcases hOldPowerLeRemainder with hEqual | hMember
      · simpa [hEqual] using hRemainderPower
      · exact hPowerOrdinal.transitive
          remainder hRemainderPower oldPower hMember
    exact
      (ordinalExponentiation_values_mem_iff
        hZF 𝕀 hωOrdinal hOne hOneOmega
        (hExponents.1.2 index hIndex oldExponent hOldExponent)
        hExponent hOldPower hPower).mp hOldPowerPower
  have hNewExponentsOrdinalValued :
      ℳ.IsOrdinalValuedSequence 𝕀
        newExponents newLength := by
    refine ⟨hNewExponentsLength, ?_⟩
    intro index hIndex value hValue
    rcases (hNewExponentsPairs index value).mp hValue with
      hOld | ⟨_, hValueEq⟩
    · have hIndexLength :=
        (hExponents.1.1.2.2 index).mpr ⟨value, hOld⟩
      exact hExponents.1.2 index hIndexLength value hOld
    · subst value
      exact hExponent
  have hNewExponents :
      ℳ.IsIncreasingOrdinalSequence 𝕀
        newExponents newLength := by
    refine ⟨hNewExponentsOrdinalValued, ?_⟩
    intro left hLeft right hRight hLeftRight
        leftValue rightValue hLeftValue hRightValue
    rcases (hNewExponentsPairs left leftValue).mp hLeftValue with
      hLeftOld | ⟨hLeftEq, hLeftValueEq⟩ <;>
      rcases (hNewExponentsPairs right rightValue).mp hRightValue with
        hRightOld | ⟨hRightEq, hRightValueEq⟩
    · have hLeftLength :=
        (hExponents.1.1.2.2 left).mpr
          ⟨leftValue, hLeftOld⟩
      have hRightLength :=
        (hExponents.1.1.2.2 right).mpr
          ⟨rightValue, hRightOld⟩
      exact hExponents.2 left hLeftLength right hRightLength
        hLeftRight leftValue rightValue hLeftOld hRightOld
    · subst right
      subst rightValue
      have hLeftLength :=
        (hExponents.1.1.2.2 left).mpr
          ⟨leftValue, hLeftOld⟩
      exact hOldExponentMem left hLeftLength leftValue hLeftOld
    · subst left
      have hRightLength :=
        (hExponents.1.1.2.2 right).mpr
          ⟨rightValue, hRightOld⟩
      have hSelf :=
        hLengthOrdinal.transitive
          right hRightLength length hLeftRight
      exact False.elim <|
        hLengthOrdinal.wellOrder.linear.irrefl
          length hSelf hSelf
    · subst left
      subst right
      exact False.elim <|
        hLengthOrdinal.wellOrder.linear.irrefl
          length hLeftRight hLeftRight
  have hNewCoefficients :
      ℳ.IsSequenceIn 𝕀
        newCoefficients newLength ω := by
    refine
      ⟨hNewLengthOrdinal,
        hNewCoefficientsLength.2.1,
        hNewCoefficientsLength.2.2, ?_⟩
    intro index hIndex
    rcases (hNewCoefficientsLength.2.2 index).mp hIndex with
      ⟨value, hValue⟩
    rcases (hNewCoefficientsPairs index value).mp hValue with
      hOld | ⟨_, hValueEq⟩
    · have hIndexLength :=
        (coefficientSequence.2.2 index).mpr ⟨value, hOld⟩
      rcases hCoefficients.2.2.2 index hIndexLength with
        ⟨selected, hSelectedOmega, hSelected⟩
      have hValueEqSelected :=
        hCoefficients.2.1.2 index value selected hOld hSelected
      subst selected
      exact ⟨value, hSelectedOmega, hValue⟩
    · subst value
      exact ⟨quotient, hQuotientOmega, hValue⟩
  have hNewValuesOrdinal :
      ℳ.IsOrdinalValuedSequence 𝕀
        newValues newValueLength := by
    refine ⟨hNewValuesLength, ?_⟩
    intro index hIndex value hValue
    rcases (hNewValuesPairs index value).mp hValue with
      hOld | ⟨_, hValueEq⟩
    · have hIndexNewLength :=
        (hValues.1.2.2 index).mpr ⟨value, hOld⟩
      exact hValues.2 index hIndexNewLength value hOld
    · subst value
      exact hα
  have hNewInitial :
      ∃ zero,
        (∀ member, ¬ ℳ.mem member zero) ∧
        ℳ.PairMember 𝕀 zero zero newValues := by
    rcases hInitial with ⟨zero, hZero, hZeroValue⟩
    exact
      ⟨zero, hZero,
        (hNewValuesPairs zero zero).mpr (Or.inl hZeroValue)⟩
  have hNewFinal :
      ℳ.PairMember 𝕀 newLength α newValues :=
    (hNewValuesPairs newLength α).mpr
      (Or.inr ⟨rfl, rfl⟩)
  have hLiftPowerBound
      {oldPower : ℳ.Domain}
      (hOldPowerLeRemainder :
        oldPower = remainder ∨ ℳ.mem oldPower remainder) :
      oldPower = α ∨ ℳ.mem oldPower α := by
    apply Or.inr
    rcases hPowerLeOrdinal with hPowerEq | hPowerOrdinalOrder
    · subst α
      rcases hOldPowerLeRemainder with hEqual | hMember
      · simpa [hEqual] using hRemainderPower
      · exact hPowerOrdinal.transitive
          remainder hRemainderPower oldPower hMember
    · rcases hOldPowerLeRemainder with hEqual | hMember
      · subst oldPower
        exact hα.transitive
          power hPowerOrdinalOrder remainder hRemainderPower
      · exact hα.transitive
          power hPowerOrdinalOrder oldPower <|
            hPowerOrdinal.transitive
              remainder hRemainderPower oldPower hMember
  have hNewSteps :
      ∀ index, ℳ.mem index newLength →
        ℳ.IsCantorNormalFormStep 𝕀
          ω α newExponents
          newCoefficients newValues index := by
    intro index hIndex
    rcases (hNewLengthSuccessor index).mp hIndex with
      hIndexLength | hIndexSame
    · intro oldExponent coefficient previous
        hOldExponent hCoefficient hPrevious
      have hOldExponent' :=
        Structure.pairMember_old_of_append
          hLengthOrdinal hIndexLength
          hNewExponentsPairs hOldExponent
      have hCoefficient' :=
        Structure.pairMember_old_of_append
          hLengthOrdinal hIndexLength
          hNewCoefficientsPairs hCoefficient
      have hIndexNewLength :
          ℳ.mem index newLength :=
        (hNewLengthSuccessor index).mpr
          (Or.inl hIndexLength)
      have hPrevious' :=
        Structure.pairMember_old_of_append
          hNewLengthOrdinal hIndexNewLength
          hNewValuesPairs hPrevious
      rcases hSteps index hIndexLength
          oldExponent coefficient previous
          hOldExponent' hCoefficient' hPrevious' with
        ⟨hCoefficientNonempty,
          next, oldPower, monomial, output,
          hNext, hOldPower, hPreviousPower,
          hOldPowerLeRemainder,
          hMonomial, hOutput, hPowerLeOutput,
          hNextOutput⟩
      exact
        ⟨hCoefficientNonempty,
          next, oldPower, monomial, output,
          hNext, hOldPower, hPreviousPower,
          hLiftPowerBound hOldPowerLeRemainder,
          hMonomial, hOutput, hPowerLeOutput,
          (hNewValuesPairs next output).mpr
            (Or.inl hNextOutput)⟩
    · have hIndexEq :=
        hZF.1.eq_of_same_members index length hIndexSame
      subst index
      intro selectedExponent selectedCoefficient previous
        hSelectedExponent hSelectedCoefficient hPrevious
      have hSelectedExponentEq :=
        Structure.pairMember_new_eq_of_append
          hExponents.1.1 hNewExponentsPairs hSelectedExponent
      have hSelectedCoefficientEq :=
        Structure.pairMember_new_eq_of_append
          coefficientSequence hNewCoefficientsPairs
          hSelectedCoefficient
      have hLengthNewLength :
          ℳ.mem length newLength :=
        (hNewLengthSuccessor length).mpr
          (Or.inr fun _ => Iff.rfl)
      have hPreviousOld :=
        Structure.pairMember_old_of_append
          hNewLengthOrdinal hLengthNewLength
          hNewValuesPairs hPrevious
      have hPreviousEq :=
        hValues.1.2.1.2 length previous remainder
          hPreviousOld hFinal
      subst selectedExponent
      subst selectedCoefficient
      subst previous
      exact
        ⟨hQuotientNonempty,
          newLength, power, product, α,
          hNewLengthSuccessor, hPower, hRemainderPower,
          hPowerLeOrdinal,
          hProduct, hDecomposition, hPowerLeOrdinal,
          hNewFinal⟩
  exact
    ⟨newLength, newExponents, newCoefficients, newValues,
      hNewLengthOmega, hNewExponents, hNewCoefficients,
      newValueLength, hNewValueLengthSuccessor,
      hNewValuesOrdinal, hNewInitial, hNewFinal, hNewSteps⟩

/-- 每个序数都有一个对象层有限 Cantor 正规形。 -/
theorem cantorNormalForm_exists
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω α : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hα : ℳ.IsOrdinal α) :
    ∃ length exponents coefficients values,
      ℳ.IsCantorNormalForm 𝕀
        ω α length exponents coefficients values := by
  let env : Env ℳ 1 := {
    bound := fun _ => ω
    free := fun _ => Classical.choice ℳ.nonempty
  }
  let property : ℳ.Domain → Prop := fun current =>
    ∃ length exponents coefficients values,
      ℳ.IsCantorNormalForm 𝕀
        ω current length exponents coefficients values
  apply hα.induction property
  · rcases exists_separation hZF
        (Definitional.Project.UnarySchema.cantorNormalFormExistence 𝒞).neg
        env α with
      ⟨counterexamples, hCounterexamples⟩
    refine ⟨counterexamples, fun current => ?_⟩
    rw [hCounterexamples current]
    simp [Definitional.Project.UnarySchema.neg, property,
      Definitional.Project.Formula.satisfies_neg_iff,
      Definitional.Project.Formula.satisfies_cantorNormalFormExistence_iff
        𝕀 hZF.1 env current]
    intro _
    rfl
  · intro current hCurrent hPrevious
    by_cases hCurrentEmpty : ∀ value, ¬ ℳ.mem value current
    · exact exists_cantorNormalForm_of_empty
        hZF 𝕀 hω hCurrentEmpty
    · have hCurrentNonempty :
          ∃ value, ℳ.mem value current := by
        apply Classical.byContradiction
        intro hNoMember
        apply hCurrentEmpty
        intro value hValue
        exact hNoMember ⟨value, hValue⟩
      rcases ordinalExponentiation_exists_leadingExponent
          hZF 𝕀 hω hCurrent hCurrentNonempty with
        ⟨exponent, successor, power, successorPower,
          hExponent, hSuccessor, hPower, hSuccessorPower,
          hPowerLeCurrent, hCurrentSuccessorPower⟩
      have hωOrdinal := hω.isOrdinal hZF
      have hPowerOrdinal :=
        ordinalExponentiation_isOrdinal hZF 𝕀
          hωOrdinal hExponent hPower
      rcases hω.exists_ordinalOne_mem with
        ⟨one, _, hOneOmega⟩
      have hPowerNonempty :=
        ordinalExponentiation_isNonemptyOnOrdinals
          hZF 𝕀 hωOrdinal
          ⟨one, hOneOmega⟩ exponent hExponent power hPower
      rcases ordinalDivision_existsUnique_pair
          hZF 𝕀 hCurrent hPowerOrdinal
          hPowerNonempty with
        ⟨quotient, remainder, hDivision, _⟩
      have hRemainderPower := hDivision.2.1
      have hRemainderCurrent :
          ℳ.mem remainder current := by
        rcases hPowerLeCurrent with hPowerEq | hPowerCurrent
        · simpa [hPowerEq] using hRemainderPower
        · exact hCurrent.transitive
            power hPowerCurrent remainder hRemainderPower
      rcases hPrevious remainder hRemainderCurrent with
        ⟨length, exponents, coefficients, values,
          hRemainderForm⟩
      exact exists_cantorNormalForm_of_remainder
        hZF 𝕀 hω hRemainderForm
        hExponent hSuccessor hPower hSuccessorPower
        hPowerLeCurrent hCurrentSuccessorPower hDivision

/-- 同一序数的两套同上界 Cantor 正规形完全相等。 -/
theorem cantorNormalFormBelow_unique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω α : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hα : ℳ.IsOrdinal α)
    {bound
      firstLength firstExponents firstCoefficients firstValues
      secondLength secondExponents secondCoefficients secondValues :
        ℳ.Domain}
    (hFirst :
      ℳ.IsCantorNormalFormBelow 𝕀
        ω bound α firstLength
        firstExponents firstCoefficients firstValues)
    (hSecond :
      ℳ.IsCantorNormalFormBelow 𝕀
        ω bound α secondLength
        secondExponents secondCoefficients secondValues) :
    firstLength = secondLength ∧
      firstExponents = secondExponents ∧
      firstCoefficients = secondCoefficients ∧
      firstValues = secondValues := by
  let env : Env ℳ 1 := {
    bound := fun _ => ω
    free := fun _ => Classical.choice ℳ.nonempty
  }
  let property : ℳ.Domain → Prop := fun current =>
    ∀ bound
        firstLength firstExponents firstCoefficients firstValues
        secondLength secondExponents secondCoefficients secondValues,
      (ℳ.IsCantorNormalFormBelow 𝕀
          ω bound current firstLength
          firstExponents firstCoefficients firstValues ∧
        ℳ.IsCantorNormalFormBelow 𝕀
          ω bound current secondLength
          secondExponents secondCoefficients secondValues) →
        firstLength = secondLength ∧
          firstExponents = secondExponents ∧
          firstCoefficients = secondCoefficients ∧
          firstValues = secondValues
  have hProperty : property α := by
    apply hα.induction property
    · rcases exists_separation hZF
          (Definitional.Project.UnarySchema.cantorNormalFormBelowUniqueness
            𝒞).neg env α with
        ⟨counterexamples, hCounterexamples⟩
      refine ⟨counterexamples, fun current => ?_⟩
      rw [hCounterexamples current]
      simp [Definitional.Project.UnarySchema.neg, property,
        Definitional.Project.Formula.satisfies_neg_iff,
        Definitional.Project.Formula.satisfies_cantorNormalFormBelowUniqueness_iff
          𝕀 hZF.1 env current]
      intro _
      rfl
    · intro current hCurrent hPrevious
      intro currentBound
          firstLength firstExponents firstCoefficients firstValues
          secondLength secondExponents secondCoefficients secondValues
      rintro ⟨hCurrentFirst, hCurrentSecond⟩
      by_cases hCurrentEmpty :
          ∀ member, ¬ ℳ.mem member current
      · exact cantorNormalFormBelow_unique_of_ordinal_empty
          hZF 𝕀 hω hCurrentEmpty
          hCurrentFirst hCurrentSecond
      · have hCurrentNonempty :
            ∃ member, ℳ.mem member current := by
          apply Classical.byContradiction
          intro hNoMember
          apply hCurrentEmpty
          intro member hMember
          exact hNoMember ⟨member, hMember⟩
        rcases cantorNormalFormBelow_exists_prefix
            hZF 𝕀 hω hCurrentNonempty
            hCurrentFirst with
          ⟨firstPreviousLength,
            firstExponent, firstCoefficient, firstPrevious,
            firstPower, firstSuccessor, firstSuccessorPower,
            firstPreviousExponents,
            firstPreviousCoefficients, firstPreviousValues,
            _, hFirstLengthSuccessor,
            hFirstExponentValue, hFirstCoefficientValue,
            hFirstPreviousValue,
            hFirstExponent, _, _, hFirstPower, hFirstDivision,
            hFirstSuccessor, hFirstSuccessorPower,
            hFirstPowerLeCurrent, hCurrentFirstSuccessorPower,
            hFirstExponentsRestriction,
            hFirstCoefficientsRestriction,
            hFirstValuesRestriction, hFirstPreviousForm⟩
        rcases cantorNormalFormBelow_exists_prefix
            hZF 𝕀 hω hCurrentNonempty
            hCurrentSecond with
          ⟨secondPreviousLength,
            secondExponent, secondCoefficient, secondPrevious,
            secondPower, secondSuccessor, secondSuccessorPower,
            secondPreviousExponents,
            secondPreviousCoefficients, secondPreviousValues,
            _, hSecondLengthSuccessor,
            hSecondExponentValue, hSecondCoefficientValue,
            hSecondPreviousValue,
            hSecondExponent, _, _, hSecondPower, hSecondDivision,
            hSecondSuccessor, hSecondSuccessorPower,
            hSecondPowerLeCurrent, hCurrentSecondSuccessorPower,
            hSecondExponentsRestriction,
            hSecondCoefficientsRestriction,
            hSecondValuesRestriction, hSecondPreviousForm⟩
        have hExponentEq : firstExponent = secondExponent :=
          ordinalExponentiation_leadingExponent_unique
            hZF 𝕀 hω
            hFirstExponent hFirstSuccessor
            hFirstPower hFirstSuccessorPower
            hFirstPowerLeCurrent hCurrentFirstSuccessorPower
            hSecondExponent hSecondSuccessor
            hSecondPower hSecondSuccessorPower
            hSecondPowerLeCurrent hCurrentSecondSuccessorPower
        subst secondExponent
        have hωOrdinal := hω.isOrdinal hZF
        have hPowerEq : firstPower = secondPower := by
          rcases ordinalExponentiation_existsUnique hZF
              𝕀 hωOrdinal hFirstExponent with
            ⟨_, _, hUniquePower⟩
          exact
            (hUniquePower firstPower hFirstPower).trans
              (hUniquePower secondPower hSecondPower).symm
        subst secondPower
        have hPowerOrdinal :=
          ordinalExponentiation_isOrdinal hZF 𝕀
            hωOrdinal hFirstExponent hFirstPower
        rcases hω.exists_ordinalOne_mem with
          ⟨one, _, hOneOmega⟩
        have hPowerNonempty :=
          ordinalExponentiation_isNonemptyOnOrdinals
            hZF 𝕀 hωOrdinal
            ⟨one, hOneOmega⟩
            firstExponent hFirstExponent firstPower hFirstPower
        rcases ordinalDivision_existsUnique_pair
            hZF 𝕀 hCurrent
            hPowerOrdinal hPowerNonempty with
          ⟨_, _, _, hUniqueDivision⟩
        have hFirstCoordinates :=
          hUniqueDivision
            firstCoefficient firstPrevious hFirstDivision
        have hSecondCoordinates :=
          hUniqueDivision
            secondCoefficient secondPrevious hSecondDivision
        have hCoefficientEq :
            firstCoefficient = secondCoefficient :=
          hFirstCoordinates.1.trans hSecondCoordinates.1.symm
        have hPreviousEq :
            firstPrevious = secondPrevious :=
          hFirstCoordinates.2.trans hSecondCoordinates.2.symm
        subst secondCoefficient
        subst secondPrevious
        have hPreviousCurrent :
            ℳ.mem firstPrevious current := by
          have hPreviousPower := hFirstDivision.2.1
          rcases hFirstPowerLeCurrent with hEqual | hMember
          · simpa [hEqual] using hPreviousPower
          · exact hCurrent.transitive
              firstPower hMember firstPrevious hPreviousPower
        have hPreviousFormsEq :=
          hPrevious firstPrevious hPreviousCurrent
            currentBound
            firstPreviousLength
            firstPreviousExponents
            firstPreviousCoefficients firstPreviousValues
            secondPreviousLength
            secondPreviousExponents
            secondPreviousCoefficients secondPreviousValues
            ⟨hFirstPreviousForm, hSecondPreviousForm⟩
        rcases hPreviousFormsEq with
          ⟨hPreviousLengthEq,
            hPreviousExponentsEq,
            hPreviousCoefficientsEq,
            hPreviousValuesEq⟩
        subst secondPreviousLength
        have hLengthEq : firstLength = secondLength :=
          Structure.SuccessorOf.eq hZF.1
            hFirstLengthSuccessor hSecondLengthSuccessor
        subst secondLength
        rcases hCurrentFirst with
          ⟨_, hFirstExponents, hFirstCoefficients,
            firstValueLength, hFirstValueLengthSuccessor,
            hFirstValues, _, hFirstFinal, _⟩
        rcases hCurrentSecond with
          ⟨_, hSecondExponents, hSecondCoefficients,
            secondValueLength, hSecondValueLengthSuccessor,
            hSecondValues, _, hSecondFinal, _⟩
        have hExponentsEq : firstExponents = secondExponents :=
          Structure.IsSequenceOfLength.eq_of_restriction_eq_of_last
            hZF.1
            hFirstExponents.1.1 hSecondExponents.1.1
            hFirstLengthSuccessor hSecondLengthSuccessor
            hFirstExponentsRestriction
            hSecondExponentsRestriction
            hPreviousExponentsEq
            hFirstExponentValue hSecondExponentValue
        let firstCoefficientSequence :
            ℳ.IsSequenceOfLength 𝕀
              firstCoefficients firstLength :=
          ⟨hFirstCoefficients.1, hFirstCoefficients.2.1,
            hFirstCoefficients.2.2.1⟩
        let secondCoefficientSequence :
            ℳ.IsSequenceOfLength 𝕀
              secondCoefficients firstLength :=
          ⟨hSecondCoefficients.1, hSecondCoefficients.2.1,
            hSecondCoefficients.2.2.1⟩
        have hCoefficientsEq :
            firstCoefficients = secondCoefficients :=
          Structure.IsSequenceOfLength.eq_of_restriction_eq_of_last
            hZF.1
            firstCoefficientSequence secondCoefficientSequence
            hFirstLengthSuccessor hSecondLengthSuccessor
            hFirstCoefficientsRestriction
            hSecondCoefficientsRestriction
            hPreviousCoefficientsEq
            hFirstCoefficientValue hSecondCoefficientValue
        have hValuesEq : firstValues = secondValues :=
          Structure.IsSequenceOfLength.eq_of_restriction_eq_of_last
            hZF.1
            hFirstValues.1 hSecondValues.1
            hFirstValueLengthSuccessor
            hSecondValueLengthSuccessor
            hFirstValuesRestriction hSecondValuesRestriction
            hPreviousValuesEq hFirstFinal hSecondFinal
        exact ⟨rfl, hExponentsEq, hCoefficientsEq, hValuesEq⟩
  exact
    hProperty bound
      firstLength firstExponents firstCoefficients firstValues
      secondLength secondExponents secondCoefficients secondValues
      ⟨hFirst, hSecond⟩

/-- 同一序数的两套普通 Cantor 正规形完全相等。 -/
theorem cantorNormalForm_unique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω α : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hα : ℳ.IsOrdinal α)
    {firstLength firstExponents firstCoefficients firstValues
      secondLength secondExponents secondCoefficients secondValues :
        ℳ.Domain}
    (hFirst :
      ℳ.IsCantorNormalForm 𝕀
        ω α firstLength
        firstExponents firstCoefficients firstValues)
    (hSecond :
      ℳ.IsCantorNormalForm 𝕀
        ω α secondLength
        secondExponents secondCoefficients secondValues) :
    firstLength = secondLength ∧
      firstExponents = secondExponents ∧
      firstCoefficients = secondCoefficients ∧
      firstValues = secondValues :=
  cantorNormalFormBelow_unique
    hZF 𝕀 hω hα hFirst hSecond

/-- 有界 Cantor 正规形中的每个系数都非空。 -/
theorem cantorNormalFormBelow_coefficient_nonempty
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω bound α length exponents coefficients values
      index coefficient : ℳ.Domain}
    (hForm :
      ℳ.IsCantorNormalFormBelow 𝕀
        ω bound α length exponents coefficients values)
    (hIndex : ℳ.mem index length)
    (hCoefficient :
      ℳ.PairMember 𝕀 index coefficient coefficients) :
    ∃ member, ℳ.mem member coefficient := by
  rcases hForm with
    ⟨_, hExponents, _, valueLength,
      hValueLengthSuccessor, hValues, _, _, hSteps⟩
  rcases (hExponents.1.1.2.2 index).mp hIndex with
    ⟨exponent, hExponent⟩
  have hLengthValueLength :
      ℳ.mem length valueLength :=
    (hValueLengthSuccessor length).mpr
      (Or.inr fun _ => Iff.rfl)
  have hIndexValueLength :
      ℳ.mem index valueLength :=
    hValues.1.1.transitive
      length hLengthValueLength index hIndex
  rcases (hValues.1.2.2 index).mp hIndexValueLength with
    ⟨previous, hPrevious⟩
  exact
    (hSteps index hIndex exponent coefficient previous
      hExponent hCoefficient hPrevious).1

/-- 每个序数都具有唯一的对象层有限 Cantor 正规形。 -/
theorem cantorNormalForm_existsUnique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω α : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hα : ℳ.IsOrdinal α) :
    ∃ length exponents coefficients values,
      ℳ.IsCantorNormalForm 𝕀
          ω α length exponents coefficients values ∧
        ∀ otherLength otherExponents otherCoefficients otherValues,
          ℳ.IsCantorNormalForm 𝕀
              ω α otherLength
              otherExponents otherCoefficients otherValues →
            otherLength = length ∧
              otherExponents = exponents ∧
              otherCoefficients = coefficients ∧
              otherValues = values := by
  rcases cantorNormalForm_exists
      hZF 𝕀 hω hα with
    ⟨length, exponents, coefficients, values, hForm⟩
  refine
    ⟨length, exponents, coefficients, values, hForm, ?_⟩
  intro otherLength otherExponents otherCoefficients otherValues
      hOther
  exact cantorNormalForm_unique
    hZF 𝕀 hω hα hOther hForm

/--
每个非零序数都具有唯一的有限 Cantor 正规形。

内部指数序列按低到高严格递增，因此反向读取即文献中的严格降序；每个系数都属于
`ω` 且非零。
-/
theorem cantorNormalForm_existsUnique_of_nonempty
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω α : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hα : ℳ.IsOrdinal α)
    (hαNonempty : ∃ member, ℳ.mem member α) :
    ∃ length exponents coefficients values,
      ℳ.IsCantorNormalForm 𝕀
          ω α length exponents coefficients values ∧
        (∃ index, ℳ.mem index length) ∧
        (∀ index, ℳ.mem index length →
          ∃ exponent coefficient,
            ℳ.PairMember 𝕀 index exponent exponents ∧
              ℳ.IsOrdinal exponent ∧
              ℳ.PairMember 𝕀
                index coefficient coefficients ∧
              ℳ.mem coefficient ω ∧
              ∃ member, ℳ.mem member coefficient) ∧
        ∀ otherLength otherExponents otherCoefficients otherValues,
          ℳ.IsCantorNormalForm 𝕀
              ω α otherLength
              otherExponents otherCoefficients otherValues →
            otherLength = length ∧
              otherExponents = exponents ∧
              otherCoefficients = coefficients ∧
              otherValues = values := by
  rcases cantorNormalForm_existsUnique
      hZF 𝕀 hω hα with
    ⟨length, exponents, coefficients, values,
      hForm, hUnique⟩
  have hLengthNonempty :=
    cantorNormalForm_length_nonempty
      hZF hαNonempty hForm
  have hForm' := hForm
  rcases hForm with
    ⟨_, hExponents, hCoefficients, _, _, _, _, _, _⟩
  refine
    ⟨length, exponents, coefficients, values,
      hForm', hLengthNonempty, ?_, hUnique⟩
  intro index hIndex
  rcases (hExponents.1.1.2.2 index).mp hIndex with
    ⟨exponent, hExponentValue⟩
  rcases hCoefficients.2.2.2 index hIndex with
    ⟨coefficient, hCoefficientOmega, hCoefficientValue⟩
  exact
    ⟨exponent, coefficient,
      hExponentValue,
      hExponents.1.2 index hIndex exponent hExponentValue,
      hCoefficientValue, hCoefficientOmega,
      cantorNormalFormBelow_coefficient_nonempty
        hForm' hIndex hCoefficientValue⟩

end ZF

end SetTheory
end YesMetaZFC
