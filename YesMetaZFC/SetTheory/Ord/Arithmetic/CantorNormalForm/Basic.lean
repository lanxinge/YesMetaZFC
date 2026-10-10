import YesMetaZFC.SetTheory.Ord.Arithmetic.Comparison
import YesMetaZFC.SetTheory.Ord.Natural
/-!
# Cantor 正规形的公式与基础语义
固定有限展开的索引、系数、部分值及首指数上界，给出对象公式与结构语义的对应。
序列追加的两个基础投影供后续存在性和唯一性证明复用。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Structure
/-- Cantor 正规形在一个索引处的递推方程。 -/
def IsCantorNormalFormStep {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (ω α exponents coefficients values index : ℳ.Domain) :
    Prop :=
  ∀ exponent coefficient previous,
    ℳ.PairMember 𝕀 index exponent exponents →
    ℳ.PairMember 𝕀 index coefficient coefficients →
    ℳ.PairMember 𝕀 index previous values → (∃ member, ℳ.mem member coefficient) ∧
        ∃ next power monomial output,
          ℳ.SuccessorOf next index ∧
          ℳ.IsOrdinalExponentiation 𝕀
            power ω exponent ∧
          ℳ.mem previous power ∧ (power = α ∨ ℳ.mem power α) ∧
          ℳ.IsOrdinalMultiplication 𝕀
            monomial power coefficient ∧
          ℳ.IsOrdinalAddition 𝕀
            output monomial previous ∧ (power = output ∨ ℳ.mem power output) ∧
          ℳ.PairMember 𝕀 next output values
/--
带环境上界的对象层有限 Cantor 正规形。
指数按从低到高的顺序存储，使归纳构造可以在末尾追加新的首项；`values` 在索引
`0` 处取 `0`，并在每个后继位置保存加入当前单项式后的部分值。
-/
def IsCantorNormalFormBelow {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (ω bound α length exponents coefficients values : ℳ.Domain) :
    Prop :=
  ℳ.mem length ω ∧
    ℳ.IsIncreasingOrdinalSequence 𝕀 exponents length ∧
    ℳ.IsSequenceIn 𝕀 coefficients length ω ∧
    ∃ valueLength,
      ℳ.SuccessorOf valueLength length ∧
      ℳ.IsOrdinalValuedSequence 𝕀 values valueLength ∧ (∃ zero, (∀ member, ¬ ℳ.mem member zero) ∧
        ℳ.PairMember 𝕀 zero zero values) ∧
      ℳ.PairMember 𝕀 length α values ∧
      ∀ index, ℳ.mem index length →
        ℳ.IsCantorNormalFormStep 𝕀
          ω bound exponents coefficients values index
/-- 环境上界取表示值本身时，得到普通对象层有限 Cantor 正规形。 -/
def IsCantorNormalForm {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (ω α length exponents coefficients values : ℳ.Domain) :
    Prop :=
  ℳ.IsCantorNormalFormBelow 𝕀
    ω α α length exponents coefficients values
/-- 序列追加后，旧定义域中的坐标仍只能来自旧序列。 -/
theorem pairMember_old_of_append {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence appended length appendedValue index value : ℳ.Domain} (hLength : ℳ.IsOrdinal length) (hIndex : ℳ.mem index length) (hPairs : ∀ input output,
      ℳ.PairMember 𝕀 input output appended ↔
        ℳ.PairMember 𝕀 input output sequence ∨ (input = length ∧ output = appendedValue)) (hValue :
      ℳ.PairMember 𝕀 index value appended) :
    ℳ.PairMember 𝕀 index value sequence := by
  rcases (hPairs index value).mp hValue with hOld | ⟨hIndexEq, _⟩
  · exact hOld
  · subst index
    exact False.elim <|
      hLength.wellOrder.linear.irrefl length hIndex hIndex
/-- 序列追加后，新末索引上的坐标值等于追加值。 -/
theorem pairMember_new_eq_of_append {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {sequence appended length appendedValue value : ℳ.Domain} (hSequence :
      ℳ.IsSequenceOfLength 𝕀 sequence length) (hPairs : ∀ input output,
      ℳ.PairMember 𝕀 input output appended ↔
        ℳ.PairMember 𝕀 input output sequence ∨ (input = length ∧ output = appendedValue)) (hValue :
      ℳ.PairMember 𝕀 length value appended) :
    value = appendedValue := by
  rcases (hPairs length value).mp hValue with hOld | ⟨_, hValueEq⟩
  · have hLengthMember : ℳ.mem length length :=
      (hSequence.2.2 length).mpr ⟨value, hOld⟩
    exact False.elim <|
      hSequence.1.wellOrder.linear.irrefl length
        hLengthMember hLengthMember
  · exact hValueEq
end Structure
namespace Definitional
namespace Project
namespace Formula
/-- Cantor 正规形在给定索引处的对象语言递推方程。 -/
def isCantorNormalFormStep (𝒞 : OrderedPairConvention)
    {depth : Nat} (ω α exponents coefficients values index : Term depth) :
    Formula 1 depth :=
  .forallE <| .forallE <| .forallE <| .imp (.conj (orderedPairMem 𝒞 index.weaken.weaken.weaken (.bound 2) exponents.weaken.weaken.weaken) <|
      .conj (orderedPairMem 𝒞 index.weaken.weaken.weaken (.bound 1) coefficients.weaken.weaken.weaken) (orderedPairMem 𝒞 index.weaken.weaken.weaken
          Term.newest values.weaken.weaken.weaken)) <|
    .conj (.neg <| isEmpty (.bound 1)) <|
      .existsE <| .conj (isSuccessor Term.newest index.weaken.weaken.weaken.weaken) <|
        .existsE <| .conj (isOrdinalExponentiation 𝒞 Term.newest
            ω.weaken.weaken.weaken.weaken.weaken (.bound 4)) <|
          .conj (.mem (.bound 2) Term.newest) <|
          .conj (.disj (extensionalEq Term.newest
                α.weaken.weaken.weaken.weaken.weaken) (.mem Term.newest
                α.weaken.weaken.weaken.weaken.weaken)) <|
            .existsE <| .conj (isOrdinalMultiplication 𝒞 Term.newest (.bound 1) (.bound 4)) <|
              .existsE <| .conj (isOrdinalAddition 𝒞 Term.newest (.bound 1) (.bound 4)) (.conj (.disj (extensionalEq (.bound 2) Term.newest)
                    (.mem (.bound 2) Term.newest)) (orderedPairMem 𝒞 (.bound 3) Term.newest
                    values.weaken.weaken.weaken.weaken.weaken.weaken.weaken))
derive_free_closed isCantorNormalFormStep
/-- 带环境上界的对象层有限 Cantor 正规形。 -/
def isCantorNormalFormBelow (𝒞 : OrderedPairConvention)
    {depth : Nat} (ω bound α length exponents coefficients values : Term depth) :
    Formula 1 depth :=
  .conj (.mem length ω) <|
    .conj (isIncreasingOrdinalSequence 𝒞 exponents length) <|
    .conj (isSequenceIn 𝒞 coefficients length ω) <|
    .existsE <| .conj (isSuccessor Term.newest length.weaken) <|
    .conj (isOrdinalValuedSequence 𝒞 values.weaken Term.newest) <|
    .conj (.existsE <| .conj (isEmpty Term.newest) (orderedPairMem 𝒞 Term.newest Term.newest
          values.weaken.weaken)) <|
    .conj (orderedPairMem 𝒞 length.weaken α.weaken
        values.weaken) <|
      forallMem length.weaken <|
        isCantorNormalFormStep 𝒞
          ω.weaken.weaken bound.weaken.weaken
          exponents.weaken.weaken coefficients.weaken.weaken
          values.weaken.weaken Term.newest
derive_free_closed isCantorNormalFormBelow
/-- 环境上界取表示值本身时，得到普通对象层有限 Cantor 正规形。 -/
def isCantorNormalForm (𝒞 : OrderedPairConvention)
    {depth : Nat} (ω α length exponents coefficients values : Term depth) :
    Formula 1 depth :=
  isCantorNormalFormBelow 𝒞
    ω α α length exponents coefficients values
derive_free_closed isCantorNormalForm
/-- 单个正规形递推步骤的公式语义。 -/

theorem satisfies_isCantorNormalFormStep_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (ω α exponents coefficients values index : Term depth) :
    satisfies env (isCantorNormalFormStep 𝒞
          ω α exponents coefficients values index) ↔
      ℳ.IsCantorNormalFormStep 𝕀 (ω.eval env) (α.eval env) (exponents.eval env) (coefficients.eval env) (values.eval env) (index.eval env) := by
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

theorem satisfies_isCantorNormalFormBelow_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (ω bound α length exponents coefficients values : Term depth) :
    satisfies env (isCantorNormalFormBelow 𝒞
          ω bound α length exponents coefficients values) ↔
      ℳ.IsCantorNormalFormBelow 𝕀 (ω.eval env) (bound.eval env) (α.eval env) (length.eval env) (exponents.eval env) (coefficients.eval env)
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

theorem satisfies_isCantorNormalForm_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ) (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (ω α length exponents coefficients values : Term depth) :
    satisfies env (isCantorNormalForm 𝒞
          ω α length exponents coefficients values) ↔
      ℳ.IsCantorNormalForm 𝕀 (ω.eval env) (α.eval env) (length.eval env) (exponents.eval env) (coefficients.eval env) (values.eval env) := by
  simp [isCantorNormalForm, Structure.IsCantorNormalForm,
    satisfies_isCantorNormalFormBelow_iff 𝕀 hExt]
end Formula
end Project
end Definitional
end SetTheory
end YesMetaZFC
