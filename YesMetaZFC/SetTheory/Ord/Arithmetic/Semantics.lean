import YesMetaZFC.SetTheory.Ord.Arithmetic.Syntax
import YesMetaZFC.SetTheory.Ord.Normal

/-!
# 序数算术的纸面语义

本层把 `Arithmetic.Syntax` 中的公式定义解释为普通 Lean 谓词。算术仍保持关系式接口：
后续存在唯一性定理将证明这些关系在序数参数上给出总函数。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- `sequence` 是定义域为空序数的超限序列。 -/
def IsZeroLengthSequence {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sequence : ℳ.Domain) : Prop :=
  ∃ zero,
    ℳ.IsSequenceOfLength 𝕀 sequence zero ∧
      ∀ value, ¬ ℳ.mem value zero

/-- `sequence` 的定义域是后继序数，且 `last` 是最后一个值。 -/
def IsSuccessorLengthSequenceWithLast {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sequence last : ℳ.Domain) : Prop :=
  ∃ predecessor,
    ℳ.IsOrdinal predecessor ∧
      ∃ length,
        ℳ.SuccessorOf length predecessor ∧
          ℳ.IsSequenceOfLength 𝕀 sequence length ∧
            ℳ.PairMember 𝕀 predecessor last sequence

/-- `sequence` 的定义域是极限序数，且 `limit` 是其值域的并。 -/
def IsLimitLengthSequenceWithUnion {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sequence limit : ℳ.Domain) : Prop :=
  ∃ length,
    ℳ.IsLimitOrdinal length ∧
      ℳ.IsSequenceOfLength 𝕀 sequence length ∧
        ∃ range,
          ℳ.IsRangeOf 𝕀 range sequence ∧
            ℳ.IsUnionOf limit range

/-- `one` 是某个空集的后继。 -/
def IsOrdinalOne (ℳ : Structure.{u}) (one : ℳ.Domain) : Prop :=
  ∃ zero,
    (∀ value, ¬ ℳ.mem value zero) ∧
      ℳ.SuccessorOf one zero

/-- 固定左参数的序数加法递归阶段。 -/
def IsOrdinalAdditionStep {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left sequence output : ℳ.Domain) : Prop :=
  (ℳ.IsZeroLengthSequence 𝕀 sequence ∧ output = left) ∨
    (∃ last,
      ℳ.IsSuccessorLengthSequenceWithLast 𝕀 sequence last ∧
        ℳ.SuccessorOf output last) ∨
    ℳ.IsLimitLengthSequenceWithUnion 𝕀 sequence output

/-- `sum` 是 `left + right` 的超限递归值。 -/
def IsOrdinalAddition {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sum left right : ℳ.Domain) : Prop :=
  ℳ.IsRecursionValue 𝕀
    (ℳ.IsOrdinalAdditionStep 𝕀 left) right sum

/--
固定左参数的序数乘法递归阶段。

序数左参数使用文献递归；非序数左参数的空集分支只用于满足递归内核的全定义合同。
-/
def IsOrdinalMultiplicationStep {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (left sequence output : ℳ.Domain) : Prop :=
  (¬ ℳ.IsOrdinal left ∧
      ∀ value, ¬ ℳ.mem value output) ∨
    (ℳ.IsOrdinal left ∧
      ((ℳ.IsZeroLengthSequence 𝕀 sequence ∧
          ∀ value, ¬ ℳ.mem value output) ∨
        (∃ last,
          ℳ.IsSuccessorLengthSequenceWithLast 𝕀
              sequence last ∧
            ℳ.IsOrdinalAddition 𝕀 output last left) ∨
        ℳ.IsLimitLengthSequenceWithUnion 𝕀
          sequence output))

/-- `product` 是 `left * right` 的超限递归值。 -/
def IsOrdinalMultiplication {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (product left right : ℳ.Domain) : Prop :=
  ℳ.IsRecursionValue 𝕀
    (ℳ.IsOrdinalMultiplicationStep 𝕀 left) right product

/-- 固定底数的序数幂递归阶段。 -/
def IsOrdinalExponentiationStep {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (base sequence output : ℳ.Domain) : Prop :=
  (ℳ.IsZeroLengthSequence 𝕀 sequence ∧
      ℳ.IsOrdinalOne output) ∨
    (∃ last,
      ℳ.IsSuccessorLengthSequenceWithLast 𝕀 sequence last ∧
        ℳ.IsOrdinalMultiplication 𝕀 output last base) ∨
    ℳ.IsLimitLengthSequenceWithUnion 𝕀 sequence output

/-- `power` 是 `base ^ exponent` 的超限递归值。 -/
def IsOrdinalExponentiation {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (power base exponent : ℳ.Domain) : Prop :=
  ℳ.IsRecursionValue 𝕀
    (ℳ.IsOrdinalExponentiationStep 𝕀 base) exponent power

/-- `dividend` 关于 `divisor` 的序数商余分解。 -/
def IsOrdinalDivision {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (dividend divisor quotient remainder : ℳ.Domain) : Prop :=
  ℳ.IsOrdinal quotient ∧ ℳ.mem remainder divisor ∧
    ∃ product,
      ℳ.IsOrdinalMultiplication 𝕀
          product divisor quotient ∧
        ℳ.IsOrdinalAddition 𝕀
          dividend product remainder

/-- `relation` 是 `carrier` 上的集合编码严格线序。 -/
def IsSetCodedLinearOrder {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (relation carrier : ℳ.Domain) : Prop :=
  ℳ.IsSetRelation 𝕀 relation ∧
    ((∀ value, ℳ.mem value carrier →
        ¬ ℳ.PairMember 𝕀 value value relation) ∧
      (∀ left, ℳ.mem left carrier →
        ∀ middle, ℳ.mem middle carrier →
          ∀ right, ℳ.mem right carrier →
            ℳ.PairMember 𝕀 left middle relation →
            ℳ.PairMember 𝕀 middle right relation →
              ℳ.PairMember 𝕀 left right relation)) ∧
      ∀ left, ℳ.mem left carrier →
        ∀ right, ℳ.mem right carrier →
          ℳ.SameMembers left right ∨
            ℳ.PairMember 𝕀 left right relation ∨
            ℳ.PairMember 𝕀 right left relation

/-- `sumRelation` 精确实现不相交线性序的序和关系。 -/
def IsLinearOrderSumRelation {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sumRelation leftCarrier leftRelation rightCarrier rightRelation :
      ℳ.Domain) : Prop :=
  ∀ left right,
    ℳ.PairMember 𝕀 left right sumRelation ↔
      (ℳ.mem left leftCarrier ∧ ℳ.mem right leftCarrier ∧
        ℳ.PairMember 𝕀 left right leftRelation) ∨
      (ℳ.mem left rightCarrier ∧ ℳ.mem right rightCarrier ∧
        ℳ.PairMember 𝕀 left right rightRelation) ∨
      (ℳ.mem left leftCarrier ∧ ℳ.mem right rightCarrier)

/-- `sumCarrier, sumRelation` 是两个不相交线性序的序和。 -/
def IsLinearOrderSum {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (sumCarrier sumRelation leftCarrier leftRelation
      rightCarrier rightRelation : ℳ.Domain) : Prop :=
  ℳ.IsSetCodedLinearOrder 𝕀 leftRelation leftCarrier ∧
    ℳ.IsSetCodedLinearOrder 𝕀 rightRelation rightCarrier ∧
    ℳ.IsDisjoint leftCarrier rightCarrier ∧
    ℳ.IsUnionOfTwo sumCarrier leftCarrier rightCarrier ∧
    ℳ.IsSetRelation 𝕀 sumRelation ∧
    ℳ.IsLinearOrderSumRelation 𝕀 sumRelation
      leftCarrier leftRelation rightCarrier rightRelation

/-- `productRelation` 精确实现第二坐标优先的右字典序。 -/
def IsRightLexicographicProductRelation {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (productRelation leftCarrier leftRelation
      rightCarrier rightRelation : ℳ.Domain) : Prop :=
  ∀ firstPair secondPair,
    ℳ.PairMember 𝕀 firstPair secondPair productRelation ↔
      ∃ firstLeft, ℳ.mem firstLeft leftCarrier ∧
        ∃ firstRight, ℳ.mem firstRight rightCarrier ∧
          ∃ secondLeft, ℳ.mem secondLeft leftCarrier ∧
            ∃ secondRight, ℳ.mem secondRight rightCarrier ∧
              𝕀.Codes firstPair firstLeft firstRight ∧
              𝕀.Codes secondPair secondLeft secondRight ∧
              (ℳ.PairMember 𝕀 firstRight secondRight
                  rightRelation ∨
                (ℳ.SameMembers firstRight secondRight ∧
                  ℳ.PairMember 𝕀 firstLeft secondLeft
                    leftRelation))

/-- `productCarrier, productRelation` 是两个线性序的右字典序积。 -/
def IsLinearOrderProduct {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (productCarrier productRelation leftCarrier leftRelation
      rightCarrier rightRelation : ℳ.Domain) : Prop :=
  ℳ.IsSetCodedLinearOrder 𝕀 leftRelation leftCarrier ∧
    ℳ.IsSetCodedLinearOrder 𝕀 rightRelation rightCarrier ∧
    ℳ.IsCartesianProduct 𝕀 productCarrier
      leftCarrier rightCarrier ∧
    ℳ.IsSetRelation 𝕀 productRelation ∧
    ℳ.IsRightLexicographicProductRelation 𝕀 productRelation
      leftCarrier leftRelation rightCarrier rightRelation

end Structure

namespace Definitional
namespace Project

namespace Formula

/-- 零长度序列公式与纸面语义一致。 -/
theorem satisfies_isZeroLengthSequence_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth) (sequence : Term depth) :
    satisfies env (isZeroLengthSequence 𝒞 sequence) ↔
      ℳ.IsZeroLengthSequence 𝕀 (sequence.eval env) := by
  simp only [isZeroLengthSequence, Structure.IsZeroLengthSequence,
    satisfies_exists_iff, satisfies_conj_iff,
    satisfies_isSequenceOfLength_iff 𝕀 hExt,
    satisfies_isEmpty_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 后继长度序列末值公式与纸面语义一致。 -/
theorem satisfies_isSuccessorLengthSequenceWithLast_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sequence last : Term depth) :
    satisfies env
        (isSuccessorLengthSequenceWithLast 𝒞 sequence last) ↔
      ℳ.IsSuccessorLengthSequenceWithLast 𝕀
        (sequence.eval env) (last.eval env) := by
  simp only [isSuccessorLengthSequenceWithLast,
    Structure.IsSuccessorLengthSequenceWithLast,
    satisfies_exists_iff, satisfies_conj_iff,
    satisfies_isOrdinal_iff,
    satisfies_isSuccessor_iff,
    satisfies_isSequenceOfLength_iff 𝕀 hExt,
    satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 极限长度序列并值公式与纸面语义一致。 -/
theorem satisfies_isLimitLengthSequenceWithUnion_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sequence limit : Term depth) :
    satisfies env
        (isLimitLengthSequenceWithUnion 𝒞 sequence limit) ↔
      ℳ.IsLimitLengthSequenceWithUnion 𝕀
        (sequence.eval env) (limit.eval env) := by
  simp only [isLimitLengthSequenceWithUnion,
    Structure.IsLimitLengthSequenceWithUnion,
    satisfies_exists_iff, satisfies_conj_iff,
    satisfies_isLimitOrdinal_iff,
    satisfies_isSequenceOfLength_iff 𝕀 hExt,
    satisfies_isRange_iff 𝕀,
    satisfies_isUnion_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 序数一公式与纸面语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isOrdinalOne_iff
    {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) (one : Term depth) :
    satisfies env (isOrdinalOne one) ↔
      ℳ.IsOrdinalOne (one.eval env) := by
  simp only [isOrdinalOne, Structure.IsOrdinalOne,
    satisfies_exists_iff, satisfies_conj_iff,
    satisfies_isEmpty_iff, satisfies_isSuccessor_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

end Formula

namespace BinarySchema

/-- 加法递归算子的 schema 解释与纸面三分支定义一致。 -/
theorem denote_ordinalAdditionOperator_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 1) (sequence output : ℳ.Domain) :
    (ordinalAdditionOperator 𝒞).denote
        env sequence output ↔
      ℳ.IsOrdinalAdditionStep 𝕀
        (env.bound 0) sequence output := by
  simp only [ordinalAdditionOperator, denote,
    Structure.IsOrdinalAdditionStep,
    Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff,
    Formula.satisfies_isZeroLengthSequence_iff 𝕀 hExt,
    Formula.satisfies_extensionalEq_iff_eq hExt,
    Formula.satisfies_isSuccessorLengthSequenceWithLast_iff
      𝕀 hExt,
    Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_isLimitLengthSequenceWithUnion_iff
      𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Definitional.Term.eval_newest]
  rfl

/-- 加法类关系的 schema 解释与纸面加法关系一致。 -/
theorem denote_ordinalAddition_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 1) (right sum : ℳ.Domain) :
    (ordinalAddition 𝒞).denote env right sum ↔
      ℳ.IsOrdinalAddition 𝕀 sum (env.bound 0) right := by
  have hOperator :
      (ordinalAdditionOperator 𝒞).denote env =
        ℳ.IsOrdinalAdditionStep 𝕀 (env.bound 0) := by
    funext sequence output
    apply propext
    exact
      denote_ordinalAdditionOperator_iff 𝕀 hExt
        env sequence output
  rw [ordinalAddition]
  rw [Formula.denote_transfiniteRecursion_iff
    𝕀 hExt env (ordinalAdditionOperator 𝒞)
    right sum]
  rw [hOperator]
  rfl

end BinarySchema

namespace Formula

/-- 序数加法公式与纸面递归关系一致。 -/
theorem satisfies_isOrdinalAddition_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sum left right : Term depth) :
    satisfies env (isOrdinalAddition 𝒞 sum left right) ↔
      ℳ.IsOrdinalAddition 𝕀
        (sum.eval env) (left.eval env) (right.eval env) := by
  rw [isOrdinalAddition, satisfies_related_iff]
  simpa [TermVector.evalEnv, TermVector.singleton] using
    BinarySchema.denote_ordinalAddition_iff 𝕀 hExt
      ((TermVector.singleton left).evalEnv env)
      (right.eval env) (sum.eval env)

end Formula

namespace BinarySchema

/-- 乘法递归算子的 schema 解释与纸面三分支定义一致。 -/
theorem denote_ordinalMultiplicationOperator_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 1) (sequence output : ℳ.Domain) :
    (ordinalMultiplicationOperator 𝒞).denote
        env sequence output ↔
      ℳ.IsOrdinalMultiplicationStep 𝕀
        (env.bound 0) sequence output := by
  simp only [ordinalMultiplicationOperator, denote,
    Structure.IsOrdinalMultiplicationStep,
    Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_isZeroLengthSequence_iff 𝕀 hExt,
    Formula.satisfies_isEmpty_iff,
    Formula.satisfies_isSuccessorLengthSequenceWithLast_iff
      𝕀 hExt,
    Formula.satisfies_isOrdinalAddition_iff 𝕀 hExt,
    Formula.satisfies_isLimitLengthSequenceWithUnion_iff
      𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Definitional.Term.eval_newest]
  rfl

/-- 乘法类关系的 schema 解释与纸面乘法关系一致。 -/
theorem denote_ordinalMultiplication_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 1) (right product : ℳ.Domain) :
    (ordinalMultiplication 𝒞).denote env right product ↔
      ℳ.IsOrdinalMultiplication 𝕀
        product (env.bound 0) right := by
  have hOperator :
      (ordinalMultiplicationOperator 𝒞).denote env =
        ℳ.IsOrdinalMultiplicationStep 𝕀 (env.bound 0) := by
    funext sequence output
    apply propext
    exact
      denote_ordinalMultiplicationOperator_iff 𝕀 hExt
        env sequence output
  rw [ordinalMultiplication]
  rw [Formula.denote_transfiniteRecursion_iff
    𝕀 hExt env
    (ordinalMultiplicationOperator 𝒞) right product]
  rw [hOperator]
  rfl

end BinarySchema

namespace Formula

/-- 序数乘法公式与纸面递归关系一致。 -/
theorem satisfies_isOrdinalMultiplication_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (product left right : Term depth) :
    satisfies env
        (isOrdinalMultiplication 𝒞 product left right) ↔
      ℳ.IsOrdinalMultiplication 𝕀
        (product.eval env) (left.eval env) (right.eval env) := by
  rw [isOrdinalMultiplication, satisfies_related_iff]
  simpa [TermVector.evalEnv, TermVector.singleton] using
    BinarySchema.denote_ordinalMultiplication_iff
      𝕀 hExt ((TermVector.singleton left).evalEnv env)
      (right.eval env) (product.eval env)

end Formula

namespace BinarySchema

/-- 幂递归算子的 schema 解释与纸面三分支定义一致。 -/
theorem denote_ordinalExponentiationOperator_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 1) (sequence output : ℳ.Domain) :
    (ordinalExponentiationOperator 𝒞).denote
        env sequence output ↔
      ℳ.IsOrdinalExponentiationStep 𝕀
        (env.bound 0) sequence output := by
  simp only [ordinalExponentiationOperator, denote,
    Structure.IsOrdinalExponentiationStep,
    Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff,
    Formula.satisfies_isZeroLengthSequence_iff 𝕀 hExt,
    Formula.satisfies_isOrdinalOne_iff,
    Formula.satisfies_isSuccessorLengthSequenceWithLast_iff
      𝕀 hExt,
    Formula.satisfies_isOrdinalMultiplication_iff
      𝕀 hExt,
    Formula.satisfies_isLimitLengthSequenceWithUnion_iff
      𝕀 hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Definitional.Term.eval_newest]
  rfl

/-- 幂类关系的 schema 解释与纸面幂关系一致。 -/
theorem denote_ordinalExponentiation_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 1) (exponent power : ℳ.Domain) :
    (ordinalExponentiation 𝒞).denote env exponent power ↔
      ℳ.IsOrdinalExponentiation 𝕀
        power (env.bound 0) exponent := by
  have hOperator :
      (ordinalExponentiationOperator 𝒞).denote env =
        ℳ.IsOrdinalExponentiationStep 𝕀 (env.bound 0) := by
    funext sequence output
    apply propext
    exact
      denote_ordinalExponentiationOperator_iff 𝕀 hExt
        env sequence output
  rw [ordinalExponentiation]
  rw [Formula.denote_transfiniteRecursion_iff
    𝕀 hExt env
    (ordinalExponentiationOperator 𝒞) exponent power]
  rw [hOperator]
  rfl

end BinarySchema

namespace Formula

/-- 序数幂公式与纸面递归关系一致。 -/
theorem satisfies_isOrdinalExponentiation_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (power base exponent : Term depth) :
    satisfies env
        (isOrdinalExponentiation 𝒞 power base exponent) ↔
      ℳ.IsOrdinalExponentiation 𝕀
        (power.eval env) (base.eval env) (exponent.eval env) := by
  rw [isOrdinalExponentiation, satisfies_related_iff]
  simpa [TermVector.evalEnv, TermVector.singleton] using
    BinarySchema.denote_ordinalExponentiation_iff
      𝕀 hExt ((TermVector.singleton base).evalEnv env)
      (exponent.eval env) (power.eval env)

/-- 序数商余公式与纸面商余关系一致。 -/
theorem satisfies_isOrdinalDivision_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (dividend divisor quotient remainder : Term depth) :
    satisfies env
        (isOrdinalDivision 𝒞
          dividend divisor quotient remainder) ↔
      ℳ.IsOrdinalDivision 𝕀
        (dividend.eval env) (divisor.eval env)
        (quotient.eval env) (remainder.eval env) := by
  simp only [isOrdinalDivision, Structure.IsOrdinalDivision,
    satisfies_conj_iff, satisfies_mem_iff, satisfies_exists_iff,
    satisfies_isOrdinal_iff,
    satisfies_isOrdinalMultiplication_iff 𝕀 hExt,
    satisfies_isOrdinalAddition_iff 𝕀 hExt,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

end Formula

namespace BinarySchema

/-- 集合编码关系 schema 的解释就是纸面的有序对成员关系。 -/
theorem denote_setCoded_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1) (left right : ℳ.Domain) :
    (RelationSchema.setCoded 𝒞).denote env left right ↔
      ℳ.PairMember 𝕀 left right (env.bound 0) := by
  change
    Formula.satisfies ((env.push left).push right)
        (Formula.orderedPairMem 𝒞
          (.bound 1) (.bound 0) (.bound 2)) ↔
      ℳ.PairMember 𝕀 left right (env.bound 0)
  rw [Formula.satisfies_orderedPairMem_iff 𝕀]
  rfl

end BinarySchema

namespace Formula

/-- 集合编码线序公式与纸面语义一致。 -/
theorem satisfies_isSetCodedLinearOrder_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (relation carrier : Term depth) :
    satisfies env
        (isSetCodedLinearOrder 𝒞 relation carrier) ↔
      ℳ.IsSetCodedLinearOrder 𝕀
        (relation.eval env) (carrier.eval env) := by
  simp only [isSetCodedLinearOrder, isLinearOrderRelation,
    isLinearOrderOn, isStrictPartialOrderOn,
    isIrreflexiveOn, isTransitiveOn,
    Structure.IsSetCodedLinearOrder,
    satisfies_conj_iff,
    satisfies_isRelation_iff 𝕀,
    satisfies_forallMem_iff, satisfies_neg_iff,
    satisfies_imp_iff, satisfies_disj_iff,
    satisfies_related_iff,
    BinarySchema.denote_setCoded_iff 𝕀,
    TermVector.evalEnv_weaken,
    TermVector.evalEnv_singleton_bound,
    satisfies_extensionalEq_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Structure.SameMembers, and_imp]

/-- 序和关系公式与纸面三分支关系一致。 -/
theorem satisfies_isLinearOrderSumRelation_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sumRelation leftCarrier leftRelation rightCarrier rightRelation :
      Term depth) :
    satisfies env
        (isLinearOrderSumRelation 𝒞 sumRelation
          leftCarrier leftRelation rightCarrier rightRelation) ↔
      ℳ.IsLinearOrderSumRelation 𝕀
        (sumRelation.eval env)
        (leftCarrier.eval env) (leftRelation.eval env)
        (rightCarrier.eval env) (rightRelation.eval env) := by
  simp only [isLinearOrderSumRelation,
    Structure.IsLinearOrderSumRelation,
    satisfies_forall_iff, satisfies_iff_iff,
    satisfies_orderedPairMem_iff 𝕀,
    satisfies_disj_iff, satisfies_conj_iff, satisfies_mem_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 线性序和公式与纸面定义一致。 -/
theorem satisfies_isLinearOrderSum_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (sumCarrier sumRelation leftCarrier leftRelation
      rightCarrier rightRelation : Term depth) :
    satisfies env
        (isLinearOrderSum 𝒞 sumCarrier sumRelation
          leftCarrier leftRelation rightCarrier rightRelation) ↔
      ℳ.IsLinearOrderSum 𝕀
        (sumCarrier.eval env) (sumRelation.eval env)
        (leftCarrier.eval env) (leftRelation.eval env)
        (rightCarrier.eval env) (rightRelation.eval env) := by
  simp only [isLinearOrderSum, Structure.IsLinearOrderSum,
    satisfies_conj_iff,
    satisfies_isSetCodedLinearOrder_iff 𝕀,
    satisfies_isDisjoint_iff, satisfies_isUnionOfTwo_iff,
    satisfies_isRelation_iff 𝕀,
    satisfies_isLinearOrderSumRelation_iff 𝕀]

/-- 右字典序积关系公式与纸面定义一致。 -/
theorem satisfies_isRightLexicographicProductRelation_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (productRelation leftCarrier leftRelation
      rightCarrier rightRelation : Term depth) :
    satisfies env
        (isRightLexicographicProductRelation 𝒞 productRelation
          leftCarrier leftRelation rightCarrier rightRelation) ↔
      ℳ.IsRightLexicographicProductRelation 𝕀
        (productRelation.eval env)
        (leftCarrier.eval env) (leftRelation.eval env)
        (rightCarrier.eval env) (rightRelation.eval env) := by
  simp only [isRightLexicographicProductRelation,
    Structure.IsRightLexicographicProductRelation,
    satisfies_forall_iff, satisfies_iff_iff,
    satisfies_orderedPairMem_iff 𝕀,
    satisfies_existsMem_iff, satisfies_conj_iff,
    satisfies_disj_iff,
    𝕀.satisfies_code_iff,
    satisfies_extensionalEq_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Structure.SameMembers]

/-- 线性序积公式与纸面定义一致。 -/
theorem satisfies_isLinearOrderProduct_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (productCarrier productRelation leftCarrier leftRelation
      rightCarrier rightRelation : Term depth) :
    satisfies env
        (isLinearOrderProduct 𝒞 productCarrier productRelation
          leftCarrier leftRelation rightCarrier rightRelation) ↔
      ℳ.IsLinearOrderProduct 𝕀
        (productCarrier.eval env) (productRelation.eval env)
        (leftCarrier.eval env) (leftRelation.eval env)
        (rightCarrier.eval env) (rightRelation.eval env) := by
  simp only [isLinearOrderProduct, Structure.IsLinearOrderProduct,
    satisfies_conj_iff,
    satisfies_isSetCodedLinearOrder_iff 𝕀,
    satisfies_isCartesianProduct_iff 𝕀,
    satisfies_isRelation_iff 𝕀,
    satisfies_isRightLexicographicProductRelation_iff 𝕀]

end Formula

end Project
end Definitional

end SetTheory
end YesMetaZFC
