import YesMetaZFC.SetTheory.Ord.Arithmetic.Normal
import YesMetaZFC.SetTheory.Ord.Natural

/-!
# 序数正规函数的不动点

本模块构造从零开始的超限迭代，证明正规序数函数在 `ω` 次迭代的极限处
取得不动点，并将该结论实例化为 epsilon 数及最小 epsilon 数的存在唯一性。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

variable {ℳ : Structure.{u}}
variable {𝒞 : Definitional.Project.OrderedPairConvention}

namespace Structure

/-- 只在序数输入上使用原函数，域外统一取空集。 -/
def IsOrdinalTotalization
    (function : ℳ.Domain → ℳ.Domain → Prop)
    (input output : ℳ.Domain) : Prop :=
  (ℳ.IsOrdinal input ∧ function input output) ∨
    (¬ ℳ.IsOrdinal input ∧ ∀ value, ¬ ℳ.mem value output)

/-- 从零序数开始迭代序数类函数，极限步取此前值域的并。 -/
def IsOrdinalIterationStep
    (𝕀 : 𝒞.Interpretation ℳ)
    (function : ℳ.Domain → ℳ.Domain → Prop)
    (sequence output : ℳ.Domain) : Prop :=
  ℳ.IsZeroSuccessorLimitStep 𝕀
    (fun initial => ∀ value, ¬ ℳ.mem value initial)
    (ℳ.IsOrdinalTotalization function) sequence output

/-- `value` 是从零序数开始迭代 `function` 在 `α` 处的值。 -/
def IsOrdinalIteration
    (𝕀 : 𝒞.Interpretation ℳ)
    (function : ℳ.Domain → ℳ.Domain → Prop)
    (α value : ℳ.Domain) : Prop :=
  ℳ.IsRecursionValue 𝕀
    (ℳ.IsOrdinalIterationStep 𝕀 function) α value

/-- `α` 是以 `ω` 为底的序数幂不动点。 -/
def IsEpsilonNumber
    (𝕀 : 𝒞.Interpretation ℳ)
    (ω α : ℳ.Domain) : Prop :=
  ℳ.IsOrdinal α ∧
    ℳ.IsOrdinalExponentiation 𝕀 α ω α

/-- `epsilon` 是最小的以 `ω` 为底的序数幂不动点。 -/
def IsEpsilonZero
    (𝕀 : 𝒞.Interpretation ℳ)
    (ω epsilon : ℳ.Domain) : Prop :=
  ℳ.IsEpsilonNumber 𝕀 ω epsilon ∧
    ∀ candidate,
      ℳ.IsEpsilonNumber 𝕀 ω candidate →
        epsilon = candidate ∨ ℳ.mem epsilon candidate

end Structure

namespace Definitional
namespace Project
namespace BinarySchema

/-- 从零序数开始反复应用给定二元 schema 的递归算子。 -/
def ordinalIterationOperator
    (𝒞 : OrderedPairConvention)
    {parameterCount : Nat} (function : BinarySchema parameterCount) :
    BinarySchema parameterCount where
  body :=
    .disj
      (.conj
        (Formula.isZeroLengthSequence 𝒞 (.bound 1))
        (Formula.isEmpty (.bound 0))) <|
      .disj
        (.existsE <| .conj
          (Formula.isSuccessorLengthSequenceWithLast 𝒞
            (.bound 2) Term.newest) <|
          .disj
            (.conj (Formula.isOrdinal Term.newest) <|
              Formula.related function
                (TermVector.boundParameters parameterCount 3)
                Term.newest (.bound 1))
            (.conj (.neg <| Formula.isOrdinal Term.newest)
              (Formula.isEmpty (.bound 1))))
        (Formula.isLimitLengthSequenceWithUnion 𝒞
          (.bound 1) (.bound 0))
  freeClosed := by
    simp [Formula.isZeroLengthSequence,
      Formula.isSuccessorLengthSequenceWithLast,
      Formula.isLimitLengthSequenceWithUnion,
      Formula.isSequenceOfLength,
      Formula.isOrdinal, Formula.isTransitive,
      Formula.isWellOrderOn, Formula.isLinearOrderOn,
      Formula.isStrictPartialOrderOn, Formula.isIrreflexiveOn,
      Formula.isTransitiveOn, Formula.isLeastOf,
      Formula.lessOrEqual, Formula.isFunction,
      Formula.isRelation, Formula.isDomain, Formula.isRange,
      Formula.isEmpty, Formula.isSuccessor,
      Formula.isLimitOrdinal, Formula.isUnion,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.subset, Formula.extensionalEq,
      Formula.FreeClosed, Term.newest,
      TermVector.boundParameters, Term.weaken]
    exact Formula.related_freeClosed_of_closed
      (relation := function)
      (parameters := TermVector.boundParameters parameterCount 3)
      (left := Term.newest) (right := .bound 1)
      (by simp) (by simp) (by simp)

/-- 由超限递归得到的序数函数迭代关系。 -/
def ordinalIteration
    (𝒞 : OrderedPairConvention)
    {parameterCount : Nat} (function : BinarySchema parameterCount) :
    BinarySchema parameterCount :=
  transfiniteRecursion 𝒞
    (ordinalIterationOperator 𝒞 function)

end BinarySchema

namespace Formula

/-- `value` 是从零序数开始迭代 `function` 在 `α` 处的值。 -/
def isOrdinalIteration
    (𝒞 : OrderedPairConvention)
    {parameterCount depth : Nat}
    (function : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (α value : Term depth) : Formula 1 depth :=
  related (function.ordinalIteration 𝒞)
    parameters α value

/-- `α` 是以 `ω` 为底的序数幂不动点。 -/
def isEpsilonNumber
    (𝒞 : OrderedPairConvention)
    {depth : Nat} (ω α : Term depth) :
    Formula 1 depth :=
  .conj (isOrdinal α) <|
    isOrdinalExponentiation 𝒞 α ω α

/-- `epsilon` 是最小的以 `ω` 为底的序数幂不动点。 -/
def isEpsilonZero
    (𝒞 : OrderedPairConvention)
    {depth : Nat} (ω epsilon : Term depth) :
    Formula 1 depth :=
  .conj (isEpsilonNumber 𝒞 ω epsilon) <|
    .forallE <| .imp
      (isEpsilonNumber 𝒞 ω.weaken Term.newest) <|
      .disj
        (extensionalEq epsilon.weaken Term.newest)
        (.mem epsilon.weaken Term.newest)

end Formula

namespace UnarySchema

/-- 给定 `ω` 后，分离其中的序数幂不动点。 -/
def epsilonNumber
    (𝒞 : OrderedPairConvention) : UnarySchema 1 where
  body :=
    Formula.isEpsilonNumber 𝒞 (.bound 1) (.bound 0)
  freeClosed := by
    simp [Formula.isEpsilonNumber,
      Formula.isOrdinalExponentiation,
      Formula.isOrdinal, Formula.isTransitive,
      Formula.isWellOrderOn, Formula.isLinearOrderOn,
      Formula.isStrictPartialOrderOn, Formula.isIrreflexiveOn,
      Formula.isTransitiveOn, Formula.isLeastOf,
      Formula.lessOrEqual, Formula.forallMem,
      Formula.existsMem, Formula.subset, Formula.extensionalEq,
      Formula.FreeClosed,
      TermVector.singleton, Term.newest,
      Term.weaken]
    exact Formula.related_freeClosed_of_closed
      (relation := BinarySchema.ordinalExponentiation 𝒞)
      (parameters := TermVector.ofFn fun _ => Term.bound 1)
      (left := .bound 0) (right := .bound 0)
      (by intro entry; simp) (by simp) (by simp)

end UnarySchema

namespace BinarySchema

@[prove_auto_norm semantic]
theorem denote_ordinalIterationOperator_iff
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : BinarySchema parameterCount)
    (sequence output : ℳ.Domain) :
    (function.ordinalIterationOperator 𝒞).denote
        env sequence output ↔
      ℳ.IsOrdinalIterationStep 𝕀
        (function.denote env) sequence output := by
  simp only [ordinalIterationOperator, denote,
    Structure.IsOrdinalIterationStep,
    Structure.IsZeroSuccessorLimitStep,
    Structure.IsOrdinalTotalization,
    Formula.satisfies_disj_iff,
    Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff,
    Formula.satisfies_neg_iff,
    Formula.satisfies_isZeroLengthSequence_iff 𝕀 hExt,
    Formula.satisfies_isEmpty_iff,
    Formula.satisfies_isSuccessorLengthSequenceWithLast_iff
      𝕀 hExt,
    Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_related_iff,
    Formula.satisfies_isLimitLengthSequenceWithUnion_iff
      𝕀 hExt,
    TermVector.evalEnv_boundParameters_three,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Definitional.Term.eval_newest]

@[prove_auto_norm semantic]
theorem denote_ordinalIteration_iff
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : BinarySchema parameterCount)
    (α value : ℳ.Domain) :
    (function.ordinalIteration 𝒞).denote env α value ↔
      ℳ.IsOrdinalIteration 𝕀
        (function.denote env) α value := by
  have hOperator :
      (function.ordinalIterationOperator 𝒞).denote env =
        ℳ.IsOrdinalIterationStep 𝕀
          (function.denote env) := by
    funext sequence output
    apply propext
    exact denote_ordinalIterationOperator_iff
      𝕀 hExt env function sequence output
  rw [ordinalIteration]
  rw [Formula.denote_transfiniteRecursion_iff
    𝕀 hExt env
    (function.ordinalIterationOperator 𝒞) α value]
  rw [hOperator]
  rfl

end BinarySchema

namespace Formula

@[prove_auto_norm semantic]
theorem satisfies_isOrdinalIteration_iff
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {parameterCount depth : Nat} (env : Env ℳ depth)
    (function : BinarySchema parameterCount)
    (parameters : TermVector parameterCount depth)
    (α value : Term depth) :
    satisfies env
        (isOrdinalIteration 𝒞 function
          parameters α value) ↔
      ℳ.IsOrdinalIteration 𝕀
        (function.denote (parameters.evalEnv env))
        (α.eval env) (value.eval env) := by
  rw [isOrdinalIteration, satisfies_related_iff]
  exact BinarySchema.denote_ordinalIteration_iff
    𝕀 hExt (parameters.evalEnv env) function
      (α.eval env) (value.eval env)

/-- epsilon 数公式与纸面不动点定义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isEpsilonNumber_iff
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (ω α : Term depth) :
    satisfies env
        (isEpsilonNumber 𝒞 ω α) ↔
      ℳ.IsEpsilonNumber 𝕀
        (ω.eval env) (α.eval env) := by
  simp only [isEpsilonNumber, Structure.IsEpsilonNumber,
    satisfies_conj_iff,
    satisfies_isOrdinal_iff,
    satisfies_isOrdinalExponentiation_iff 𝕀 hExt]

/-- 最小 epsilon 数公式与纸面最小性定义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isEpsilonZero_iff
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (ω epsilon : Term depth) :
    satisfies env
        (isEpsilonZero 𝒞 ω epsilon) ↔
      ℳ.IsEpsilonZero 𝕀
        (ω.eval env) (epsilon.eval env) := by
  simp only [isEpsilonZero, Structure.IsEpsilonZero,
    satisfies_conj_iff, satisfies_forall_iff,
    satisfies_imp_iff, satisfies_disj_iff, satisfies_mem_iff,
    satisfies_isEpsilonNumber_iff 𝕀 hExt,
    satisfies_extensionalEq_iff_eq hExt,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

end Formula

end Project
end Definitional

namespace ZF

open Definitional.Project

/-- 序数类函数在域外补空集后，对所有对象全定义且单值。 -/
theorem ordinalTotalization_isClassFunction
    (hZF : ℳ.Models SetTheory.ZF)
    {function : ℳ.Domain → ℳ.Domain → Prop}
    (hFunction : ℳ.IsClassFunctionOnOrdinals function) :
    ∀ input,
      ∃ output,
        ℳ.IsOrdinalTotalization function input output ∧
          ∀ other,
            ℳ.IsOrdinalTotalization function input other →
              other = output := by
  intro input
  by_cases hInput : ℳ.IsOrdinal input
  · rcases hFunction input hInput with
      ⟨output, hOutput, hUnique⟩
    refine ⟨output, Or.inl ⟨hInput, hOutput⟩, ?_⟩
    intro other hOther
    rcases hOther with hOther | hOther
    · exact hUnique other hOther.2
    · exact False.elim (hOther.1 hInput)
  · rcases KP.exists_empty (ZF.modelsKP hZF) with
      ⟨output, hOutput⟩
    refine ⟨output, Or.inr ⟨hInput, hOutput⟩, ?_⟩
    intro other hOther
    rcases hOther with hOther | hOther
    · exact False.elim (hInput hOther.1)
    · apply hZF.1.eq_of_same_members
      intro value
      exact iff_of_false (hOther.2 value) (hOutput value)

/-- 从零序数开始的迭代步在所有超限序列上全定义且单值。 -/
theorem ordinalIterationStep_isClassFunctionOnTransfiniteSequences
    (hZF : ℳ.Models SetTheory.ZF)
    (𝕀 : 𝒞.Interpretation ℳ)
    {function : ℳ.Domain → ℳ.Domain → Prop}
    (hFunction : ℳ.IsClassFunctionOnOrdinals function) :
    ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
      (ℳ.IsOrdinalIterationStep 𝕀 function) := by
  rcases KP.exists_empty (ZF.modelsKP hZF) with
    ⟨zero, hZero⟩
  exact
    zeroSuccessorLimitStep_isClassFunctionOnTransfiniteSequences
      hZF 𝕀
      (fun initial => ∀ value, ¬ ℳ.mem value initial)
      (ℳ.IsOrdinalTotalization function)
      ⟨zero, hZero, fun other hOther =>
        hZF.1.eq_of_same_members other zero
          (fun value => iff_of_false
            (hOther value) (hZero value))⟩
      (ordinalTotalization_isClassFunction hZF hFunction)

/-- 迭代算子的 schema 解释在所有超限序列上全定义且单值。 -/
theorem ordinalIterationOperator_isClassFunctionOnTransfiniteSequences
    (hZF : ℳ.Models SetTheory.ZF)
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hFunction :
      ℳ.IsClassFunctionOnOrdinals (function.denote env)) :
    ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
      ((function.ordinalIterationOperator 𝒞).denote env) := by
  have hStep :=
    ordinalIterationStep_isClassFunctionOnTransfiniteSequences
      hZF 𝕀 hFunction
  intro sequence hSequence
  rcases hStep sequence hSequence with
    ⟨output, hOutput, hUnique⟩
  refine ⟨output, ?_, ?_⟩
  · exact
      (BinarySchema.denote_ordinalIterationOperator_iff
        𝕀 hZF.1 env function sequence output).mpr
        hOutput
  · intro other hOther
    apply hUnique other
    exact
      (BinarySchema.denote_ordinalIterationOperator_iff
        𝕀 hZF.1 env function sequence other).mp
        hOther

/-- 从零序数开始的迭代关系在序数类上全定义且单值。 -/
theorem ordinalIteration_isClassFunctionOnOrdinals
    (hZF : ℳ.Models SetTheory.ZF)
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hFunction :
      ℳ.IsClassFunctionOnOrdinals (function.denote env)) :
    ℳ.IsClassFunctionOnOrdinals
      ((function.ordinalIteration 𝒞).denote env) := by
  simpa [BinarySchema.ordinalIteration] using
    transfiniteRecursion_isClassFunctionOnOrdinals
      hZF 𝕀 env
      (function.ordinalIterationOperator 𝒞)
      (ordinalIterationOperator_isClassFunctionOnTransfiniteSequences
        hZF 𝕀 env function hFunction)

/-- 从零序数开始的迭代关系在每个序数处存在唯一值。 -/
theorem ordinalIteration_existsUnique
    (hZF : ℳ.Models SetTheory.ZF)
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hFunction :
      ℳ.IsClassFunctionOnOrdinals (function.denote env))
    {α : ℳ.Domain} (hα : ℳ.IsOrdinal α) :
    ∃ value,
      ℳ.IsOrdinalIteration 𝕀
          (function.denote env) α value ∧
        ∀ other,
          ℳ.IsOrdinalIteration 𝕀
              (function.denote env) α other →
            other = value := by
  rcases ordinalIteration_isClassFunctionOnOrdinals
      hZF 𝕀 env function hFunction
      α hα with
    ⟨value, hValue, hUnique⟩
  refine ⟨value, ?_, ?_⟩
  · exact
      (BinarySchema.denote_ordinalIteration_iff
        𝕀 hZF.1 env function α value).mp
        hValue
  · intro other hOther
    apply hUnique other
    exact
      (BinarySchema.denote_ordinalIteration_iff
        𝕀 hZF.1 env function α other).mpr
        hOther

/-- 正规序数函数从零序数开始的每个迭代值仍是序数。 -/
theorem ordinalIteration_isOrdinalClassFunction
    (hZF : ℳ.Models SetTheory.ZF)
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hNormal :
      ℳ.IsNormalOrdinalFunction (function.denote env)) :
    ℳ.IsOrdinalClassFunction
      ((function.ordinalIteration 𝒞).denote env) := by
  have hClass :=
    ordinalIteration_isClassFunctionOnOrdinals
      hZF 𝕀 env function hNormal.1.1
  apply ordinalClassFunction_of_progressive
      hZF env (function.ordinalIteration 𝒞) hClass
  intro α hα hPrevious value hValue
  have hIteration :
      ℳ.IsOrdinalIteration 𝕀
        (function.denote env) α value :=
    (BinarySchema.denote_ordinalIteration_iff
      𝕀 hZF.1 env function α value).mp
      hValue
  rcases hIteration with ⟨sequence, hSequence, hOutput⟩
  -- 递归算子的三支与当前序数的零、后继、极限分类逐一对应。
  rcases hα.classify hZF.1 with
    hZero | hSuccessor | hLimit
  · have hZeroLength :
        ℳ.IsZeroLengthSequence 𝕀 sequence :=
      ⟨α, hSequence.1, hZero⟩
    rcases hOutput with hOutput | hOutput | hOutput
    · exact Structure.IsOrdinal.of_no_members hOutput.2
    · rcases hOutput with
        ⟨_, hSuccessorLength, _⟩
      exact False.elim <|
        hZeroLength.not_successorLength
          hZF.1 hSuccessorLength
    · exact False.elim <|
        hZeroLength.not_limitLength hZF.1 hOutput
  · rcases hSuccessor with
      ⟨predecessor, hPredecessorOrdinal, hSuccessor⟩
    have hPredecessorMem : ℳ.mem predecessor α :=
      (hSuccessor predecessor).mpr
        (Or.inr fun _ => Iff.rfl)
    rcases (hSequence.1.2.2 predecessor).mp
        hPredecessorMem with
      ⟨previous, hPreviousPair⟩
    have hSuccessorLength :
        ℳ.IsSuccessorLengthSequenceWithLast 𝕀
          sequence previous :=
      ⟨predecessor, hPredecessorOrdinal, α,
        hSuccessor, hSequence.1, hPreviousPair⟩
    have hPreviousIteration :
        ℳ.IsOrdinalIteration 𝕀
          (function.denote env) predecessor previous :=
      hSequence.recursionValue_of_pairMember
        hPredecessorMem hPreviousPair
    have hPreviousOrdinal : ℳ.IsOrdinal previous :=
      hPrevious predecessor hPredecessorMem previous <|
        (BinarySchema.denote_ordinalIteration_iff
          𝕀 hZF.1 env function
          predecessor previous).mpr hPreviousIteration
    rcases hOutput with hOutput | hOutput | hOutput
    · exact False.elim <|
        hOutput.1.not_successorLength
          hZF.1 hSuccessorLength
    · rcases hOutput with
        ⟨otherPrevious, hOtherLength, hOtherOutput⟩
      have hPreviousEq :=
        hOtherLength.last_eq hZF.1 hSuccessorLength
      subst otherPrevious
      rcases hOtherOutput with hFunctionValue | hOutside
      · exact hNormal.1.2 previous value
          hPreviousOrdinal hFunctionValue.2
      · exact False.elim (hOutside.1 hPreviousOrdinal)
    · exact False.elim <|
        hSuccessorLength.not_limitLength hZF.1 hOutput
  · rcases exists_limitLengthSequenceWithUnion
        hZF 𝕀 hSequence.1 hLimit with
      ⟨_, hCanonical⟩
    rcases hOutput with hOutput | hOutput | hOutput
    · exact False.elim <|
        hOutput.1.not_limitLength hZF.1 hCanonical
    · rcases hOutput with
        ⟨_, hSuccessorLength, _⟩
      exact False.elim <|
        hSuccessorLength.not_limitLength
          hZF.1 hCanonical
    · rcases hOutput with
        ⟨_, _, _, range, hRange, hUnion⟩
      apply Structure.IsOrdinal.of_union
        (ZF.modelsKP hZF) hUnion
      intro member hMember
      rcases (hRange member).mp hMember with
        ⟨index, hMemberPair⟩
      have hIndex : ℳ.mem index α :=
        (hSequence.1.2.2 index).mpr
          ⟨member, hMemberPair⟩
      have hMemberIteration :
          ℳ.IsOrdinalIteration 𝕀
            (function.denote env) index member :=
        hSequence.recursionValue_of_pairMember
          hIndex hMemberPair
      exact hPrevious index hIndex member <|
        (BinarySchema.denote_ordinalIteration_iff
          𝕀 hZF.1 env function
          index member).mpr hMemberIteration

/-- 正规序数函数的每个序数阶段迭代值都是序数。 -/
theorem ordinalIteration_isOrdinal
    (hZF : ℳ.Models SetTheory.ZF)
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hNormal :
      ℳ.IsNormalOrdinalFunction (function.denote env))
    {α value : ℳ.Domain}
    (hα : ℳ.IsOrdinal α)
    (hValue :
      ℳ.IsOrdinalIteration 𝕀
        (function.denote env) α value) :
    ℳ.IsOrdinal value := by
  exact
    (ordinalIteration_isOrdinalClassFunction
      hZF 𝕀 env function hNormal).2
      α value hα <|
        (BinarySchema.denote_ordinalIteration_iff
          𝕀 hZF.1 env function
          α value).mpr hValue

/-- 迭代的零步方程：零阶段仍取零序数。 -/
theorem ordinalIteration_zero_iff
    (hZF : ℳ.Models SetTheory.ZF)
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hFunction :
      ℳ.IsClassFunctionOnOrdinals (function.denote env))
    {zero value : ℳ.Domain}
    (hZero : ∀ member, ¬ ℳ.mem member zero) :
    ℳ.IsOrdinalIteration 𝕀
        (function.denote env) zero value ↔
      ∀ member, ¬ ℳ.mem member value := by
  have iterationValue_empty {selected : ℳ.Domain}
      (hSelected :
        ℳ.IsOrdinalIteration 𝕀
          (function.denote env) zero selected) :
      ∀ member, ¬ ℳ.mem member selected := by
    rcases hSelected with ⟨sequence, hSequence, hOutput⟩
    have hZeroLength :
        ℳ.IsZeroLengthSequence 𝕀 sequence :=
      ⟨zero, hSequence.1, hZero⟩
    rcases hOutput with hOutput | hOutput | hOutput
    · exact hOutput.2
    · rcases hOutput with
        ⟨_, hSuccessorLength, _⟩
      exact False.elim <|
        hZeroLength.not_successorLength
          hZF.1 hSuccessorLength
    · exact False.elim <|
        hZeroLength.not_limitLength hZF.1 hOutput
  constructor
  · exact iterationValue_empty
  · intro hValue
    rcases ordinalIteration_existsUnique
        hZF 𝕀 env function hFunction
        (Structure.IsOrdinal.of_no_members hZero) with
      ⟨selected, hSelected, _⟩
    have hSelectedEmpty := iterationValue_empty hSelected
    have hSelectedEq := by
      apply hZF.1.eq_of_same_members
      intro member
      exact iff_of_false
        (hSelectedEmpty member) (hValue member)
    simpa [hSelectedEq] using hSelected

/-- 迭代的后继步方程：下一阶段应用一次原正规函数。 -/
theorem ordinalIteration_successor_iff
    (hZF : ℳ.Models SetTheory.ZF)
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hNormal :
      ℳ.IsNormalOrdinalFunction (function.denote env))
    {predecessor successor value : ℳ.Domain}
    (hPredecessor : ℳ.IsOrdinal predecessor)
    (hSuccessor : ℳ.SuccessorOf successor predecessor) :
    ℳ.IsOrdinalIteration 𝕀
        (function.denote env) successor value ↔
      ∃ previous,
        ℳ.IsOrdinalIteration 𝕀
            (function.denote env) predecessor previous ∧
          function.denote env previous value := by
  have successorIterationData {selected : ℳ.Domain}
      (hSelected :
        ℳ.IsOrdinalIteration 𝕀
          (function.denote env) successor selected) :
      ∃ previous,
        ℳ.IsOrdinalIteration 𝕀
            (function.denote env) predecessor previous ∧
          function.denote env previous selected := by
    rcases hSelected with ⟨sequence, hSequence, hOutput⟩
    have hPredecessorMem : ℳ.mem predecessor successor :=
      (hSuccessor predecessor).mpr
        (Or.inr fun _ => Iff.rfl)
    rcases (hSequence.1.2.2 predecessor).mp
        hPredecessorMem with
      ⟨previous, hPreviousPair⟩
    have hSuccessorLength :
        ℳ.IsSuccessorLengthSequenceWithLast 𝕀
          sequence previous :=
      ⟨predecessor, hPredecessor, successor, hSuccessor,
        hSequence.1, hPreviousPair⟩
    have hPrevious :
        ℳ.IsOrdinalIteration 𝕀
          (function.denote env) predecessor previous :=
      hSequence.recursionValue_of_pairMember
        hPredecessorMem hPreviousPair
    have hPreviousOrdinal :=
      ordinalIteration_isOrdinal
        hZF 𝕀 env function hNormal
        hPredecessor hPrevious
    rcases hOutput with hOutput | hOutput | hOutput
    · exact False.elim <|
        hOutput.1.not_successorLength
          hZF.1 hSuccessorLength
    · rcases hOutput with
        ⟨otherPrevious, hOtherLength, hOtherOutput⟩
      have hPreviousEq :=
        hOtherLength.last_eq hZF.1 hSuccessorLength
      subst otherPrevious
      rcases hOtherOutput with hFunctionValue | hOutside
      · exact ⟨previous, hPrevious, hFunctionValue.2⟩
      · exact False.elim (hOutside.1 hPreviousOrdinal)
    · exact False.elim <|
        hSuccessorLength.not_limitLength hZF.1 hOutput
  constructor
  · exact successorIterationData
  · rintro ⟨previous, hPrevious, hValue⟩
    have hSuccessorOrdinal :=
      KP.successor_isOrdinal
        (ZF.modelsKP hZF) hPredecessor hSuccessor
    rcases ordinalIteration_existsUnique
        hZF 𝕀 env function hNormal.1.1
        hSuccessorOrdinal with
      ⟨selected, hSelected, _⟩
    rcases successorIterationData hSelected with
      ⟨selectedPrevious, hSelectedPrevious, hSelectedValue⟩
    rcases ordinalIteration_existsUnique
        hZF 𝕀 env function hNormal.1.1
        hPredecessor with
      ⟨_, _, hPreviousUnique⟩
    have hPreviousEq : selectedPrevious = previous :=
      (hPreviousUnique selectedPrevious hSelectedPrevious).trans
        (hPreviousUnique previous hPrevious).symm
    subst selectedPrevious
    rcases hNormal.1.1 previous
        (ordinalIteration_isOrdinal
          hZF 𝕀 env function hNormal
          hPredecessor hPrevious) with
      ⟨_, _, hValueUnique⟩
    have hSelectedEq : selected = value :=
      (hValueUnique selected hSelectedValue).trans
        (hValueUnique value hValue).symm
    simpa [hSelectedEq] using hSelected

/-- 迭代的极限步方程：极限阶段取此前迭代值集合的并。 -/
theorem ordinalIteration_limit_iff
    (hZF : ℳ.Models SetTheory.ZF)
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hFunction :
      ℳ.IsClassFunctionOnOrdinals (function.denote env))
    {limit value : ℳ.Domain}
    (hLimit : ℳ.IsLimitOrdinal limit) :
    ℳ.IsOrdinalIteration 𝕀
        (function.denote env) limit value ↔
      ∃ range,
        (∀ member,
          ℳ.mem member range ↔
            ∃ index, ℳ.mem index limit ∧
              ℳ.IsOrdinalIteration 𝕀
                (function.denote env) index member) ∧
          ℳ.IsUnionOf value range := by
  have limitIterationData {selected : ℳ.Domain}
      (hSelected :
        ℳ.IsOrdinalIteration 𝕀
          (function.denote env) limit selected) :
      ∃ range,
        (∀ member,
          ℳ.mem member range ↔
            ∃ index, ℳ.mem index limit ∧
              ℳ.IsOrdinalIteration 𝕀
                (function.denote env) index member) ∧
          ℳ.IsUnionOf selected range := by
    apply Structure.IsRecursionValue.limit_range hSelected
    · intro sequence output hSequence hOutput
      rcases exists_limitLengthSequenceWithUnion
          hZF 𝕀 hSequence.1 hLimit with
        ⟨_, hCanonical⟩
      rcases hOutput with hOutput | hOutput | hOutput
      · exact False.elim <|
          hOutput.1.not_limitLength hZF.1 hCanonical
      · rcases hOutput with
          ⟨_, hSuccessorLength, _⟩
        exact False.elim <|
          hSuccessorLength.not_limitLength
            hZF.1 hCanonical
      · exact hOutput
    · intro index hIndex first second hFirst hSecond
      rcases ordinalIteration_existsUnique
          hZF 𝕀 env function hFunction
          (hLimit.1.mem hIndex) with
        ⟨_, _, hUnique⟩
      exact
        (hUnique first hFirst).trans
          (hUnique second hSecond).symm
  constructor
  · exact limitIterationData
  · rintro ⟨range, hRange, hUnion⟩
    rcases ordinalIteration_existsUnique
        hZF 𝕀 env function hFunction hLimit.1 with
      ⟨selected, hSelected, _⟩
    rcases limitIterationData hSelected with
      ⟨selectedRange, hSelectedRange, hSelectedUnion⟩
    have hRangeEq : range = selectedRange := by
      apply hZF.1.eq_of_same_members
      intro member
      rw [hRange member, hSelectedRange member]
    subst selectedRange
    have hValueEq :=
      Structure.IsUnionOf.eq hZF.1
        hUnion hSelectedUnion
    simpa [hValueEq] using hSelected

/--
若零序数严格小于它的首个函数值，则从零序数开始的迭代在 `ω` 上严格递增。
-/
theorem ordinalIteration_isIncreasing_on_omega
    (hZF : ℳ.Models SetTheory.ZF)
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hNormal :
      ℳ.IsNormalOrdinalFunction (function.denote env))
    {ω : ℳ.Domain} (hω : ℳ.IsOmega ω)
    (hInitialGrowth : ∀ zero,
      (∀ member, ¬ ℳ.mem member zero) →
        ∀ next, function.denote env zero next →
          ℳ.mem zero next) :
    ∀ α, ℳ.mem α ω →
      ∀ predecessor, ℳ.mem predecessor α →
        ∀ predecessorValue αValue,
          ℳ.IsOrdinalIteration 𝕀
              (function.denote env) predecessor predecessorValue →
            ℳ.IsOrdinalIteration 𝕀
              (function.denote env) α αValue →
            ℳ.mem predecessorValue αValue := by
  let iteration := function.ordinalIteration 𝒞
  let property : ℳ.Domain → Prop := fun α =>
    ∀ predecessor, ℳ.mem predecessor α →
      ∀ predecessorValue αValue,
        iteration.denote env predecessor predecessorValue →
        iteration.denote env α αValue →
          ℳ.mem predecessorValue αValue
  have hProperty :
      ∀ α, ℳ.mem α ω → property α := by
    apply hω.induction property
    · rcases exists_separation hZF
          iteration.ordinalIncreasingAt env ω with
        ⟨closed, hClosed⟩
      refine ⟨closed, fun α => ?_⟩
      rw [hClosed α]
      exact and_congr_right fun _ =>
        Formula.satisfies_ordinalIncreasingAt_iff
          env iteration α
    · intro empty hEmpty predecessor hPredecessor
      exact False.elim (hEmpty predecessor hPredecessor)
    · intro predecessor hPredecessorOmega hPredecessorProperty
        successor hSuccessor
      intro earlier hEarlier predecessorValue successorValue
        hEarlierValue hSuccessorValue
      have hPredecessorOrdinal :=
        hω.members_areOrdinals hZF
          predecessor hPredecessorOmega
      have hSuccessorOrdinal :=
        KP.successor_isOrdinal
          (ZF.modelsKP hZF) hPredecessorOrdinal hSuccessor
      have hSuccessorIteration :
          ℳ.IsOrdinalIteration 𝕀
            (function.denote env) successor successorValue :=
        (BinarySchema.denote_ordinalIteration_iff
          𝕀 hZF.1 env function
          successor successorValue).mp hSuccessorValue
      rcases
          (ordinalIteration_successor_iff
            hZF 𝕀 env function hNormal
            hPredecessorOrdinal hSuccessor).mp
            hSuccessorIteration with
        ⟨previousValue, hPreviousIteration, hSuccessorFunction⟩
      have hPreviousValue :
          iteration.denote env predecessor previousValue :=
        (BinarySchema.denote_ordinalIteration_iff
          𝕀 hZF.1 env function
          predecessor previousValue).mpr hPreviousIteration
      have hPreviousOrdinal :=
        ordinalIteration_isOrdinal
          hZF 𝕀 env function hNormal
          hPredecessorOrdinal hPreviousIteration
      have hSuccessorValueOrdinal :=
        ordinalIteration_isOrdinal
          hZF 𝕀 env function hNormal
          hSuccessorOrdinal hSuccessorIteration
      have hPreviousSuccessor :
          ℳ.mem previousValue successorValue := by
        by_cases hPredecessorNonempty :
            ∃ member, ℳ.mem member predecessor
        · rcases hω.exists_predecessor_of_mem_of_nonempty
              hZF hPredecessorOmega hPredecessorNonempty with
            ⟨prior, hPriorOmega, hPredecessorSuccessor⟩
          rcases
              (ordinalIteration_successor_iff
                hZF 𝕀 env function hNormal
                (hω.members_areOrdinals hZF
                  prior hPriorOmega)
                hPredecessorSuccessor).mp hPreviousIteration with
            ⟨priorValue, hPriorIteration, hPreviousFunction⟩
          have hPriorValue :
              iteration.denote env prior priorValue :=
            (BinarySchema.denote_ordinalIteration_iff
              𝕀 hZF.1 env function
              prior priorValue).mpr hPriorIteration
          have hPriorPredecessor :
              ℳ.mem prior predecessor :=
            (hPredecessorSuccessor prior).mpr
              (Or.inr fun _ => Iff.rfl)
          have hPriorValuePredecessor :
              ℳ.mem priorValue previousValue :=
            hPredecessorProperty prior hPriorPredecessor
              priorValue previousValue hPriorValue hPreviousValue
          exact hNormal.2.1 priorValue previousValue
            (ordinalIteration_isOrdinal
              hZF 𝕀 env function hNormal
              (hω.members_areOrdinals hZF prior hPriorOmega)
              hPriorIteration)
            hPreviousOrdinal hPriorValuePredecessor
            previousValue successorValue
            hPreviousFunction hSuccessorFunction
        · have hPredecessorEmpty :
              ∀ member, ¬ ℳ.mem member predecessor := by
            intro member hMember
            exact hPredecessorNonempty ⟨member, hMember⟩
          have hPreviousEmpty :=
            (ordinalIteration_zero_iff
              hZF 𝕀 env function hNormal.1.1
              hPredecessorEmpty).mp hPreviousIteration
          exact hInitialGrowth previousValue hPreviousEmpty
            successorValue hSuccessorFunction
      rcases (hSuccessor earlier).mp hEarlier with
        hEarlierPredecessor | hSame
      · have hEarlierPrevious :
            ℳ.mem predecessorValue previousValue :=
          hPredecessorProperty earlier hEarlierPredecessor
            predecessorValue previousValue
            hEarlierValue hPreviousValue
        exact hSuccessorValueOrdinal.transitive
          previousValue hPreviousSuccessor
          predecessorValue hEarlierPrevious
      · have hEarlierEq :=
          hZF.1.eq_of_same_members earlier predecessor hSame
        subst earlier
        rcases ordinalIteration_existsUnique
            hZF 𝕀 env function hNormal.1.1
            hPredecessorOrdinal with
          ⟨_, _, hUnique⟩
        have hEarlierIteration :
            ℳ.IsOrdinalIteration 𝕀
              (function.denote env) predecessor predecessorValue :=
          (BinarySchema.denote_ordinalIteration_iff
            𝕀 hZF.1 env function
            predecessor predecessorValue).mp hEarlierValue
        have hValueEq : predecessorValue = previousValue :=
          (hUnique predecessorValue hEarlierIteration).trans
            (hUnique previousValue hPreviousIteration).symm
        simpa [hValueEq] using hPreviousSuccessor
  intro α hα predecessor hPredecessor
    predecessorValue αValue
    hPredecessorValue hαValue
  exact hProperty α hα predecessor hPredecessor
    predecessorValue αValue
    ((BinarySchema.denote_ordinalIteration_iff
      𝕀 hZF.1 env function
      predecessor predecessorValue).mpr hPredecessorValue)
    ((BinarySchema.denote_ordinalIteration_iff
      𝕀 hZF.1 env function
      α αValue).mpr hαValue)

/--
任意满足 `0 < F(0)` 的可定义正规序数函数都有一个非零极限不动点。

证明取从零开始的 `ω` 次迭代之上确界，并用正规函数的连续性把函数作用与该上确界
交换。
-/
theorem normalFunction_exists_limitFixedPoint
    (hZF : ℳ.Models SetTheory.ZF)
    (𝕀 : 𝒞.Interpretation ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hNormal :
      ℳ.IsNormalOrdinalFunction (function.denote env))
    {ω : ℳ.Domain} (hω : ℳ.IsOmega ω)
    (hInitialGrowth : ∀ zero,
      (∀ member, ¬ ℳ.mem member zero) →
        ∀ next, function.denote env zero next →
          ℳ.mem zero next) :
    ∃ fixed,
      ℳ.IsOrdinalIteration 𝕀
          (function.denote env) ω fixed ∧
        ℳ.IsLimitOrdinal fixed ∧
          function.denote env fixed fixed := by
  have hωOrdinal := hω.isOrdinal hZF
  have hωLimit := hω.isLimitOrdinal hZF
  have hIncreasing :=
    ordinalIteration_isIncreasing_on_omega
      hZF 𝕀 env function hNormal
      hω hInitialGrowth
  rcases ordinalIteration_existsUnique
      hZF 𝕀 env function hNormal.1.1
      hωOrdinal with
    ⟨fixed, hFixedIteration, _⟩
  have hFixedOrdinal :=
    ordinalIteration_isOrdinal
      hZF 𝕀 env function hNormal
      hωOrdinal hFixedIteration
  rcases
      (ordinalIteration_limit_iff
        hZF 𝕀 env function hNormal.1.1
        hωLimit).mp hFixedIteration with
    ⟨range, hRange, hUnion⟩
  -- 每个有限阶段都能推进到下一阶段，并由严格递增性得到当前值属于下一值。
  have exists_nextIterationValue
      {index current : ℳ.Domain}
      (hIndex : ℳ.mem index ω)
      (hCurrent :
        ℳ.IsOrdinalIteration 𝕀
          (function.denote env) index current) :
      ∃ successor next,
        ℳ.mem successor ω ∧
          ℳ.SuccessorOf successor index ∧
          ℳ.IsOrdinalIteration 𝕀
              (function.denote env) successor next ∧
          function.denote env current next ∧
          ℳ.mem current next := by
    rcases hω.1.2 index hIndex with
      ⟨successor, hSuccessor, hSuccessorOmega⟩
    have hIndexOrdinal :=
      hω.members_areOrdinals hZF index hIndex
    have hSuccessorOrdinal :=
      KP.successor_isOrdinal
        (ZF.modelsKP hZF) hIndexOrdinal hSuccessor
    rcases ordinalIteration_existsUnique
        hZF 𝕀 env function hNormal.1.1
        hSuccessorOrdinal with
      ⟨next, hNext, _⟩
    rcases
        (ordinalIteration_successor_iff
          hZF 𝕀 env function hNormal
          hIndexOrdinal hSuccessor).mp hNext with
      ⟨previous, hPrevious, hFunction⟩
    rcases ordinalIteration_existsUnique
        hZF 𝕀 env function hNormal.1.1
        hIndexOrdinal with
      ⟨_, _, hUnique⟩
    have hPreviousEq : previous = current :=
      (hUnique previous hPrevious).trans
        (hUnique current hCurrent).symm
    subst previous
    have hIndexSuccessor : ℳ.mem index successor :=
      (hSuccessor index).mpr
        (Or.inr fun _ => Iff.rfl)
    exact
      ⟨successor, next, hSuccessorOmega, hSuccessor,
        hNext, hFunction,
        hIncreasing successor hSuccessorOmega
          index hIndexSuccessor current next hCurrent hNext⟩
  -- `ω` 阶段的值非空且传递，因此确为极限序数。
  have hFixedLimit : ℳ.IsLimitOrdinal fixed := by
    refine ⟨hFixedOrdinal, ?_, ?_⟩
    · rcases hω.1.1 with
        ⟨zero, hZero, hZeroOmega⟩
      rcases ordinalIteration_existsUnique
          hZF 𝕀 env function hNormal.1.1
          (Structure.IsOrdinal.of_no_members hZero) with
        ⟨zeroValue, hZeroValue, _⟩
      rcases exists_nextIterationValue hZeroOmega hZeroValue with
        ⟨successor, next, hSuccessorOmega, _,
          hNext, _, hZeroNext⟩
      exact ⟨zeroValue, (hUnion zeroValue).mpr
        ⟨next, (hRange next).mpr
          ⟨successor, hSuccessorOmega, hNext⟩,
          hZeroNext⟩⟩
    · intro member hMember
      rcases (hUnion member).mp hMember with
        ⟨current, hCurrentRange, hMemberCurrent⟩
      rcases (hRange current).mp hCurrentRange with
        ⟨index, hIndex, hCurrent⟩
      rcases exists_nextIterationValue hIndex hCurrent with
        ⟨successor, next, hSuccessorOmega, _,
          hNext, _, hCurrentNext⟩
      exact ⟨current,
        (hUnion current).mpr
          ⟨next, (hRange next).mpr
            ⟨successor, hSuccessorOmega, hNext⟩,
            hCurrentNext⟩,
        hMemberCurrent⟩
  rcases hNormal.1.1 fixed hFixedOrdinal with
    ⟨image, hImage, _⟩
  rcases hNormal.2.2 fixed image
      ⟨hFixedLimit, hImage⟩ with
    ⟨imageRange, hImageRange, hImageUnion⟩
  -- 连续性把 `F(fixed)` 化为此前函数值的并；两边逐成员比较即可识别为同一序数。
  have hImageEq : image = fixed := by
    apply hZF.1.eq_of_same_members
    intro member
    constructor
    · intro hMember
      rcases (hImageUnion member).mp hMember with
        ⟨functionValue, hFunctionValueRange,
          hMemberFunctionValue⟩
      rcases (hImageRange functionValue).mp
          hFunctionValueRange with
        ⟨input, hInputFixed, hInputFunction⟩
      rcases (hUnion input).mp hInputFixed with
        ⟨current, hCurrentRange, hInputCurrent⟩
      rcases (hRange current).mp hCurrentRange with
        ⟨index, hIndex, hCurrent⟩
      rcases exists_nextIterationValue hIndex hCurrent with
        ⟨successor, next, hSuccessorOmega, _,
          hNext, hCurrentFunction, _⟩
      have hFunctionValueNext :
          ℳ.mem functionValue next :=
        hNormal.2.1 input current
          (hFixedOrdinal.mem hInputFixed)
          (ordinalIteration_isOrdinal
            hZF 𝕀 env function hNormal
            (hω.members_areOrdinals hZF index hIndex)
            hCurrent)
          hInputCurrent functionValue next
          hInputFunction hCurrentFunction
      have hNextOrdinal :=
        ordinalIteration_isOrdinal
          hZF 𝕀 env function hNormal
          (hω.members_areOrdinals
            hZF successor hSuccessorOmega)
          hNext
      exact (hUnion member).mpr
        ⟨next, (hRange next).mpr
          ⟨successor, hSuccessorOmega, hNext⟩,
          hNextOrdinal.transitive
            functionValue hFunctionValueNext
            member hMemberFunctionValue⟩
    · intro hMember
      rcases (hUnion member).mp hMember with
        ⟨current, hCurrentRange, hMemberCurrent⟩
      rcases (hRange current).mp hCurrentRange with
        ⟨index, hIndex, hCurrent⟩
      rcases exists_nextIterationValue hIndex hCurrent with
        ⟨successor, next, hSuccessorOmega, _,
          hNext, hCurrentFunction, hCurrentNext⟩
      have hCurrentFixed : ℳ.mem current fixed :=
        (hUnion current).mpr
          ⟨next, (hRange next).mpr
            ⟨successor, hSuccessorOmega, hNext⟩,
            hCurrentNext⟩
      have hNextRange : ℳ.mem next imageRange :=
        (hImageRange next).mpr
          ⟨current, hCurrentFixed, hCurrentFunction⟩
      have hNextOrdinal :=
        ordinalIteration_isOrdinal
          hZF 𝕀 env function hNormal
          (hω.members_areOrdinals
            hZF successor hSuccessorOmega)
          hNext
      exact (hImageUnion member).mpr
        ⟨next, hNextRange,
          hNextOrdinal.transitive
            current hCurrentNext member hMemberCurrent⟩
  exact ⟨fixed, hFixedIteration, hFixedLimit,
    by simpa [hImageEq] using hImage⟩

/-!
## `epsilon_0`
-/

/-- ZF 中存在一个以 `ω` 为底的序数幂不动点。 -/
theorem exists_epsilonNumber
    (hZF : ℳ.Models SetTheory.ZF)
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω : ℳ.Domain} (hω : ℳ.IsOmega ω) :
    ∃ epsilon,
      ℳ.IsEpsilonNumber 𝕀 ω epsilon := by
  rcases hω.exists_ordinalOne_mem with
    ⟨one, hOne, hOneOmega⟩
  have hωOrdinal := hω.isOrdinal hZF
  let env : Env ℳ 1 := {
    bound := fun _ => ω
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hNormal :
      ℳ.IsNormalOrdinalFunction
        ((BinarySchema.ordinalExponentiation 𝒞).denote env) := by
    have hRelation :
        (BinarySchema.ordinalExponentiation 𝒞).denote env =
          fun exponent power =>
            ℳ.IsOrdinalExponentiation 𝕀
              power ω exponent := by
      funext exponent power
      apply propext
      simpa [env] using
        BinarySchema.denote_ordinalExponentiation_iff
          𝕀 hZF.1 env exponent power
    rw [hRelation]
    exact ordinalExponentiation_isNormalOrdinalFunction
      hZF 𝕀 hωOrdinal hOne hOneOmega
  have hInitialGrowth :
      ∀ zero, (∀ member, ¬ ℳ.mem member zero) →
        ∀ next,
          (BinarySchema.ordinalExponentiation 𝒞).denote
              env zero next →
            ℳ.mem zero next := by
    intro zero hZero next hNext
    have hNextSemantic :
        ℳ.IsOrdinalExponentiation 𝕀
          next ω zero :=
      (BinarySchema.denote_ordinalExponentiation_iff
        𝕀 hZF.1 env zero next).mp hNext
    have hNextOne :=
      (ordinalExponentiation_zero_iff
        hZF 𝕀 hωOrdinal hZero).mp hNextSemantic
    rcases hNextOne with
      ⟨oneZero, hOneZero, hNextSuccessor⟩
    have hOneZeroEq : oneZero = zero := by
      apply hZF.1.eq_of_same_members
      intro member
      exact iff_of_false (hOneZero member) (hZero member)
    subst oneZero
    exact (hNextSuccessor zero).mpr
      (Or.inr fun _ => Iff.rfl)
  rcases normalFunction_exists_limitFixedPoint
      hZF 𝕀 env
      (BinarySchema.ordinalExponentiation 𝒞)
      hNormal hω hInitialGrowth with
    ⟨epsilon, hIteration, _, hFixed⟩
  have hFixedExponentiation :
      ℳ.IsOrdinalExponentiation 𝕀
        epsilon ω epsilon :=
    (BinarySchema.denote_ordinalExponentiation_iff
      𝕀 hZF.1 env epsilon epsilon).mp hFixed
  have hEpsilonOrdinal :=
    ordinalIteration_isOrdinal
      hZF 𝕀 env
      (BinarySchema.ordinalExponentiation 𝒞)
      hNormal hωOrdinal hIteration
  exact ⟨epsilon, hEpsilonOrdinal, hFixedExponentiation⟩

/-- ZF 中存在最小的以 `ω` 为底的序数幂不动点。 -/
theorem epsilonZero_exists
    (hZF : ℳ.Models SetTheory.ZF)
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω : ℳ.Domain} (hω : ℳ.IsOmega ω) :
    ∃ epsilon,
      ℳ.IsEpsilonZero 𝕀 ω epsilon := by
  rcases exists_epsilonNumber hZF 𝕀 hω with
    ⟨upper, hUpper⟩
  rcases KP.exists_successor (ZF.modelsKP hZF) upper with
    ⟨bound, hBound⟩
  have hBoundOrdinal :=
    KP.successor_isOrdinal
      (ZF.modelsKP hZF) hUpper.1 hBound
  let env : Env ℳ 1 := {
    bound := fun _ => ω
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_separation hZF
      (UnarySchema.epsilonNumber 𝒞) env bound with
    ⟨candidates, hCandidates⟩
  -- 在已知 epsilon 数的后继中分离全部 epsilon 数，再取该序数良序下的最小元。
  have hCandidatesSemantic (value : ℳ.Domain) :
      ℳ.mem value candidates ↔
        ℳ.mem value bound ∧
          ℳ.IsEpsilonNumber 𝕀 ω value := by
    rw [hCandidates value]
    apply and_congr_right
    intro _
    simpa [UnarySchema.epsilonNumber, env,
      Term.eval_bound_zero_push, Term.eval_bound_one_push] using
      Formula.satisfies_isEpsilonNumber_iff
        𝕀 hZF.1
        (env.push value) (.bound 1) (.bound 0)
  have hCandidatesSubset :
      ℳ.MemberSubset candidates bound := by
    intro value hValue
    exact (hCandidatesSemantic value).mp hValue |>.1
  have hCandidatesNonempty :
      ∃ value, ℳ.mem value candidates := by
    exact ⟨upper, (hCandidatesSemantic upper).mpr
      ⟨(hBound upper).mpr (Or.inr fun _ => Iff.rfl),
        hUpper⟩⟩
  rcases hBoundOrdinal.wellOrder.least
      candidates hCandidatesSubset hCandidatesNonempty with
    ⟨epsilon, hEpsilonCandidates, hLeast⟩
  have hEpsilonData :=
    (hCandidatesSemantic epsilon).mp hEpsilonCandidates
  refine ⟨epsilon, hEpsilonData.2, ?_⟩
  intro candidate hCandidate
  rcases Structure.IsOrdinal.trichotomy hZF.1
      hEpsilonData.2.1 hCandidate.1
      (KP.exists_difference (ZF.modelsKP hZF))
      (KP.exists_intersection (ZF.modelsKP hZF)
        epsilon candidate) with
    hSame | hEpsilonCandidate | hCandidateEpsilon
  · exact Or.inl <|
      hZF.1.eq_of_same_members epsilon candidate hSame
  · exact Or.inr hEpsilonCandidate
  · have hCandidateBound : ℳ.mem candidate bound :=
      hBoundOrdinal.transitive epsilon hEpsilonData.1
        candidate hCandidateEpsilon
    have hCandidateCandidates : ℳ.mem candidate candidates :=
      (hCandidatesSemantic candidate).mpr
        ⟨hCandidateBound, hCandidate⟩
    rcases hLeast candidate hCandidateCandidates with
      hLeastSame | hEpsilonCandidate
    · have hEq :=
        hZF.1.eq_of_same_members epsilon candidate hLeastSame
      subst candidate
      exact False.elim <|
        hEpsilonData.2.1.wellOrder.linear.irrefl
          epsilon hCandidateEpsilon hCandidateEpsilon
    · have hSelf : ℳ.mem epsilon epsilon :=
        hEpsilonData.2.1.transitive candidate
          hCandidateEpsilon epsilon hEpsilonCandidate
      exact False.elim <|
        hEpsilonData.2.1.wellOrder.linear.irrefl
          epsilon hSelf hSelf

/-- 给定 `ω` 后，最小 epsilon 数唯一。 -/
theorem epsilonZero_unique
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω first second : ℳ.Domain}
    (hFirst : ℳ.IsEpsilonZero 𝕀 ω first)
    (hSecond : ℳ.IsEpsilonZero 𝕀 ω second) :
    first = second := by
  rcases hFirst.2 second hSecond.1 with
    hEq | hFirstSecond
  · exact hEq
  · rcases hSecond.2 first hFirst.1 with
      hEq | hSecondFirst
    · exact hEq.symm
    · have hSelf : ℳ.mem first first :=
        hFirst.1.1.transitive second hSecondFirst
          first hFirstSecond
      exact False.elim <|
        hFirst.1.1.wellOrder.linear.irrefl first hSelf hSelf

/-- 给定 `ω` 后，最小 epsilon 数存在且唯一。 -/
theorem epsilonZero_existsUnique
    (hZF : ℳ.Models SetTheory.ZF)
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω : ℳ.Domain} (hω : ℳ.IsOmega ω) :
    ∃ epsilon,
      ℳ.IsEpsilonZero 𝕀 ω epsilon ∧
        ∀ other,
          ℳ.IsEpsilonZero 𝕀 ω other →
            other = epsilon := by
  rcases epsilonZero_exists hZF 𝕀 hω with
    ⟨epsilon, hEpsilon⟩
  exact ⟨epsilon, hEpsilon, fun other hOther =>
    epsilonZero_unique 𝕀 hOther hEpsilon⟩

end ZF

end SetTheory
end YesMetaZFC
