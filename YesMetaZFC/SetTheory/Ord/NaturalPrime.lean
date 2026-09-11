import YesMetaZFC.SetTheory.Ord.PrimePower
import YesMetaZFC.SetTheory.Ord.Arithmetic.Noncommutative
import YesMetaZFC.Automation.HostAvatar.Dispatch
/-!
# 模型内部自然数的素数算术
本文件承接自然数闭包和序数算术递归，先整理自然数范围内的交换律与整除代数，
再证明 Euclid 引理以及不同素数的正指数幂互异。所有关系仍然使用模型内部的
序数算术关系，不把自然数运算提升为元层的全局函数。
-/
namespace YesMetaZFC
namespace SetTheory
universe u
namespace Definitional
namespace Project
namespace BinarySchema
/-- 输出 `left + input` 的直接关系模式。 -/
private def naturalAdditionLeft (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body := Formula.isOrdinalAddition 𝒞 (.bound 0) (.bound 2) (.bound 1)
/-- 输出 `input + left` 的直接关系模式。 -/
private def naturalAdditionRight (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body := Formula.isOrdinalAddition 𝒞 (.bound 0) (.bound 1) (.bound 2)
/-- 输出 `left * input` 的直接关系模式。 -/
private def naturalMultiplicationLeft (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body := Formula.isOrdinalMultiplication 𝒞 (.bound 0) (.bound 2) (.bound 1)
/-- 输出 `input * left` 的直接关系模式。 -/
private def naturalMultiplicationRight (𝒞 : OrderedPairConvention) : BinarySchema 1 where
  body := Formula.isOrdinalMultiplication 𝒞 (.bound 0) (.bound 1) (.bound 2)
/-- `successor * input` 与 `predecessor * input + input` 的关系模式。 -/
private def naturalMultiplicationSuccessorAdd (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := .existsE <| .conj (Formula.isOrdinalMultiplication 𝒞
      Term.newest (.bound 3) (.bound 2)) (Formula.isOrdinalAddition 𝒞 (.bound 1) Term.newest (.bound 2))
/-- 固定后继左因子的乘法关系模式。 -/
private def naturalMultiplicationAtSuccessor (𝒞 : OrderedPairConvention) : BinarySchema 2 where
  body := Formula.isOrdinalMultiplication 𝒞 (.bound 0) (.bound 3) (.bound 1)
end BinarySchema
namespace UnarySchema
/--
固定自然数因子 `factor` 与素数 `prime` 后，筛出所有非零乘数 `multiplier`，
使 `prime ∣ factor * multiplier`。该模式供 Euclid 引理的最小乘数论证复用。
-/
private def natPrimeMultiplier (𝒞 : OrderedPairConvention) : UnarySchema 3 where
  body := .conj (.existsE <| .mem (.bound 0) (.bound 1)) (.existsE <| .conj (Formula.isOrdinalMultiplication 𝒞 (.bound 0) (.bound 3) (.bound 1)) (.conj
        (.mem (.bound 4) (.bound 2)) (.existsE <| .conj (.mem (.bound 0) (.bound 3)) (Formula.isOrdinalMultiplication 𝒞 (.bound 1) (.bound 5) (.bound 0)))))
/--
固定自然数 `base` 与素数 `prime` 后，筛出所有指数 `exponent`，
使 `prime ∣ base ^ exponent`。
-/
private def natPrimePowerExponent (𝒞 : OrderedPairConvention) : UnarySchema 3 where
  body := .existsE <| .conj (Formula.isOrdinalExponentiation 𝒞 (.bound 0) (.bound 4) (.bound 1)) (.conj (.mem (.bound 3) (.bound 2)) (.existsE <| .conj
        (.mem (.bound 0) (.bound 3)) (Formula.isOrdinalMultiplication 𝒞 (.bound 1) (.bound 4) (.bound 0))))
end UnarySchema
end Project
end Definitional
namespace ZF
private theorem naturalAdditionLeft_denote_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (hZF : ℳ.Models SetTheory.ZF) (𝕀 : 𝒞.Interpretation ℳ) (env : Env ℳ 1) (input output : ℳ.Domain) :
    (Definitional.Project.BinarySchema.naturalAdditionLeft 𝒞).denote
        env input output ↔
      ℳ.IsOrdinalAddition 𝕀 output (env.bound 0) input := by
  simp only [Definitional.Project.BinarySchema.naturalAdditionLeft,
    Definitional.Project.BinarySchema.denote,
    Definitional.Project.Formula.satisfies_isOrdinalAddition_iff
      𝕀 hZF.1]
  rfl
private theorem naturalAdditionRight_denote_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (hZF : ℳ.Models SetTheory.ZF) (𝕀 : 𝒞.Interpretation ℳ) (env : Env ℳ 1) (input output : ℳ.Domain) :
    (Definitional.Project.BinarySchema.naturalAdditionRight 𝒞).denote
        env input output ↔
      ℳ.IsOrdinalAddition 𝕀 output input (env.bound 0) := by
  simp only [Definitional.Project.BinarySchema.naturalAdditionRight,
    Definitional.Project.BinarySchema.denote,
    Definitional.Project.Formula.satisfies_isOrdinalAddition_iff
      𝕀 hZF.1]
  rfl
private theorem naturalMultiplicationLeft_denote_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (hZF : ℳ.Models SetTheory.ZF) (𝕀 : 𝒞.Interpretation ℳ) (env : Env ℳ 1) (input output : ℳ.Domain) :
    (Definitional.Project.BinarySchema.naturalMultiplicationLeft 𝒞).denote
        env input output ↔
      ℳ.IsOrdinalMultiplication 𝕀 output (env.bound 0) input := by
  simp only [Definitional.Project.BinarySchema.naturalMultiplicationLeft,
    Definitional.Project.BinarySchema.denote,
    Definitional.Project.Formula.satisfies_isOrdinalMultiplication_iff
      𝕀 hZF.1]
  rfl
private theorem naturalMultiplicationRight_denote_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (hZF : ℳ.Models SetTheory.ZF) (𝕀 : 𝒞.Interpretation ℳ) (env : Env ℳ 1) (input output : ℳ.Domain) :
    (Definitional.Project.BinarySchema.naturalMultiplicationRight 𝒞).denote
        env input output ↔
      ℳ.IsOrdinalMultiplication 𝕀 output input (env.bound 0) := by
  simp only [Definitional.Project.BinarySchema.naturalMultiplicationRight,
    Definitional.Project.BinarySchema.denote,
    Definitional.Project.Formula.satisfies_isOrdinalMultiplication_iff
      𝕀 hZF.1]
  rfl
private theorem naturalMultiplicationSuccessorAdd_denote_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (hZF : ℳ.Models SetTheory.ZF) (𝕀 : 𝒞.Interpretation ℳ) (env : Env ℳ 2) (input output : ℳ.Domain) :
    (Definitional.Project.BinarySchema.naturalMultiplicationSuccessorAdd 𝒞).denote
        env input output ↔
      ∃ previous,
        ℳ.IsOrdinalMultiplication 𝕀
          previous (env.bound 0) input ∧
        ℳ.IsOrdinalAddition 𝕀
          output previous input := by
  simp only [Definitional.Project.BinarySchema.naturalMultiplicationSuccessorAdd,
    Definitional.Project.BinarySchema.denote,
    Definitional.Project.Formula.satisfies_exists_iff,
    Definitional.Project.Formula.satisfies_conj_iff,
    Definitional.Project.Formula.satisfies_isOrdinalMultiplication_iff
      𝕀 hZF.1,
    Definitional.Project.Formula.satisfies_isOrdinalAddition_iff
      𝕀 hZF.1,
    Definitional.Project.Term.eval_bound_zero_push,
    Definitional.Project.Term.eval_bound_one_push,
    Definitional.Project.Term.eval_bound_two_push,
    Definitional.Project.Term.eval_bound_three_push,
    Definitional.Term.eval_newest]
  rfl
private theorem naturalMultiplicationAtSuccessor_denote_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (hZF : ℳ.Models SetTheory.ZF) (𝕀 : 𝒞.Interpretation ℳ) (env : Env ℳ 2) (input output : ℳ.Domain) :
    (Definitional.Project.BinarySchema.naturalMultiplicationAtSuccessor 𝒞).denote
        env input output ↔
      ℳ.IsOrdinalMultiplication 𝕀 output (env.bound 1) input := by
  simp only [Definitional.Project.BinarySchema.naturalMultiplicationAtSuccessor,
    Definitional.Project.BinarySchema.denote,
    Definitional.Project.Formula.satisfies_isOrdinalMultiplication_iff
      𝕀 hZF.1]
  rfl
private theorem natPrimeMultiplier_denote_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (hZF : ℳ.Models SetTheory.ZF) (𝕀 : 𝒞.Interpretation ℳ) (env : Env ℳ 3) (multiplier : ℳ.Domain) :
    (Definitional.Project.UnarySchema.natPrimeMultiplier 𝒞).denote
        env multiplier ↔ (∃ member, ℳ.mem member multiplier) ∧
        ∃ product,
          ℳ.IsOrdinalMultiplication 𝕀
            product (env.bound 1) multiplier ∧
          ℳ.IsNaturalDivisor 𝕀 (env.bound 0) (env.bound 2) product := by
  simp only [Definitional.Project.UnarySchema.natPrimeMultiplier,
    Definitional.Project.UnarySchema.denote,
    Definitional.Project.Formula.satisfies_conj_iff,
    Definitional.Project.Formula.satisfies_exists_iff,
    Definitional.Project.Formula.satisfies_mem_iff,
    Definitional.Project.Formula.satisfies_isOrdinalMultiplication_iff
      𝕀 hZF.1,
    Definitional.Project.Term.eval_bound,
    Structure.IsNaturalDivisor]
  rfl
private theorem natPrimePowerExponent_denote_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention} (hZF : ℳ.Models SetTheory.ZF) (𝕀 : 𝒞.Interpretation ℳ) (env : Env ℳ 3) (exponent : ℳ.Domain) :
    (Definitional.Project.UnarySchema.natPrimePowerExponent 𝒞).denote
        env exponent ↔
      ∃ power,
        ℳ.IsOrdinalExponentiation 𝕀
          power (env.bound 2) exponent ∧
        ℳ.IsNaturalDivisor 𝕀 (env.bound 0) (env.bound 1) power := by
  simp only [Definitional.Project.UnarySchema.natPrimePowerExponent,
    Definitional.Project.UnarySchema.denote,
    Definitional.Project.Formula.satisfies_conj_iff,
    Definitional.Project.Formula.satisfies_exists_iff,
    Definitional.Project.Formula.satisfies_mem_iff,
    Definitional.Project.Formula.satisfies_isOrdinalMultiplication_iff
      𝕀 hZF.1,
    Definitional.Project.Formula.satisfies_isOrdinalExponentiation_iff
      𝕀 hZF.1,
    Definitional.Project.Term.eval_bound,
    Structure.IsNaturalDivisor]
  rfl
end ZF
namespace Structure
/-- 左参数取后继时，自然数加法值也是原值的后继。 -/
theorem natural_add_left_successor
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω predecessor successor right previous value : ℳ.Domain} (hω : ℳ.IsOmega ω) (hPredecessor : ℳ.mem predecessor ω)
    (hSuccessor : ℳ.SuccessorOf successor predecessor) (hRight : ℳ.mem right ω) (hPrevious : ℳ.IsOrdinalAddition 𝕀 previous predecessor right)
    (hValue : ℳ.IsOrdinalAddition 𝕀 value successor right) :
    ℳ.SuccessorOf value previous := by
  have hPredecessorOrdinal :=
    hω.members_areOrdinals hZF predecessor hPredecessor
  have hRightOrdinal :=
    hω.members_areOrdinals hZF right hRight
  rcases hω.exists_ordinalOne_mem with
    ⟨one, hOne, hOneOmega⟩
  have hOneOrdinal :=
    KP.ordinalOne_isOrdinal (ZF.modelsKP hZF) hOne
  rcases ZF.ordinalAddition_existsUnique hZF 𝕀 predecessor hOneOrdinal with
    ⟨successorValue, hSuccessorValue, _⟩
  rcases hOne with ⟨zero, hZero, hOneSuccessor⟩
  have hSuccessorValueData := (ZF.ordinalAddition_successor_iff
      hZF 𝕀 (Structure.IsOrdinal.of_no_members hZero)
        hOneSuccessor).mp
      hSuccessorValue
  rcases hSuccessorValueData with
    ⟨successorPrevious, hSuccessorPrevious, hSuccessorValueSucc⟩
  have hSuccessorPreviousEq := (ZF.ordinalAddition_zero_iff hZF 𝕀 hZero).mp
      hSuccessorPrevious
  have hSuccessorValueSuccessor :
      ℳ.SuccessorOf successorValue predecessor := by
    simpa [hSuccessorPreviousEq] using hSuccessorValueSucc
  have hSuccessorValueEq : successorValue = successor :=
    SuccessorOf.eq hZF.1 hSuccessorValueSuccessor hSuccessor
  have hPredecessorOne :
      ℳ.IsOrdinalAddition 𝕀 successor predecessor one := by
    simpa [hSuccessorValueEq] using hSuccessorValue
  rcases ZF.ordinalAddition_existsUnique hZF 𝕀 one hRightOrdinal with
    ⟨oneRight, hOneRight, _⟩
  have hOneRightSuccessor :=
    ZF.ordinalAddition_one_isSuccessor_on_omega
      hZF 𝕀 hω ⟨zero, hZero, hOneSuccessor⟩ right hRight
        oneRight hOneRight
  have hOneRightOrdinal :=
    ZF.ordinalAddition_isOrdinal hZF 𝕀 hOneOrdinal hRightOrdinal hOneRight
  rcases ZF.ordinalAddition_existsUnique hZF 𝕀 predecessor hOneRightOrdinal with
    ⟨rightAssociated, hRightAssociated, _⟩
  have hValueEq :=
    ZF.ordinalAddition_assoc hZF 𝕀
      hPredecessorOrdinal hOneOrdinal hRightOrdinal
      hPredecessorOne hOneRight hRightAssociated hValue
  have hValueAssociated :
      ℳ.IsOrdinalAddition 𝕀 value predecessor oneRight := by
    simpa [hValueEq] using hRightAssociated
  rcases (ZF.ordinalAddition_successor_iff
      hZF 𝕀 hRightOrdinal hOneRightSuccessor).mp
      hValueAssociated with
    ⟨candidatePrevious, hCandidatePrevious, hCandidateSuccessor⟩
  rcases ZF.ordinalAddition_existsUnique hZF 𝕀 predecessor hRightOrdinal with
    ⟨selectedPrevious, hSelectedPrevious, hPreviousUnique⟩
  have hCandidatePreviousEq : candidatePrevious = previous := (hPreviousUnique candidatePrevious hCandidatePrevious).trans
      (hPreviousUnique previous hPrevious).symm
  subst candidatePrevious
  exact hCandidateSuccessor
/-- 作为后续整除证明的公共接口：自然数加法在模型内部交换。 -/
theorem natural_add_comm
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω left right first second : ℳ.Domain} (hω : ℳ.IsOmega ω) (hLeft : ℳ.mem left ω) (hRight : ℳ.mem right ω) (hFirst : ℳ.IsOrdinalAddition 𝕀 first left right)
    (hSecond : ℳ.IsOrdinalAddition 𝕀 second right left) :
    first = second := by
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  let property : ℳ.Domain → Prop := fun current =>
    ∀ firstValue secondValue,
      ℳ.IsOrdinalAddition 𝕀 firstValue left current →
      ℳ.IsOrdinalAddition 𝕀 secondValue current left →
        firstValue = secondValue
  have hProperty : ∀ current, ℳ.mem current ω → property current := by
    apply hω.induction property
    · rcases ZF.separation_exists_d hZF ((Definitional.Project.BinarySchema.naturalAdditionLeft 𝒞).agreeAt
            (Definitional.Project.BinarySchema.naturalAdditionRight 𝒞))
          env ω with
        ⟨counterexamples, hCounterexamples⟩
      refine ⟨counterexamples, fun current => ?_⟩
      rw [hCounterexamples current]
      simp only [Definitional.Project.Formula.satisfies_agreeAt_iff hZF.1,
        property]
      change (ℳ.mem current ω ∧ (∀ firstValue secondValue, (Definitional.Project.BinarySchema.naturalAdditionLeft 𝒞).denote
                env current firstValue → (Definitional.Project.BinarySchema.naturalAdditionRight 𝒞).denote
                env current secondValue →
              firstValue = secondValue)) ↔ (ℳ.mem current ω ∧ property current)
      constructor
      · rintro ⟨hCurrent, hNot⟩
        refine ⟨hCurrent, ?_⟩
        intro firstValue secondValue hFirstValue hSecondValue
        exact hNot firstValue secondValue ((ZF.naturalAdditionLeft_denote_iff hZF 𝕀 env
            current firstValue).mpr hFirstValue) ((ZF.naturalAdditionRight_denote_iff hZF 𝕀 env
            current secondValue).mpr hSecondValue)
      · rintro ⟨hCurrent, hNot⟩
        refine ⟨hCurrent, ?_⟩
        intro firstValue secondValue hFirstValue hSecondValue
        exact hNot firstValue secondValue ((ZF.naturalAdditionLeft_denote_iff hZF 𝕀 env
            current firstValue).mp hFirstValue) ((ZF.naturalAdditionRight_denote_iff hZF 𝕀 env
            current secondValue).mp hSecondValue)
    · intro empty hEmpty firstValue secondValue hFirstValue hSecondValue
      have hFirstEq := (ZF.ordinalAddition_zero_iff hZF 𝕀 hEmpty).mp hFirstValue
      have hSecondEq :=
        ZF.ordinalAddition_empty_left hZF 𝕀 hEmpty
          left (hω.members_areOrdinals hZF left hLeft)
          secondValue hSecondValue
      exact hFirstEq.trans hSecondEq.symm
    · intro predecessor hPredecessor hPrevious
        successor hSuccessor firstValue secondValue
        hFirstValue hSecondValue
      have hPredecessorOrdinal :=
        hω.members_areOrdinals hZF predecessor hPredecessor
      rcases (ZF.ordinalAddition_successor_iff
          hZF 𝕀 hPredecessorOrdinal hSuccessor).mp hFirstValue with
        ⟨firstPrevious, hFirstPrevious, hFirstSuccessor⟩
      have hLeftOrdinal := hω.members_areOrdinals hZF left hLeft
      rcases ZF.ordinalAddition_existsUnique hZF 𝕀 predecessor hLeftOrdinal with
        ⟨secondPrevious, hSecondPrevious, _⟩
      have hSecondSuccessor :=
        natural_add_left_successor hZF 𝕀 hω
          hPredecessor hSuccessor hLeft
          hSecondPrevious hSecondValue
      have hSecondPreviousEq :=
        hPrevious firstPrevious secondPrevious
          hFirstPrevious hSecondPrevious
      subst secondPrevious
      exact Structure.SuccessorOf.eq hZF.1
        hFirstSuccessor hSecondSuccessor
  exact hProperty right hRight first second hFirst hSecond
/-- 两个自然数分别取后继后，加法值仍可交换。 -/
theorem natural_add_successor_swap
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω left right leftSuccessor rightSuccessor
      baseFirst baseSecond first second : ℳ.Domain} (hω : ℳ.IsOmega ω) (hLeft : ℳ.mem left ω) (hRight : ℳ.mem right ω)
    (hLeftSuccessor : ℳ.SuccessorOf leftSuccessor left) (hRightSuccessor : ℳ.SuccessorOf rightSuccessor right)
    (hBaseFirst : ℳ.IsOrdinalAddition 𝕀 baseFirst left right) (hBaseSecond : ℳ.IsOrdinalAddition 𝕀 baseSecond right left)
    (hFirst : ℳ.IsOrdinalAddition 𝕀 first left rightSuccessor) (hSecond : ℳ.IsOrdinalAddition 𝕀 second right leftSuccessor) :
    first = second := by
  have hLeftOrdinal := hω.members_areOrdinals hZF left hLeft
  have hRightOrdinal := hω.members_areOrdinals hZF right hRight
  have hBaseEq :=
    natural_add_comm hZF 𝕀 hω hLeft hRight hBaseFirst hBaseSecond
  rcases (ZF.ordinalAddition_successor_iff
      hZF 𝕀 hRightOrdinal hRightSuccessor).mp hFirst with
    ⟨firstPrevious, hFirstPrevious, hFirstSuccessor⟩
  rcases (ZF.ordinalAddition_successor_iff
      hZF 𝕀 hLeftOrdinal hLeftSuccessor).mp hSecond with
    ⟨secondPrevious, hSecondPrevious, hSecondSuccessor⟩
  rcases ZF.ordinalAddition_existsUnique hZF 𝕀 left hRightOrdinal with
    ⟨_, _, hFirstUnique⟩
  rcases ZF.ordinalAddition_existsUnique hZF 𝕀 right hLeftOrdinal with
    ⟨_, _, hSecondUnique⟩
  have hFirstPreviousEq : firstPrevious = baseFirst := (hFirstUnique firstPrevious hFirstPrevious).trans (hFirstUnique baseFirst hBaseFirst).symm
  have hSecondPreviousEq : secondPrevious = baseSecond := (hSecondUnique secondPrevious hSecondPrevious).trans (hSecondUnique baseSecond hBaseSecond).symm
  subst firstPrevious
  subst secondPrevious
  have hBaseEq' : baseFirst = baseSecond :=
    hBaseEq
  subst baseSecond
  exact SuccessorOf.eq hZF.1 hFirstSuccessor hSecondSuccessor
/-- 乘法左因子的后继递推在自然数右参数上成立。 -/
theorem natural_mul_left_successor_add
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω predecessor successor right previous value sum : ℳ.Domain} (hω : ℳ.IsOmega ω) (hPredecessor : ℳ.mem predecessor ω)
    (hSuccessor : ℳ.SuccessorOf successor predecessor) (hRight : ℳ.mem right ω) (hPrevious : ℳ.IsOrdinalMultiplication 𝕀
      previous predecessor right) (hValue : ℳ.IsOrdinalMultiplication 𝕀
      value successor right) (hSum : ℳ.IsOrdinalAddition 𝕀 sum previous right) :
    value = sum := by
  have hPredecessorOrdinal :=
    hω.members_areOrdinals hZF predecessor hPredecessor
  have hSuccessorOrdinal :=
    KP.successor_isOrdinal (ZF.modelsKP hZF)
      hPredecessorOrdinal hSuccessor
  let env : Env ℳ 2 := {
    bound := fun
      | 0 => predecessor
      | 1 => successor
    free := fun _ => Classical.choice ℳ.nonempty
  }
  let property : ℳ.Domain → Prop := fun current =>
    ∀ first second,
      ℳ.IsOrdinalMultiplication 𝕀
        first successor current → (∃ previous,
        ℳ.IsOrdinalMultiplication 𝕀
          previous predecessor current ∧
        ℳ.IsOrdinalAddition 𝕀 second previous current) →
      first = second
  have hProperty : ∀ current, ℳ.mem current ω → property current := by
    apply hω.induction property
    · rcases ZF.separation_exists_d hZF ((Definitional.Project.BinarySchema.naturalMultiplicationAtSuccessor
            𝒞).agreeAt (Definitional.Project.BinarySchema.naturalMultiplicationSuccessorAdd
              𝒞))
          env ω with
        ⟨closed, hClosed⟩
      refine ⟨closed, fun current => ?_⟩
      rw [hClosed current]
      simp only [Definitional.Project.Formula.satisfies_agreeAt_iff hZF.1,
        property]
      change (ℳ.mem current ω ∧ (∀ first second, (Definitional.Project.BinarySchema.naturalMultiplicationAtSuccessor
              𝒞).denote env current first → (Definitional.Project.BinarySchema.naturalMultiplicationSuccessorAdd
              𝒞).denote env current second →
              first = second)) ↔ (ℳ.mem current ω ∧ property current)
      constructor
      · rintro ⟨hCurrent, hAgree⟩
        refine ⟨hCurrent, ?_⟩
        intro first second hFirst hSecond
        exact hAgree first second ((ZF.naturalMultiplicationAtSuccessor_denote_iff
            hZF 𝕀 env current first).mpr hFirst) ((ZF.naturalMultiplicationSuccessorAdd_denote_iff
            hZF 𝕀 env current second).mpr hSecond)
      · rintro ⟨hCurrent, hProperty⟩
        refine ⟨hCurrent, ?_⟩
        intro first second hFirst hSecond
        exact hProperty first second ((ZF.naturalMultiplicationAtSuccessor_denote_iff
            hZF 𝕀 env current first).mp hFirst) ((ZF.naturalMultiplicationSuccessorAdd_denote_iff
            hZF 𝕀 env current second).mp hSecond)
    · intro empty hEmpty first second hFirst hSecond
      have hFirstEmpty := (ZF.ordinalMultiplication_zero_iff
          hZF 𝕀 hSuccessorOrdinal hEmpty).mp hFirst
      rcases hSecond with
        ⟨previousValue, hPreviousValue, hSecondAddition⟩
      have hPreviousEmpty := (ZF.ordinalMultiplication_zero_iff
          hZF 𝕀 hPredecessorOrdinal hEmpty).mp hPreviousValue
      have hSecondEq := (ZF.ordinalAddition_zero_iff hZF 𝕀 hEmpty).mp
          hSecondAddition
      apply hZF.1.eq_of_same_members
      intro member
      exact iff_of_false (by simp [hFirstEmpty]) (by simp [hSecondEq, hPreviousEmpty])
    · intro currentPredecessor hCurrentPredecessor hPreviousProperty
        currentSuccessor hCurrentSuccessor first second
        hFirst hSecond
      have hCurrentPredecessorOrdinal :=
        hω.members_areOrdinals hZF
          currentPredecessor hCurrentPredecessor
      have hCurrentSuccessorOrdinal :=
        KP.successor_isOrdinal (ZF.modelsKP hZF)
          hCurrentPredecessorOrdinal hCurrentSuccessor
      rcases (ZF.ordinalMultiplication_successor_iff
          hZF 𝕀 hSuccessorOrdinal
          hCurrentPredecessorOrdinal hCurrentSuccessor).mp hFirst with
        ⟨firstPrevious, hFirstPrevious, hFirstAddition⟩
      rcases hSecond with
        ⟨secondPrevious, hSecondPrevious, hSecondAddition⟩
      rcases (ZF.ordinalMultiplication_successor_iff
          hZF 𝕀 hPredecessorOrdinal
          hCurrentPredecessorOrdinal hCurrentSuccessor).mp
          hSecondPrevious with
        ⟨basePrevious, hBasePrevious, hSecondPreviousAddition⟩
      rcases ZF.ordinalAddition_existsUnique hZF 𝕀
          basePrevious hCurrentPredecessorOrdinal with
        ⟨middle, hMiddle, _⟩
      have hBasePreviousOrdinal :=
        ZF.ordinalMultiplication_isOrdinal hZF 𝕀
          hPredecessorOrdinal hCurrentPredecessorOrdinal
          hBasePrevious
      have hPreviousEquality :=
        hPreviousProperty firstPrevious middle hFirstPrevious
          ⟨basePrevious, hBasePrevious, hMiddle⟩
      rcases ZF.ordinalAddition_existsUnique hZF 𝕀
          currentPredecessor hSuccessorOrdinal with
        ⟨innerFirst, hInnerFirst, _⟩
      rcases ZF.ordinalAddition_existsUnique hZF 𝕀
          predecessor hCurrentSuccessorOrdinal with
        ⟨innerSecond, hInnerSecond, _⟩
      rcases ZF.ordinalAddition_existsUnique hZF 𝕀
          currentPredecessor hPredecessorOrdinal with
        ⟨baseCurrent, hBaseCurrent, _⟩
      rcases ZF.ordinalAddition_existsUnique hZF 𝕀
          predecessor hCurrentPredecessorOrdinal with
        ⟨baseSwap, hBaseSwap, _⟩
      have hInnerEquality :=
        natural_add_successor_swap hZF 𝕀 hω
          hCurrentPredecessor hPredecessor
          hCurrentSuccessor hSuccessor
          hBaseCurrent hBaseSwap hInnerFirst hInnerSecond
      have hInnerFirstOrdinal :=
        ZF.ordinalAddition_isOrdinal hZF 𝕀
          hCurrentPredecessorOrdinal hSuccessorOrdinal hInnerFirst
      rcases ZF.ordinalAddition_existsUnique hZF 𝕀
          basePrevious hInnerFirstOrdinal with
        ⟨leftAssociated, hLeftAssociated, _⟩
      have hInnerSecondOrdinal :=
        ZF.ordinalAddition_isOrdinal hZF 𝕀
          hPredecessorOrdinal hCurrentSuccessorOrdinal hInnerSecond
      rcases ZF.ordinalAddition_existsUnique hZF 𝕀
          basePrevious hInnerSecondOrdinal with
        ⟨rightAssociated, hRightAssociated, _⟩
      have hFirstAssocEq :=
        let hFirstAddition' :
            ℳ.IsOrdinalAddition 𝕀 first middle successor := by
          simpa [hPreviousEquality] using hFirstAddition
        ZF.ordinalAddition_assoc hZF 𝕀
          hBasePreviousOrdinal
          hCurrentPredecessorOrdinal hSuccessorOrdinal
          hMiddle hInnerFirst hLeftAssociated hFirstAddition'
      have hSecondAssocEq :=
        ZF.ordinalAddition_assoc hZF 𝕀
          hBasePreviousOrdinal
          hPredecessorOrdinal hCurrentSuccessorOrdinal
          hSecondPreviousAddition hInnerSecond
          hRightAssociated hSecondAddition
      have hRightAssociated' :
          ℳ.IsOrdinalAddition 𝕀 rightAssociated
            basePrevious innerFirst := by
        simpa [hInnerEquality] using hRightAssociated
      rcases ZF.ordinalAddition_existsUnique hZF 𝕀
          basePrevious hInnerFirstOrdinal with
        ⟨selectedAssociated, hSelectedAssociated,
          hAssociatedUnique⟩
      have hAssociatedEq : leftAssociated = rightAssociated := (hAssociatedUnique leftAssociated hLeftAssociated).trans
          (hAssociatedUnique rightAssociated hRightAssociated').symm
      exact hFirstAssocEq.symm.trans (hAssociatedEq.trans hSecondAssocEq)
  exact hProperty right hRight value sum hValue
    ⟨previous, hPrevious, hSum⟩
/-- 两个自然数的模型内部乘法交换。 -/
theorem natural_mul_comm
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω left right first second : ℳ.Domain} (hω : ℳ.IsOmega ω) (hLeft : ℳ.mem left ω) (hRight : ℳ.mem right ω) (hFirst : ℳ.IsOrdinalMultiplication 𝕀
      first left right) (hSecond : ℳ.IsOrdinalMultiplication 𝕀
      second right left) :
    first = second := by
  have hLeftOrdinal := hω.members_areOrdinals hZF left hLeft
  let env : Env ℳ 1 := {
    bound := fun _ => left
    free := fun _ => Classical.choice ℳ.nonempty
  }
  let property : ℳ.Domain → Prop := fun current =>
    ∀ firstValue secondValue,
      ℳ.IsOrdinalMultiplication 𝕀
        firstValue left current →
      ℳ.IsOrdinalMultiplication 𝕀
        secondValue current left →
      firstValue = secondValue
  have hProperty : ∀ current, ℳ.mem current ω → property current := by
    apply hω.induction property
    · rcases ZF.separation_exists_d hZF ((Definitional.Project.BinarySchema.naturalMultiplicationLeft
            𝒞).agreeAt (Definitional.Project.BinarySchema.naturalMultiplicationRight
              𝒞))
          env ω with
        ⟨closed, hClosed⟩
      refine ⟨closed, fun current => ?_⟩
      rw [hClosed current]
      simp only [Definitional.Project.Formula.satisfies_agreeAt_iff hZF.1,
        property]
      change (ℳ.mem current ω ∧ (∀ firstValue secondValue, (Definitional.Project.BinarySchema.naturalMultiplicationLeft
              𝒞).denote env current firstValue → (Definitional.Project.BinarySchema.naturalMultiplicationRight
              𝒞).denote env current secondValue →
              firstValue = secondValue)) ↔ (ℳ.mem current ω ∧ property current)
      constructor
      · rintro ⟨hCurrent, hAgree⟩
        refine ⟨hCurrent, ?_⟩
        intro firstValue secondValue hFirstValue hSecondValue
        exact hAgree firstValue secondValue ((ZF.naturalMultiplicationLeft_denote_iff
            hZF 𝕀 env current firstValue).mpr hFirstValue) ((ZF.naturalMultiplicationRight_denote_iff
            hZF 𝕀 env current secondValue).mpr hSecondValue)
      · rintro ⟨hCurrent, hProperty⟩
        refine ⟨hCurrent, ?_⟩
        intro firstValue secondValue hFirstValue hSecondValue
        exact hProperty firstValue secondValue ((ZF.naturalMultiplicationLeft_denote_iff
            hZF 𝕀 env current firstValue).mp hFirstValue) ((ZF.naturalMultiplicationRight_denote_iff
            hZF 𝕀 env current secondValue).mp hSecondValue)
    · intro empty hEmpty firstValue secondValue
        hFirstValue hSecondValue
      have hFirstEmpty := (ZF.ordinalMultiplication_zero_iff
          hZF 𝕀 hLeftOrdinal hEmpty).mp hFirstValue
      have hSecondEmpty :=
        ZF.ordinalMultiplication_empty_left hZF 𝕀 hEmpty
          left hLeftOrdinal secondValue hSecondValue
      apply hZF.1.eq_of_same_members
      intro member
      exact iff_of_false (by simp [hFirstEmpty]) (hSecondEmpty member)
    · intro predecessor hPredecessor hPrevious
        successor hSuccessor firstValue secondValue
        hFirstValue hSecondValue
      have hPredecessorOrdinal :=
        hω.members_areOrdinals hZF predecessor hPredecessor
      have hSuccessorOrdinal :=
        KP.successor_isOrdinal (ZF.modelsKP hZF)
          hPredecessorOrdinal hSuccessor
      rcases (ZF.ordinalMultiplication_successor_iff
          hZF 𝕀 hLeftOrdinal hPredecessorOrdinal hSuccessor).mp
          hFirstValue with
        ⟨firstPrevious, hFirstPrevious, hFirstAddition⟩
      rcases ZF.ordinalMultiplication_existsUnique hZF 𝕀
          predecessor hLeftOrdinal with
        ⟨secondPrevious, hSecondPrevious, _⟩
      rcases ZF.ordinalAddition_existsUnique hZF 𝕀
          secondPrevious hLeftOrdinal with
        ⟨secondSum, hSecondSum, _⟩
      have hSecondEq :=
        natural_mul_left_successor_add hZF 𝕀 hω
          hPredecessor hSuccessor hLeft
          hSecondPrevious hSecondValue hSecondSum
      have hPreviousEq :=
        hPrevious firstPrevious secondPrevious
          hFirstPrevious hSecondPrevious
      have hFirstAddition' :
          ℳ.IsOrdinalAddition 𝕀 firstValue secondPrevious left := by
        simpa [hPreviousEq] using hFirstAddition
      rcases ZF.ordinalAddition_existsUnique hZF 𝕀
          secondPrevious hLeftOrdinal with
        ⟨selected, hSelected, hSelectedUnique⟩
      have hFirstEq : firstValue = secondSum := (hSelectedUnique firstValue hFirstAddition').trans (hSelectedUnique secondSum hSecondSum).symm
      exact hFirstEq.trans hSecondEq.symm
  exact hProperty right hRight first second hFirst hSecond
/-- 自然数的非零序数除法所产生的商仍属于 `ω`。 -/
theorem nat_div_quotient_mem_omega
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω dividend divisor quotient remainder : ℳ.Domain} (hω : ℳ.IsOmega ω) (hDividend : ℳ.mem dividend ω) (hDivisor : ℳ.mem divisor ω)
    (hDivisorNonempty : ∃ member, ℳ.mem member divisor) (hDivision :
      ℳ.IsOrdinalDivision 𝕀
        dividend divisor quotient remainder) :
    ℳ.mem quotient ω := by
  rcases hDivision with
    ⟨hQuotientOrdinal, hRemainderDivisor,
      product, hProduct, hDecomposition⟩
  have hDividendOrdinal :=
    hω.members_areOrdinals hZF dividend hDividend
  have hDivisorOrdinal :=
    hω.members_areOrdinals hZF divisor hDivisor
  have hQuotientProduct :=
    ZF.ordinalMultiplication_right_eq_or_mem
      hZF 𝕀 hDivisorOrdinal hDivisorNonempty
      hQuotientOrdinal hProduct
  have hProductDividend :=
    ZF.ordinalAddition_left_eq_or_mem
      hZF 𝕀 (hDivisorOrdinal.mem hRemainderDivisor)
      hDecomposition
  rcases hQuotientProduct with hQuotientEq | hQuotientProduct
  · rcases hProductDividend with hProductEq | hProductDividend
    · simpa [hQuotientEq, hProductEq] using hDividend
    · exact hω.transitive hZF dividend hDividend quotient <| by
        simpa [hQuotientEq] using hProductDividend
  · rcases hProductDividend with hProductEq | hProductDividend
    · exact hω.transitive hZF dividend hDividend quotient <| by
        simpa [hProductEq] using hQuotientProduct
    · exact hω.transitive hZF dividend hDividend quotient <|
        hDividendOrdinal.transitive
          product hProductDividend quotient hQuotientProduct
/-- 自然数整除关系对被除数的右乘封闭。 -/
theorem nat_dvd_mul_right
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω divisor factor right product : ℳ.Domain} (hω : ℳ.IsOmega ω) (hRight : ℳ.mem right ω) (hProduct :
      ℳ.IsOrdinalMultiplication 𝕀 product factor right) (hDivides :
      ℳ.IsNaturalDivisor 𝕀 ω divisor factor) :
    ℳ.IsNaturalDivisor 𝕀 ω divisor product := by
  rcases hDivides with
    ⟨hDivisor, quotient, hQuotient, hFactor⟩
  have hDivisorOrdinal :=
    hω.members_areOrdinals hZF divisor hDivisor
  have hQuotientOrdinal :=
    hω.members_areOrdinals hZF quotient hQuotient
  have hRightOrdinal :=
    hω.members_areOrdinals hZF right hRight
  rcases ZF.ordinalMultiplication_existsUnique
      hZF 𝕀 quotient hRightOrdinal with
    ⟨combinedQuotient, hCombinedQuotient, _⟩
  have hCombinedQuotientOmega :=
    ZF.ordinalMultiplication_mem_omega
      hZF 𝕀 hω hQuotient hRight hCombinedQuotient
  rcases ZF.ordinalMultiplication_existsUnique
      hZF 𝕀 divisor (ZF.ordinalMultiplication_isOrdinal
        hZF 𝕀 hQuotientOrdinal hRightOrdinal
        hCombinedQuotient) with
    ⟨combinedProduct, hCombinedProduct, _⟩
  have hAssociated :=
    ZF.ordinalMultiplication_assoc
      hZF 𝕀 hDivisorOrdinal hQuotientOrdinal hRightOrdinal
      hFactor hCombinedQuotient hCombinedProduct hProduct
  refine ⟨hDivisor, combinedQuotient,
    hCombinedQuotientOmega, ?_⟩
  simpa [hAssociated] using hCombinedProduct
/--
若非零自然数同时整除一个和及其左项，则它也整除右余项。
这是 Euclid 最小乘数下降中使用的加法消去律。
-/
theorem nat_dvd_add_right_cancel
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω divisor left right sum : ℳ.Domain} (hω : ℳ.IsOmega ω) (hDivisorNonempty : ∃ member, ℳ.mem member divisor) (hLeft : ℳ.mem left ω) (hRight : ℳ.mem right ω)
    (hSum : ℳ.mem sum ω) (hAddition : ℳ.IsOrdinalAddition 𝕀 sum left right) (hDividesLeft : ℳ.IsNaturalDivisor 𝕀 ω divisor left)
    (hDividesSum : ℳ.IsNaturalDivisor 𝕀 ω divisor sum) :
    ℳ.IsNaturalDivisor 𝕀 ω divisor right := by
  rcases hDividesLeft with
    ⟨hDivisor, leftQuotient, hLeftQuotient, hLeftProduct⟩
  rcases hDividesSum with
    ⟨_, sumQuotient, hSumQuotient, hSumProduct⟩
  have hDivisorOrdinal :=
    hω.members_areOrdinals hZF divisor hDivisor
  have hLeftOrdinal :=
    hω.members_areOrdinals hZF left hLeft
  have hRightOrdinal :=
    hω.members_areOrdinals hZF right hRight
  have hSumOrdinal :=
    hω.members_areOrdinals hZF sum hSum
  have hLeftQuotientOrdinal :=
    hω.members_areOrdinals hZF leftQuotient hLeftQuotient
  have hSumQuotientOrdinal :=
    hω.members_areOrdinals hZF sumQuotient hSumQuotient
  have hQuotientOrder :
      leftQuotient = sumQuotient ∨
        ℳ.mem leftQuotient sumQuotient := by
    rcases Structure.IsOrdinal.trichotomy hZF.1
        hLeftQuotientOrdinal hSumQuotientOrdinal (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF)
          leftQuotient sumQuotient) with
      hSame | hLeftSum | hSumLeft
    · exact Or.inl <|
        hZF.1.eq_of_same_members
          leftQuotient sumQuotient hSame
    · exact Or.inr hLeftSum
    · have hSumLeftProduct :=
        ZF.ordinalMultiplication_isIncreasingOnOrdinals
          hZF 𝕀 hDivisorOrdinal hDivisorNonempty
          sumQuotient leftQuotient
          hSumQuotientOrdinal hLeftQuotientOrdinal hSumLeft
          sum left hSumProduct hLeftProduct
      rcases ZF.ordinalAddition_left_eq_or_mem
          hZF 𝕀 hRightOrdinal hAddition with
        hLeftEq | hLeftSum
      · subst left
        exact False.elim <|
          hSumOrdinal.wellOrder.linear.irrefl
            sum hSumLeftProduct hSumLeftProduct
      · have hSelf :=
          hSumOrdinal.transitive
            left hLeftSum sum hSumLeftProduct
        exact False.elim <|
          hSumOrdinal.wellOrder.linear.irrefl sum hSelf hSelf
  rcases hω.1.1 with ⟨zero, hZero, hZeroOmega⟩
  rcases hQuotientOrder with hQuotientEq | hQuotientMem
  · subst sumQuotient
    have hZeroProduct :
        ℳ.IsOrdinalMultiplication 𝕀 zero divisor zero := (ZF.ordinalMultiplication_zero_iff
        hZF 𝕀 hDivisorOrdinal hZero).mpr hZero
    have hLeftPlusZero :
        ℳ.IsOrdinalAddition 𝕀 left left zero := (ZF.ordinalAddition_zero_iff hZF 𝕀 hZero).mpr rfl
    have hProductEq : sum = left := by
      rcases ZF.ordinalMultiplication_existsUnique
          hZF 𝕀 divisor hLeftQuotientOrdinal with
        ⟨selected, _, hUnique⟩
      exact (hUnique sum hSumProduct).trans (hUnique left hLeftProduct).symm
    subst sum
    have hRightEq : right = zero :=
      ZF.ordinalAddition_right_injective
        hZF 𝕀 hLeftOrdinal hRightOrdinal (Structure.IsOrdinal.of_no_members hZero)
        hAddition hLeftPlusZero
    subst right
    exact ⟨hDivisor, zero, hZeroOmega, hZeroProduct⟩
  · rcases ZF.ordinalAddition_existsUnique_rightRemainder
        hZF 𝕀 hLeftQuotientOrdinal hSumQuotientOrdinal
        hQuotientMem with
      ⟨rightQuotient, hQuotientAddition, _⟩
    have hRightQuotientOrdinal :=
      Structure.IsOrdinalAddition.right_isOrdinal
        hQuotientAddition
    have hRightQuotientOrder :=
      ZF.ordinalAddition_right_eq_or_mem
        hZF 𝕀 hLeftQuotientOrdinal hRightQuotientOrdinal
        hQuotientAddition
    have hRightQuotientOmega : ℳ.mem rightQuotient ω := by
      rcases hRightQuotientOrder with hEq | hMem
      · simpa [hEq] using hSumQuotient
      · exact hω.transitive hZF
          sumQuotient hSumQuotient rightQuotient hMem
    rcases ZF.ordinalMultiplication_existsUnique
        hZF 𝕀 divisor hRightQuotientOrdinal with
      ⟨rightProduct, hRightProduct, _⟩
    rcases ZF.ordinalAddition_existsUnique
        hZF 𝕀 left (ZF.ordinalMultiplication_isOrdinal
          hZF 𝕀 hDivisorOrdinal hRightQuotientOrdinal
          hRightProduct) with
      ⟨distributed, hDistributed, _⟩
    have hDistribution :=
      ZF.ordinalMultiplication_add
        hZF 𝕀 hDivisorOrdinal
        hLeftQuotientOrdinal hRightQuotientOrdinal
        hQuotientAddition hSumProduct
        hLeftProduct hRightProduct hDistributed
    have hDistributedAddition :
        ℳ.IsOrdinalAddition 𝕀 sum left rightProduct := by
      simpa [hDistribution] using hDistributed
    have hRightEq : right = rightProduct :=
      ZF.ordinalAddition_right_injective
        hZF 𝕀 hLeftOrdinal hRightOrdinal (ZF.ordinalMultiplication_isOrdinal
          hZF 𝕀 hDivisorOrdinal hRightQuotientOrdinal
          hRightProduct)
        hAddition hDistributedAddition
    subst right
    exact ⟨hDivisor, rightQuotient,
      hRightQuotientOmega, hRightProduct⟩
/--
设 `multiplier = blockBase * quotient + remainder`。若 `divisor` 同时整除
`factor * blockBase` 与 `factor * multiplier`，则它也整除
`factor * remainder`。该接口封装 Euclid 下降中的分配律计算。
-/
theorem nat_dvd_mul_remainder
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω divisor factor blockBase multiplier quotient remainder
      factorBlock block total : ℳ.Domain} (hω : ℳ.IsOmega ω) (hDivisorNonempty : ∃ member, ℳ.mem member divisor) (hFactor : ℳ.mem factor ω)
    (hBlockBase : ℳ.mem blockBase ω) (hMultiplier : ℳ.mem multiplier ω) (hQuotient : ℳ.mem quotient ω) (hRemainder : ℳ.mem remainder ω) (hFactorBlock :
      ℳ.IsOrdinalMultiplication 𝕀
        factorBlock factor blockBase) (hBlock :
      ℳ.IsOrdinalMultiplication 𝕀
        block blockBase quotient) (hDecomposition :
      ℳ.IsOrdinalAddition 𝕀 multiplier block remainder) (hTotal :
      ℳ.IsOrdinalMultiplication 𝕀
        total factor multiplier) (hDividesFactorBlock :
      ℳ.IsNaturalDivisor 𝕀 ω divisor factorBlock) (hDividesTotal :
      ℳ.IsNaturalDivisor 𝕀 ω divisor total) :
    ∃ remainderProduct,
      ℳ.IsOrdinalMultiplication 𝕀
        remainderProduct factor remainder ∧
      ℳ.IsNaturalDivisor 𝕀 ω divisor remainderProduct := by
  have hFactorOrdinal :=
    hω.members_areOrdinals hZF factor hFactor
  have hBlockBaseOrdinal :=
    hω.members_areOrdinals hZF blockBase hBlockBase
  have hQuotientOrdinal :=
    hω.members_areOrdinals hZF quotient hQuotient
  have hRemainderOrdinal :=
    hω.members_areOrdinals hZF remainder hRemainder
  have hBlockOmega :=
    ZF.ordinalMultiplication_mem_omega
      hZF 𝕀 hω hBlockBase hQuotient hBlock
  have hTotalOmega :=
    ZF.ordinalMultiplication_mem_omega
      hZF 𝕀 hω hFactor hMultiplier hTotal
  rcases ZF.ordinalMultiplication_existsUnique
      hZF 𝕀 factor (ZF.ordinalMultiplication_isOrdinal
        hZF 𝕀 hBlockBaseOrdinal hQuotientOrdinal hBlock) with
    ⟨factorBlockQuotient, hFactorBlockQuotient, _⟩
  rcases ZF.ordinalMultiplication_existsUnique
      hZF 𝕀 factorBlock hQuotientOrdinal with
    ⟨associatedFactorBlock, hAssociatedFactorBlock, _⟩
  have hAssociation :=
    ZF.ordinalMultiplication_assoc
      hZF 𝕀 hFactorOrdinal hBlockBaseOrdinal hQuotientOrdinal
      hFactorBlock hBlock hFactorBlockQuotient
      hAssociatedFactorBlock
  have hDividesAssociated :=
    nat_dvd_mul_right hZF 𝕀 hω hQuotient
      hAssociatedFactorBlock hDividesFactorBlock
  have hDividesFactorBlockQuotient :
      ℳ.IsNaturalDivisor 𝕀 ω divisor factorBlockQuotient := by
    simpa [hAssociation] using hDividesAssociated
  rcases ZF.ordinalMultiplication_existsUnique
      hZF 𝕀 factor hRemainderOrdinal with
    ⟨remainderProduct, hRemainderProduct, _⟩
  have hRemainderProductOmega :=
    ZF.ordinalMultiplication_mem_omega
      hZF 𝕀 hω hFactor hRemainder hRemainderProduct
  rcases ZF.ordinalAddition_existsUnique
      hZF 𝕀 factorBlockQuotient (ZF.ordinalMultiplication_isOrdinal
        hZF 𝕀 hFactorOrdinal hRemainderOrdinal
        hRemainderProduct) with
    ⟨distributed, hDistributed, _⟩
  have hDistribution :=
    ZF.ordinalMultiplication_add
      hZF 𝕀 hFactorOrdinal (ZF.ordinalMultiplication_isOrdinal
        hZF 𝕀 hBlockBaseOrdinal hQuotientOrdinal hBlock)
      hRemainderOrdinal hDecomposition hTotal
      hFactorBlockQuotient hRemainderProduct hDistributed
  have hTotalAddition :
      ℳ.IsOrdinalAddition 𝕀
        total factorBlockQuotient remainderProduct := by
    simpa [hDistribution] using hDistributed
  exact ⟨remainderProduct, hRemainderProduct,
    nat_dvd_add_right_cancel hZF 𝕀 hω
      hDivisorNonempty (ZF.ordinalMultiplication_mem_omega
        hZF 𝕀 hω hFactor hBlockOmega
        hFactorBlockQuotient)
      hRemainderProductOmega hTotalOmega
      hTotalAddition hDividesFactorBlockQuotient hDividesTotal⟩
namespace IsPrimeInOmega
/--
Euclid 引理：模型内部素数若整除两个自然数的乘积，则整除其中一个因子。
证明选择使 `prime ∣ left * multiplier` 的最小非零乘数。商余分解和上一层的
余项整除引理说明该最小乘数整除所有候选乘数；它因而整除 `prime`，素性迫使它
等于一或 `prime`，而“不整除左因子”的分支排除了一。
-/
theorem nat_prime_dvd_mul
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω one prime left right product : ℳ.Domain} (hω : ℳ.IsOmega ω) (hPrime : ℳ.IsPrimeInOmega 𝕀 ω one prime) (hLeft : ℳ.mem left ω) (hRight : ℳ.mem right ω)
    (hProduct :
      ℳ.IsOrdinalMultiplication 𝕀 product left right) (hDividesProduct :
      ℳ.IsNaturalDivisor 𝕀 ω prime product) :
    ℳ.IsNaturalDivisor 𝕀 ω prime left ∨
      ℳ.IsNaturalDivisor 𝕀 ω prime right := by
  by_cases hDividesLeft :
      ℳ.IsNaturalDivisor 𝕀 ω prime left
  · exact Or.inl hDividesLeft
  · apply Or.inr
    have hPrimeNonempty : ∃ member, ℳ.mem member prime :=
      ⟨one, hPrime.one_mem_prime⟩
    have hLeftOrdinal :=
      hω.members_areOrdinals hZF left hLeft
    have hPrimeOrdinal := hPrime.prime_isOrdinal hZF hω
    let env : Env ℳ 3 := {
      bound := fun
        | 0 => ω
        | 1 => left
        | 2 => prime
      free := fun _ => Classical.choice ℳ.nonempty
    }
    rcases ZF.separation_exists_d hZF (Definitional.Project.UnarySchema.natPrimeMultiplier 𝒞)
        env ω with
      ⟨candidates, hCandidatesRaw⟩
    have hCandidates (multiplier : ℳ.Domain) :
        ℳ.mem multiplier candidates ↔
          ℳ.mem multiplier ω ∧ (∃ member, ℳ.mem member multiplier) ∧
            ∃ candidateProduct,
              ℳ.IsOrdinalMultiplication 𝕀
                candidateProduct left multiplier ∧
              ℳ.IsNaturalDivisor 𝕀
                ω prime candidateProduct := by
      rw [hCandidatesRaw multiplier]
      change (ℳ.mem multiplier ω ∧ (Definitional.Project.UnarySchema.natPrimeMultiplier 𝒞).denote
            env multiplier) ↔ _
      rw [ZF.natPrimeMultiplier_denote_iff hZF 𝕀 env multiplier]
    have hCandidatesSubset :
        ℳ.MemberSubset candidates ω := by
      intro multiplier hMultiplier
      exact (hCandidates multiplier).mp hMultiplier |>.1
    rcases ZF.ordinalMultiplication_existsUnique
        hZF 𝕀 left hPrimeOrdinal with
      ⟨leftPrime, hLeftPrime, _⟩
    rcases ZF.ordinalMultiplication_existsUnique
        hZF 𝕀 prime hLeftOrdinal with
      ⟨primeLeft, hPrimeLeft, _⟩
    have hLeftPrimeEq :=
      natural_mul_comm hZF 𝕀 hω
        hLeft hPrime.prime_mem_omega
        hLeftPrime hPrimeLeft
    have hPrimeDividesLeftPrime :
        ℳ.IsNaturalDivisor 𝕀 ω prime leftPrime :=
      ⟨hPrime.prime_mem_omega, left, hLeft, by
        simpa [hLeftPrimeEq] using hPrimeLeft⟩
    have hPrimeCandidate : ℳ.mem prime candidates := (hCandidates prime).mpr
        ⟨hPrime.prime_mem_omega, hPrimeNonempty,
          leftPrime, hLeftPrime, hPrimeDividesLeftPrime⟩
    rcases (hω.isOrdinal hZF).wellOrder.least
        candidates hCandidatesSubset
        ⟨prime, hPrimeCandidate⟩ with
      ⟨leastMultiplier, hLeastCandidate, hLeast⟩
    rcases (hCandidates leastMultiplier).mp hLeastCandidate with
      ⟨hLeastOmega, hLeastNonempty,
        leastProduct, hLeastProduct, hPrimeDividesLeastProduct⟩
    have hLeastOrdinal :=
      hω.members_areOrdinals hZF leastMultiplier hLeastOmega
    have hNoEarlierCandidate :
        ∀ earlier, ℳ.mem earlier leastMultiplier →
          ¬ ℳ.mem earlier candidates := by
      intro earlier hEarlier hEarlierCandidate
      rcases hLeast earlier hEarlierCandidate with
        hSame | hLeastEarlier
      · have hEq :=
          hZF.1.eq_of_same_members
            leastMultiplier earlier hSame
        subst earlier
        exact hLeastOrdinal.wellOrder.linear.irrefl
          leastMultiplier hEarlier hEarlier
      · have hSelf :=
          hLeastOrdinal.transitive
            earlier hEarlier leastMultiplier hLeastEarlier
        exact hLeastOrdinal.wellOrder.linear.irrefl
          leastMultiplier hSelf hSelf
    have hLeastDivides :
        ∀ multiplier candidateProduct,
          ℳ.mem multiplier ω →
          ℳ.IsOrdinalMultiplication 𝕀
            candidateProduct left multiplier →
          ℳ.IsNaturalDivisor 𝕀 ω prime candidateProduct →
          ℳ.IsNaturalDivisor 𝕀
            ω leastMultiplier multiplier := by
      intro multiplier candidateProduct
        hMultiplier hCandidateProduct hPrimeDividesCandidate
      rcases ZF.ordinalDivision_existsUnique_pair
          hZF 𝕀 (hω.members_areOrdinals hZF multiplier hMultiplier)
          hLeastOrdinal hLeastNonempty with
        ⟨quotient, remainder, hDivision, _⟩
      have hQuotientOmega :=
        nat_div_quotient_mem_omega
          hZF 𝕀 hω hMultiplier hLeastOmega
          hLeastNonempty hDivision
      rcases hDivision with
        ⟨_, hRemainderLeast,
          block, hBlock, hDecomposition⟩
      have hRemainderOmega :=
        hω.transitive hZF
          leastMultiplier hLeastOmega
          remainder hRemainderLeast
      rcases nat_dvd_mul_remainder
          hZF 𝕀 hω hPrimeNonempty
          hLeft hLeastOmega hMultiplier
          hQuotientOmega hRemainderOmega
          hLeastProduct hBlock hDecomposition
          hCandidateProduct
          hPrimeDividesLeastProduct hPrimeDividesCandidate with
        ⟨remainderProduct, hRemainderProduct,
          hPrimeDividesRemainderProduct⟩
      have hRemainderEmpty :
          ∀ member, ¬ ℳ.mem member remainder := by
        intro member hMember
        have hRemainderCandidate :
            ℳ.mem remainder candidates := (hCandidates remainder).mpr
            ⟨hRemainderOmega, ⟨member, hMember⟩,
              remainderProduct, hRemainderProduct,
              hPrimeDividesRemainderProduct⟩
        exact hNoEarlierCandidate
          remainder hRemainderLeast hRemainderCandidate
      have hMultiplierEq : multiplier = block := (ZF.ordinalAddition_zero_iff
          hZF 𝕀 hRemainderEmpty).mp hDecomposition
      exact ⟨hLeastOmega, quotient, hQuotientOmega, by
        simpa [hMultiplierEq] using hBlock⟩
    have hLeastDividesPrime :
        ℳ.IsNaturalDivisor 𝕀 ω leastMultiplier prime :=
      hLeastDivides prime leftPrime
        hPrime.prime_mem_omega hLeftPrime
        hPrimeDividesLeftPrime
    have hLeastEqPrime : leastMultiplier = prime := by
      rcases hPrime.only_trivial_divisors
          leastMultiplier hLeastDividesPrime with
        hLeastEqOne | hLeastEqPrime
      · have hLeastProductEq : leastProduct = left := by
          have hLeastProductOne :
              ℳ.IsOrdinalMultiplication 𝕀
                leastProduct left one := by
            simpa [hLeastEqOne] using hLeastProduct
          exact ZF.ordinalMultiplication_one_right
            hZF 𝕀 hLeftOrdinal hPrime.one_is_one
            hLeastProductOne
        exact False.elim <| hDividesLeft <| by
          simpa [hLeastProductEq] using
            hPrimeDividesLeastProduct
      · exact hLeastEqPrime
    have hLeastDividesRight :=
      hLeastDivides right product hRight
        hProduct hDividesProduct
    simpa [hLeastEqPrime] using hLeastDividesRight
/-- 模型内部素数不整除一。 -/
theorem nat_prime_not_dvd_one
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω one prime : ℳ.Domain} (hω : ℳ.IsOmega ω) (hPrime : ℳ.IsPrimeInOmega 𝕀 ω one prime) :
    ¬ ℳ.IsNaturalDivisor 𝕀 ω prime one := by
  intro hDividesOne
  rcases hDividesOne with
    ⟨_, quotient, hQuotient, hOneProduct⟩
  have hPrimeOrdinal := hPrime.prime_isOrdinal hZF hω
  have hQuotientOrdinal :=
    hω.members_areOrdinals hZF quotient hQuotient
  by_cases hQuotientEmpty :
      ∀ member, ¬ ℳ.mem member quotient
  · have hOneEmpty := (ZF.ordinalMultiplication_zero_iff
        hZF 𝕀 hPrimeOrdinal hQuotientEmpty).mp
        hOneProduct
    rcases hPrime.one_is_one with
      ⟨zero, _, hOneSuccessor⟩
    exact hOneEmpty zero <| (hOneSuccessor zero).mpr (Or.inr fun _ => Iff.rfl)
  · have hQuotientNonempty :
        ∃ member, ℳ.mem member quotient := by
      apply Classical.byContradiction
      intro hNoMember
      apply hQuotientEmpty
      intro member hMember
      exact hNoMember ⟨member, hMember⟩
    rcases ZF.ordinalMultiplication_existsUnique
        hZF 𝕀 quotient hPrimeOrdinal with
      ⟨quotientPrime, hQuotientPrime, _⟩
    have hOneEqQuotientPrime :=
      natural_mul_comm hZF 𝕀 hω
        hPrime.prime_mem_omega hQuotient
        hOneProduct hQuotientPrime
    have hPrimeOrder :=
      ZF.ordinalMultiplication_right_eq_or_mem
        hZF 𝕀 hQuotientOrdinal hQuotientNonempty
        hPrimeOrdinal hQuotientPrime
    have hOneQuotientPrime :
        ℳ.mem one quotientPrime := by
      rcases hPrimeOrder with hPrimeEq | hPrimeMember
      · simpa [hPrimeEq] using hPrime.one_mem_prime
      · exact (ZF.ordinalMultiplication_isOrdinal
            hZF 𝕀 hQuotientOrdinal hPrimeOrdinal
            hQuotientPrime).transitive
            prime hPrimeMember one hPrime.one_mem_prime
    have hSelf : ℳ.mem quotientPrime quotientPrime := by
      simpa [hOneEqQuotientPrime] using hOneQuotientPrime
    exact (ZF.ordinalMultiplication_isOrdinal
        hZF 𝕀 hQuotientOrdinal hPrimeOrdinal
        hQuotientPrime).wellOrder.linear.irrefl
        quotientPrime hSelf hSelf
/--
若模型内部素数整除一个自然数底数的任意幂，则它整除该底数。
证明选取被整除幂的最小指数，并用 Euclid 引理下降到前一指数。
-/
theorem nat_prime_dvd_base_of_dvd_power
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention} (𝕀 : 𝒞.Interpretation ℳ)
    {ω one prime base exponent power : ℳ.Domain} (hω : ℳ.IsOmega ω) (hPrime : ℳ.IsPrimeInOmega 𝕀 ω one prime) (hBase : ℳ.mem base ω)
    (hExponent : ℳ.mem exponent ω) (hPower :
      ℳ.IsOrdinalExponentiation 𝕀 power base exponent) (hDividesPower :
      ℳ.IsNaturalDivisor 𝕀 ω prime power) :
    ℳ.IsNaturalDivisor 𝕀 ω prime base := by
  let env : Env ℳ 3 := {
    bound := fun
      | 0 => ω
      | 1 => prime
      | 2 => base
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases ZF.separation_exists_d hZF (Definitional.Project.UnarySchema.natPrimePowerExponent 𝒞)
      env ω with
    ⟨candidates, hCandidatesRaw⟩
  have hCandidates (candidateExponent : ℳ.Domain) :
      ℳ.mem candidateExponent candidates ↔
        ℳ.mem candidateExponent ω ∧
          ∃ candidatePower,
            ℳ.IsOrdinalExponentiation 𝕀
              candidatePower base candidateExponent ∧
            ℳ.IsNaturalDivisor 𝕀
              ω prime candidatePower := by
    rw [hCandidatesRaw candidateExponent]
    change (ℳ.mem candidateExponent ω ∧ (Definitional.Project.UnarySchema.natPrimePowerExponent 𝒞).denote
          env candidateExponent) ↔ _
    rw [ZF.natPrimePowerExponent_denote_iff
      hZF 𝕀 env candidateExponent]
  have hCandidatesSubset :
      ℳ.MemberSubset candidates ω := by
    intro candidateExponent hCandidate
    exact (hCandidates candidateExponent).mp hCandidate |>.1
  have hExponentCandidate : ℳ.mem exponent candidates := (hCandidates exponent).mpr
      ⟨hExponent, power, hPower, hDividesPower⟩
  rcases (hω.isOrdinal hZF).wellOrder.least
      candidates hCandidatesSubset
      ⟨exponent, hExponentCandidate⟩ with
    ⟨leastExponent, hLeastCandidate, hLeast⟩
  rcases (hCandidates leastExponent).mp hLeastCandidate with
    ⟨hLeastOmega, leastPower,
      hLeastPower, hDividesLeastPower⟩
  have hBaseOrdinal :=
    hω.members_areOrdinals hZF base hBase
  have hLeastOrdinal :=
    hω.members_areOrdinals hZF leastExponent hLeastOmega
  have hLeastNonempty :
      ∃ member, ℳ.mem member leastExponent := by
    apply Classical.byContradiction
    intro hNoMember
    have hLeastEmpty :
        ∀ member, ¬ ℳ.mem member leastExponent := by
      simpa only [not_exists] using hNoMember
    have hLeastPowerOne := (ZF.ordinalExponentiation_zero_iff
        hZF 𝕀 hBaseOrdinal hLeastEmpty).mp
        hLeastPower
    have hLeastPowerEqOne :=
      Structure.IsOrdinalOne.eq hZF.1
        hLeastPowerOne hPrime.one_is_one
    apply hPrime.nat_prime_not_dvd_one hZF 𝕀 hω
    simpa [hLeastPowerEqOne] using hDividesLeastPower
  rcases hω.exists_predecessor_of_mem_of_nonempty
      hZF hLeastOmega hLeastNonempty with
    ⟨predecessor, hPredecessorOmega, hLeastSuccessor⟩
  have hPredecessorOrdinal :=
    hω.members_areOrdinals hZF predecessor hPredecessorOmega
  rcases (ZF.ordinalExponentiation_successor_iff
      hZF 𝕀 hBaseOrdinal hPredecessorOrdinal
      hLeastSuccessor).mp hLeastPower with
    ⟨previousPower, hPreviousPower, hLeastProduct⟩
  have hPreviousPowerOmega :=
    ZF.ordinalExponentiation_mem_omega
      hZF 𝕀 hω hBase hPredecessorOmega hPreviousPower
  rcases hPrime.nat_prime_dvd_mul
      hZF 𝕀 hω hPreviousPowerOmega hBase
      hLeastProduct hDividesLeastPower with
    hDividesPrevious | hDividesBase
  · have hPredecessorCandidate :
        ℳ.mem predecessor candidates := (hCandidates predecessor).mpr
        ⟨hPredecessorOmega, previousPower,
          hPreviousPower, hDividesPrevious⟩
    have hPredecessorLeast : ℳ.mem predecessor leastExponent := (hLeastSuccessor predecessor).mpr (Or.inr fun _ => Iff.rfl)
    rcases hLeast predecessor hPredecessorCandidate with
      hSame | hLeastPredecessor
    · have hEq :=
        hZF.1.eq_of_same_members
          leastExponent predecessor hSame
      subst predecessor
      exact False.elim <|
        hLeastOrdinal.wellOrder.linear.irrefl
          leastExponent hPredecessorLeast hPredecessorLeast
    · have hSelf :=
        hLeastOrdinal.transitive predecessor
          hPredecessorLeast leastExponent hLeastPredecessor
      exact False.elim <|
        hLeastOrdinal.wellOrder.linear.irrefl
          leastExponent hSelf hSelf
  · exact hDividesBase
end IsPrimeInOmega
namespace IsPrimePower
/-- 正指数素数幂可被其底素数整除。 -/
theorem prime_dvd_power_of_exponent_nonempty
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one power prime exponent : ℳ.Domain} (hω : ℳ.IsOmega ω) (hPower : ℳ.IsPrimePower 𝕀 ω one power prime exponent)
    (hExponentNonempty : ∃ member, ℳ.mem member exponent) :
    ℳ.IsNaturalDivisor 𝕀 ω prime power := by
  rcases hω.exists_predecessor_of_mem_of_nonempty
      hZF hPower.exponent_mem_omega hExponentNonempty with
    ⟨predecessor, hPredecessorOmega, hExponentSuccessor⟩
  have hPrimeOrdinal :=
    hPower.prime_is_prime.prime_isOrdinal hZF hω
  have hPredecessorOrdinal :=
    hω.members_areOrdinals hZF predecessor hPredecessorOmega
  rcases (ZF.ordinalExponentiation_successor_iff
      hZF 𝕀 hPrimeOrdinal hPredecessorOrdinal
      hExponentSuccessor).mp hPower.power_spec with
    ⟨previousPower, hPreviousPower, hPowerProduct⟩
  have hPreviousPowerOmega :=
    ZF.ordinalExponentiation_mem_omega
      hZF 𝕀 hω
      hPower.prime_is_prime.prime_mem_omega
      hPredecessorOmega hPreviousPower
  rcases ZF.ordinalMultiplication_existsUnique
      hZF 𝕀 prime (hω.members_areOrdinals hZF
        previousPower hPreviousPowerOmega) with
    ⟨primePrevious, hPrimePrevious, _⟩
  have hPowerEqPrimePrevious :=
    natural_mul_comm hZF 𝕀 hω
      hPreviousPowerOmega
      hPower.prime_is_prime.prime_mem_omega
      hPowerProduct hPrimePrevious
  exact ⟨hPower.prime_is_prime.prime_mem_omega,
    previousPower, hPreviousPowerOmega, by
      simpa [hPowerEqPrimePrevious] using hPrimePrevious⟩
/--
两个正指数素数幂若取值相同，则它们的底素数相同。
双向使用 Euclid 下降后，两边素性将两个底数都压到平凡因子分支。
-/
theorem prime_eq_of_power_eq
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one firstPower secondPower firstPrime secondPrime
      firstExponent secondExponent : ℳ.Domain} (hω : ℳ.IsOmega ω) (hFirst :
      ℳ.IsPrimePower 𝕀 ω one
        firstPower firstPrime firstExponent) (hSecond :
      ℳ.IsPrimePower 𝕀 ω one
        secondPower secondPrime secondExponent) (hFirstExponentNonempty :
      ∃ member, ℳ.mem member firstExponent) (hSecondExponentNonempty :
      ∃ member, ℳ.mem member secondExponent) (hPowerEq : firstPower = secondPower) :
    firstPrime = secondPrime := by
  have hFirstDividesFirst :=
    hFirst.prime_dvd_power_of_exponent_nonempty
      hZF hω hFirstExponentNonempty
  have hFirstDividesSecond :
      ℳ.IsNaturalDivisor 𝕀 ω firstPrime secondPower := by
    simpa only [hPowerEq] using hFirstDividesFirst
  have hFirstDividesSecondPrime :=
    hFirst.prime_is_prime.nat_prime_dvd_base_of_dvd_power
      hZF 𝕀 hω
      hSecond.prime_is_prime.prime_mem_omega
      hSecond.exponent_mem_omega hSecond.power_spec
      hFirstDividesSecond
  have hSecondDividesSecond :=
    hSecond.prime_dvd_power_of_exponent_nonempty
      hZF hω hSecondExponentNonempty
  have hSecondDividesFirst :
      ℳ.IsNaturalDivisor 𝕀 ω secondPrime firstPower := by
    simpa only [hPowerEq] using hSecondDividesSecond
  have hSecondDividesFirstPrime :=
    hSecond.prime_is_prime.nat_prime_dvd_base_of_dvd_power
      hZF 𝕀 hω
      hFirst.prime_is_prime.prime_mem_omega
      hFirst.exponent_mem_omega hFirst.power_spec
      hSecondDividesFirst
  rcases hSecond.prime_is_prime.only_trivial_divisors
      firstPrime hFirstDividesSecondPrime with
    hFirstOne | hPrimeEq
  · rcases hFirst.prime_is_prime.only_trivial_divisors
        secondPrime hSecondDividesFirstPrime with
      hSecondOne | hPrimeEq
    · exact hFirstOne.trans hSecondOne.symm
    · exact hPrimeEq.symm
  · exact hPrimeEq
/-- 不同素数的正指数幂互异。 -/
theorem power_ne_of_prime_ne
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {ω one firstPower secondPower firstPrime secondPrime
      firstExponent secondExponent : ℳ.Domain} (hω : ℳ.IsOmega ω) (hFirst :
      ℳ.IsPrimePower 𝕀 ω one
        firstPower firstPrime firstExponent) (hSecond :
      ℳ.IsPrimePower 𝕀 ω one
        secondPower secondPrime secondExponent) (hFirstExponentNonempty :
      ∃ member, ℳ.mem member firstExponent) (hSecondExponentNonempty :
      ∃ member, ℳ.mem member secondExponent) (hPrimeNe : firstPrime ≠ secondPrime) :
    firstPower ≠ secondPower := by
  intro hPowerEq
  exact hPrimeNe <|
    hFirst.prime_eq_of_power_eq hZF hω hSecond
      hFirstExponentNonempty hSecondExponentNonempty hPowerEq
end IsPrimePower
end Structure
end SetTheory
end YesMetaZFC
