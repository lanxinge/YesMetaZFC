import YesMetaZFC.SetTheory.Card.Aleph.Hartogs
import YesMetaZFC.SetTheory.Ord.Closure

/-!
# Aleph 数的递归定理

本层完成基数后继的存在唯一性，并把 Aleph 递归算子接入公共超限递归内核。由此得到
Aleph 类关系在序数指标上的存在唯一性，以及零、后继、极限三类指标处的递归方程。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure.IsCardinalSuccessor

/-- 同一基数的两个基数后继相等。 -/
theorem eq {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {first second predecessor : ℳ.Domain}
    (hFirst : ℳ.IsCardinalSuccessor 𝕀 first predecessor)
    (hSecond : ℳ.IsCardinalSuccessor 𝕀 second predecessor) :
    first = second := by
  rcases hFirst.2.2 second hSecond.1 hSecond.2.1 with
    hFirstEq | hFirstSecond
  · exact hFirstEq
  rcases hSecond.2.2 first hFirst.1 hFirst.2.1 with
    hSecondEq | hSecondFirst
  · exact hSecondEq.symm
  have hSelf : ℳ.mem first first :=
    hFirst.1.1.transitive second hSecondFirst first hFirstSecond
  exact False.elim <|
    hFirst.1.1.wellOrder.linear.irrefl first hSelf hSelf

end Structure.IsCardinalSuccessor

namespace ZF

/-- 从给定序数上界中分离严格位于参数序数之上的基数。 -/
private def cardinalAboveMembership
    (𝒞 : Definitional.Project.OrderedPairConvention) :
    Definitional.Project.UnarySchema 1 where
  body := .conj
    (Definitional.Project.Formula.isCardinal 𝒞 (.bound 0))
    (.mem (.bound 1) (.bound 0))
  freeClosed := by
    simp [Definitional.Project.Formula.isCardinal,
      Definitional.Project.Formula.equinumerous,
      Definitional.Project.Formula.isBijectionFromTo,
      Definitional.Project.Formula.isInjectionFromTo,
      Definitional.Project.Formula.isFunctionFromTo,
      Definitional.Project.Formula.isFunction,
      Definitional.Project.Formula.isRelation,
      Definitional.Project.Formula.isDomain,
      Definitional.Project.Formula.isSurjectiveOnto,
      Definitional.Project.Formula.isInjective,
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

/-- 基数上界分离模式的模型语义。 -/
private theorem satisfies_cardinalAboveMembership_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 1) (candidate : ℳ.Domain) :
    Definitional.Project.Formula.satisfies
        (env.push candidate) (cardinalAboveMembership 𝒞).body ↔
      ℳ.IsCardinal 𝕀 candidate ∧
        ℳ.mem (env.bound 0) candidate := by
  simp only [cardinalAboveMembership,
    Definitional.Project.Formula.satisfies_conj_iff,
    Definitional.Project.Formula.satisfies_isCardinal_iff 𝕀 hExt,
    Definitional.Project.Formula.satisfies_mem_iff]
  change
    (ℳ.IsCardinal 𝕀 candidate ∧
      ℳ.mem (env.bound 0) candidate) ↔
    (ℳ.IsCardinal 𝕀 candidate ∧
      ℳ.mem (env.bound 0) candidate)
  rfl

/-- “当前指标处的每个 Aleph 值都是基数”的一参数归纳模式。 -/
private def alephValueCardinalAt
    (𝒞 : Definitional.Project.OrderedPairConvention) :
    Definitional.Project.UnarySchema 1 where
  body := .forallE <| .imp
    (Definitional.Project.Formula.isAlephNumber 𝒞
      (.bound 2) (.bound 1) (.bound 0))
    (Definitional.Project.Formula.isCardinal 𝒞 (.bound 0))
  freeClosed := by
    simp [Definitional.Project.Formula.isAlephNumber,
      Definitional.Project.Formula.isCardinal,
      Definitional.Project.Formula.equinumerous,
      Definitional.Project.Formula.isBijectionFromTo,
      Definitional.Project.Formula.isInjectionFromTo,
      Definitional.Project.Formula.isFunctionFromTo,
      Definitional.Project.Formula.isFunction,
      Definitional.Project.Formula.isRelation,
      Definitional.Project.Formula.isDomain,
      Definitional.Project.Formula.isSurjectiveOnto,
      Definitional.Project.Formula.isInjective,
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
      Definitional.Project.Formula.related,
      Definitional.Formula.FreeClosed,
      Definitional.Term.newest]
    constructor
    · exact Definitional.Project.Formula.related_freeClosed_of_closed
        (relation := Definitional.Project.BinarySchema.aleph 𝒞)
        (parameters :=
          (Definitional.TermVector.singleton (.bound 2) :
            Definitional.TermVector 1 3))
        (left := (.bound 1 : Definitional.Term 3))
        (right := (.bound 0 : Definitional.Term 3))
        (by intro entry; simp [Definitional.TermVector.singleton])
        (by simp) (by simp)
    · repeat' constructor
      all_goals
        apply Definitional.Project.Formula.related_freeClosed_of_closed <;>
          simp [Definitional.TermVector.FreeClosed,
            Definitional.TermVector.empty]

/-- Aleph 值基数性归纳模式的模型语义。 -/
private theorem satisfies_alephValueCardinalAt_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 1) (index : ℳ.Domain) :
    Definitional.Project.Formula.satisfies
        (env.push index) (alephValueCardinalAt 𝒞).body ↔
      ∀ value,
        ℳ.IsAlephNumber 𝕀 (env.bound 0) index value →
          ℳ.IsCardinal 𝕀 value := by
  simp only [alephValueCardinalAt,
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_imp_iff,
    Definitional.Project.Formula.satisfies_isAlephNumber_iff 𝕀 hExt,
    Definitional.Project.Formula.satisfies_isCardinal_iff 𝕀 hExt]
  change
    (∀ value,
      ℳ.IsAlephNumber 𝕀 (env.bound 0) index value →
        ℳ.IsCardinal 𝕀 value) ↔
    (∀ value,
      ℳ.IsAlephNumber 𝕀 (env.bound 0) index value →
        ℳ.IsCardinal 𝕀 value)
  rfl

/-- 引理 3.4(i) 的最小化形式：每个序数都有唯一的基数后继。 -/
theorem cardinalSuccessor_existsUnique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {predecessor : ℳ.Domain}
    (hPredecessor : ℳ.IsOrdinal predecessor) :
    ∃ successor,
      ℳ.IsCardinalSuccessor 𝕀 successor predecessor ∧
        ∀ other,
          ℳ.IsCardinalSuccessor 𝕀 other predecessor →
            other = successor := by
  rcases exists_cardinalAbove hZF 𝕀 hPredecessor with
    ⟨firstUpper, hFirstUpperCardinal, hPredecessorFirstUpper⟩
  rcases exists_cardinalAbove hZF 𝕀 hFirstUpperCardinal.1 with
    ⟨bound, hBoundCardinal, hFirstUpperBound⟩
  let env : Env ℳ 1 := {
    bound := fun _ => predecessor
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_separation hZF
      (cardinalAboveMembership 𝒞) env bound with
    ⟨candidates, hCandidates⟩
  have hCandidatesSemantic (candidate : ℳ.Domain) :
      ℳ.mem candidate candidates ↔
        ℳ.mem candidate bound ∧
          ℳ.IsCardinal 𝕀 candidate ∧
            ℳ.mem predecessor candidate := by
    rw [hCandidates candidate]
    constructor
    · rintro ⟨hCandidateBound, hCandidate⟩
      exact ⟨hCandidateBound,
        (satisfies_cardinalAboveMembership_iff
          𝕀 hZF.1 env candidate).mp hCandidate⟩
    · rintro ⟨hCandidateBound, hCandidate⟩
      exact ⟨hCandidateBound,
        (satisfies_cardinalAboveMembership_iff
          𝕀 hZF.1 env candidate).mpr hCandidate⟩
  have hCandidatesSubset : ℳ.MemberSubset candidates bound := by
    intro candidate hCandidate
    exact (hCandidatesSemantic candidate).mp hCandidate |>.1
  have hCandidatesNonempty :
      ∃ candidate, ℳ.mem candidate candidates :=
    ⟨firstUpper, (hCandidatesSemantic firstUpper).mpr
      ⟨hFirstUpperBound, hFirstUpperCardinal,
        hPredecessorFirstUpper⟩⟩
  rcases hBoundCardinal.1.wellOrder.least candidates
      hCandidatesSubset hCandidatesNonempty with
    ⟨successor, hSuccessorCandidates, hLeast⟩
  have hSuccessorData :=
    (hCandidatesSemantic successor).mp hSuccessorCandidates
  have hSuccessorBound : ℳ.mem successor bound :=
    hSuccessorData.1
  have hMinimal :
      ∀ candidate,
        ℳ.IsCardinal 𝕀 candidate →
          ℳ.mem predecessor candidate →
            successor = candidate ∨
              ℳ.mem successor candidate := by
    intro candidate hCandidateCardinal hPredecessorCandidate
    rcases Structure.IsOrdinal.trichotomy hZF.1
        hCandidateCardinal.1 hBoundCardinal.1
        (KP.exists_difference (ZF.modelsKP hZF))
        (KP.exists_intersection (ZF.modelsKP hZF)
          candidate bound) with
      hSame | hCandidateBound | hBoundCandidate
    · have hCandidateEq :=
        hZF.1.eq_of_same_members candidate bound hSame
      subst candidate
      exact Or.inr hSuccessorBound
    · rcases hLeast candidate <|
          (hCandidatesSemantic candidate).mpr
            ⟨hCandidateBound, hCandidateCardinal,
              hPredecessorCandidate⟩ with
        hSame | hSuccessorCandidate
      · exact Or.inl <|
          hZF.1.eq_of_same_members successor candidate hSame
      · exact Or.inr hSuccessorCandidate
    · exact Or.inr <|
        hCandidateCardinal.1.transitive bound hBoundCandidate
          successor hSuccessorBound
  have hSuccessor :
      ℳ.IsCardinalSuccessor 𝕀 successor predecessor :=
    ⟨hSuccessorData.2.1, hSuccessorData.2.2, hMinimal⟩
  exact ⟨successor, hSuccessor, fun other hOther =>
    Structure.IsCardinalSuccessor.eq hOther hSuccessor⟩

/-- Aleph 后继运算在任意输入上全定义且单值。 -/
theorem alephSuccessorOperation_existsUnique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (previous : ℳ.Domain) :
    ∃ output,
      ℳ.IsAlephSuccessorOperation 𝕀 previous output ∧
        ∀ other,
          ℳ.IsAlephSuccessorOperation 𝕀 previous other →
            other = output := by
  by_cases hPrevious : ℳ.IsOrdinal previous
  · rcases cardinalSuccessor_existsUnique hZF 𝕀 hPrevious with
      ⟨output, hOutput, hUnique⟩
    refine ⟨output, Or.inl ⟨hPrevious, hOutput⟩, ?_⟩
    intro other hOther
    rcases hOther with hOther | hOther
    · exact hUnique other hOther.2
    · exact False.elim <| hOther.1 hPrevious
  · rcases KP.exists_empty (ZF.modelsKP hZF) with
      ⟨output, hOutput⟩
    refine ⟨output, Or.inr ⟨hPrevious, hOutput⟩, ?_⟩
    intro other hOther
    rcases hOther with hOther | hOther
    · exact False.elim <| hPrevious hOther.1
    · apply hZF.1.eq_of_same_members
      intro value
      exact iff_of_false (hOther.2 value) (hOutput value)

/-- Aleph 的零、后继、极限递归步在所有超限序列上全定义且单值。 -/
theorem alephStep_isClassFunctionOnTransfiniteSequences
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (ω : ℳ.Domain) :
    ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
      (ℳ.IsAlephStep 𝕀 ω) := by
  exact zeroSuccessorLimitStep_isClassFunctionOnTransfiniteSequences
    hZF 𝕀
    (fun initial => initial = ω)
    (ℳ.IsAlephSuccessorOperation 𝕀)
    ⟨ω, rfl, fun other hOther => hOther⟩
    (alephSuccessorOperation_existsUnique hZF 𝕀)

/-- Aleph 递归算子的 schema 解释在所有超限序列上全定义且单值。 -/
theorem alephOperator_isClassFunctionOnTransfiniteSequences
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1) :
    ℳ.IsClassFunctionOnTransfiniteSequences 𝕀
      ((Definitional.Project.BinarySchema.alephOperator 𝒞).denote env) := by
  have hStep :=
    alephStep_isClassFunctionOnTransfiniteSequences
      hZF 𝕀 (env.bound 0)
  intro sequence hSequence
  rcases hStep sequence hSequence with
    ⟨output, hOutput, hUnique⟩
  refine ⟨output, ?_, ?_⟩
  · exact
      (Definitional.Project.BinarySchema.denote_alephOperator_iff
        𝕀 hZF.1 env sequence output).mpr hOutput
  · intro other hOther
    apply hUnique other
    exact
      (Definitional.Project.BinarySchema.denote_alephOperator_iff
        𝕀 hZF.1 env sequence other).mp hOther

/-- Aleph 关系在所有序数指标上全定义且单值。 -/
theorem aleph_isClassFunctionOnOrdinals
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (ω : ℳ.Domain) :
    ℳ.IsClassFunctionOnOrdinals
      (fun index value => ℳ.IsAlephNumber 𝕀 ω index value) := by
  let env : Env ℳ 1 := {
    bound := fun _ => ω
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hClass :=
    transfiniteRecursion_isClassFunctionOnOrdinals
      hZF 𝕀 env
      (Definitional.Project.BinarySchema.alephOperator 𝒞)
      (alephOperator_isClassFunctionOnTransfiniteSequences
        hZF 𝕀 env)
  intro index hIndex
  rcases hClass index hIndex with
    ⟨value, hValue, hUnique⟩
  refine ⟨value, ?_, ?_⟩
  · have hSemantic :=
      (Definitional.Project.BinarySchema.denote_aleph_iff
        𝕀 hZF.1 env index value).mp hValue
    simpa [env] using hSemantic
  · intro other hOther
    apply hUnique other
    apply
      (Definitional.Project.BinarySchema.denote_aleph_iff
        𝕀 hZF.1 env index other).mpr
    simpa [env] using hOther

/-- Aleph 数对每个序数指标存在唯一。 -/
theorem aleph_existsUnique
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (ω : ℳ.Domain) {index : ℳ.Domain}
    (hIndex : ℳ.IsOrdinal index) :
    ∃ value,
      ℳ.IsAlephNumber 𝕀 ω index value ∧
        ∀ other,
          ℳ.IsAlephNumber 𝕀 ω index other →
            other = value :=
  aleph_isClassFunctionOnOrdinals hZF 𝕀 ω index hIndex

/-- Aleph 的零步方程：`aleph(0) = ω`。 -/
theorem aleph_zero_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω zero value : ℳ.Domain}
    (hZero : ∀ member, ¬ ℳ.mem member zero) :
    ℳ.IsAlephNumber 𝕀 ω zero value ↔
      value = ω := by
  have value_eq {selected : ℳ.Domain}
      (hSelected :
        ℳ.IsAlephNumber 𝕀 ω zero selected) :
      selected = ω := by
    rcases hSelected with
      ⟨sequence, hSequence, hOutput⟩
    have hZeroLength :
        ℳ.IsZeroLengthSequence 𝕀 sequence :=
      ⟨zero, hSequence.1, hZero⟩
    rcases hOutput with hOutput | hOutput | hOutput
    · exact hOutput.2
    · rcases hOutput with ⟨_, hSuccessorLength, _⟩
      exact False.elim <|
        hZeroLength.not_successorLength
          hZF.1 hSuccessorLength
    · exact False.elim <|
        hZeroLength.not_limitLength hZF.1 hOutput
  constructor
  · exact value_eq
  · intro hValue
    subst value
    rcases aleph_existsUnique hZF 𝕀 ω
        (Structure.IsOrdinal.of_no_members hZero) with
      ⟨selected, hSelected, _⟩
    have hSelectedEq := value_eq hSelected
    simpa [hSelectedEq] using hSelected

/--
Aleph 的后继步方程：后继指标处的值由前一 Aleph 值施行基数后继总化运算得到。
-/
theorem aleph_successor_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω predecessor successor value : ℳ.Domain}
    (hPredecessor : ℳ.IsOrdinal predecessor)
    (hSuccessor : ℳ.SuccessorOf successor predecessor) :
    ℳ.IsAlephNumber 𝕀 ω successor value ↔
      ∃ previous,
        ℳ.IsAlephNumber 𝕀 ω predecessor previous ∧
          ℳ.IsAlephSuccessorOperation 𝕀 previous value := by
  have characterize {selected : ℳ.Domain}
      (hSelected :
        ℳ.IsAlephNumber 𝕀 ω successor selected) :
      ∃ previous,
        ℳ.IsAlephNumber 𝕀 ω predecessor previous ∧
          ℳ.IsAlephSuccessorOperation 𝕀 previous selected := by
    rcases hSelected with
      ⟨sequence, hSequence, hOutput⟩
    have hPredecessorMem : ℳ.mem predecessor successor :=
      hSuccessor.predecessor_mem
    rcases (hSequence.1.2.2 predecessor).mp hPredecessorMem with
      ⟨previous, hPrevious⟩
    have hSuccessorLength :
        ℳ.IsSuccessorLengthSequenceWithLast 𝕀
          sequence previous :=
      ⟨predecessor, hPredecessor, successor, hSuccessor,
        hSequence.1, hPrevious⟩
    have hPreviousValue :
        ℳ.IsAlephNumber 𝕀 ω predecessor previous :=
      hSequence.recursionValue_of_pairMember
        hPredecessorMem hPrevious
    rcases hOutput with hOutput | hOutput | hOutput
    · exact False.elim <|
        hOutput.1.not_successorLength hZF.1 hSuccessorLength
    · rcases hOutput with
        ⟨otherPrevious, hOtherLength, hOtherOutput⟩
      have hPreviousEq :=
        hOtherLength.last_eq hZF.1 hSuccessorLength
      subst otherPrevious
      exact ⟨previous, hPreviousValue, hOtherOutput⟩
    · exact False.elim <|
        hSuccessorLength.not_limitLength hZF.1 hOutput
  constructor
  · exact characterize
  · rintro ⟨previous, hPrevious, hValue⟩
    have hSuccessorOrdinal :=
      KP.successor_isOrdinal (ZF.modelsKP hZF)
        hPredecessor hSuccessor
    rcases aleph_existsUnique hZF 𝕀 ω hSuccessorOrdinal with
      ⟨selected, hSelected, _⟩
    rcases characterize hSelected with
      ⟨selectedPrevious, hSelectedPrevious, hSelectedValue⟩
    rcases aleph_existsUnique hZF 𝕀 ω hPredecessor with
      ⟨_, _, hPreviousUnique⟩
    have hPreviousEq : selectedPrevious = previous :=
      (hPreviousUnique selectedPrevious hSelectedPrevious).trans
        (hPreviousUnique previous hPrevious).symm
    subst selectedPrevious
    rcases alephSuccessorOperation_existsUnique hZF 𝕀 previous with
      ⟨_, _, hValueUnique⟩
    have hSelectedEq : selected = value :=
      (hValueUnique selected hSelectedValue).trans
        (hValueUnique value hValue).symm
    simpa [hSelectedEq] using hSelected

/-- Aleph 的极限步方程：极限指标处的值是此前全部 Aleph 值组成之集合的并。 -/
theorem aleph_limit_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω limit value : ℳ.Domain}
    (hLimit : ℳ.IsLimitOrdinal limit) :
    ℳ.IsAlephNumber 𝕀 ω limit value ↔
      ∃ range,
        (∀ member,
          ℳ.mem member range ↔
            ∃ index, ℳ.mem index limit ∧
              ℳ.IsAlephNumber 𝕀 ω index member) ∧
          ℳ.IsUnionOf value range := by
  have characterize {selected : ℳ.Domain}
      (hSelected :
        ℳ.IsAlephNumber 𝕀 ω limit selected) :
      ∃ range,
        (∀ member,
          ℳ.mem member range ↔
            ∃ index, ℳ.mem index limit ∧
              ℳ.IsAlephNumber 𝕀 ω index member) ∧
          ℳ.IsUnionOf selected range := by
    apply Structure.IsRecursionValue.limit_range hSelected
    · intro sequence output hSequence hOutput
      rcases exists_limitLengthSequenceWithUnion
          hZF 𝕀 hSequence.1 hLimit with
        ⟨_, hCanonical⟩
      rcases hOutput with hOutput | hOutput | hOutput
      · exact False.elim <|
          hOutput.1.not_limitLength hZF.1 hCanonical
      · rcases hOutput with ⟨_, hSuccessorLength, _⟩
        exact False.elim <|
          hSuccessorLength.not_limitLength hZF.1 hCanonical
      · exact hOutput
    · intro index hIndex first second hFirst hSecond
      rcases aleph_existsUnique hZF 𝕀 ω
          (hLimit.1.mem hIndex) with
        ⟨_, _, hUnique⟩
      exact
        (hUnique first hFirst).trans
          (hUnique second hSecond).symm
  constructor
  · exact characterize
  · rintro ⟨range, hRange, hUnion⟩
    rcases aleph_existsUnique hZF 𝕀 ω hLimit.1 with
      ⟨selected, hSelected, _⟩
    rcases characterize hSelected with
      ⟨selectedRange, hSelectedRange, hSelectedUnion⟩
    have hRangeEq : range = selectedRange := by
      apply hZF.1.eq_of_same_members
      intro member
      rw [hRange member, hSelectedRange member]
    subst selectedRange
    have hValueEq :=
      Structure.IsUnionOf.eq hZF.1 hUnion hSelectedUnion
    simpa [hValueEq] using hSelected

/--
若 Aleph 递归的首项 `ω` 是基数，则每个 Aleph 值都是基数。

后继步使用基数后继的定义，极限步使用引理 3.4(ii)：基数族的并仍是基数。
-/
theorem aleph_isCardinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω index value : ℳ.Domain}
    (hωCardinal : ℳ.IsCardinal 𝕀 ω)
    (hIndex : ℳ.IsOrdinal index)
    (hValue : ℳ.IsAlephNumber 𝕀 ω index value) :
    ℳ.IsCardinal 𝕀 value := by
  let env : Env ℳ 1 := {
    bound := fun _ => ω
    free := fun _ => Classical.choice ℳ.nonempty
  }
  let property : ℳ.Domain → Prop := fun current =>
    ∀ selected,
      ℳ.IsAlephNumber 𝕀 ω current selected →
        ℳ.IsCardinal 𝕀 selected
  have hProperty : property index := by
    apply Structure.IsOrdinal.induction hIndex property
    · rcases exists_separation hZF
          (alephValueCardinalAt 𝒞).neg env index with
        ⟨counterexamples, hCounterexamples⟩
      refine ⟨counterexamples, fun current => ?_⟩
      rw [hCounterexamples current]
      simp only [Definitional.Project.UnarySchema.neg,
        Definitional.Project.Formula.satisfies_neg_iff,
        satisfies_alephValueCardinalAt_iff 𝕀 hZF.1 env current]
      rfl
    · intro current hCurrent hPrevious selected hSelected
      rcases Structure.IsOrdinal.classify hZF.1 hCurrent with
        hZero | hSuccessor | hLimit
      · have hSelectedEq :=
          (aleph_zero_iff hZF 𝕀 hZero).mp hSelected
        simpa [hSelectedEq] using hωCardinal
      · rcases hSuccessor with
          ⟨predecessor, hPredecessor, hSuccessor⟩
        have hPredecessorMem : ℳ.mem predecessor current :=
          hSuccessor.predecessor_mem
        rcases (aleph_successor_iff hZF 𝕀
            hPredecessor hSuccessor).mp hSelected with
          ⟨previous, hPreviousValue, hOperation⟩
        have hPreviousCardinal :=
          hPrevious predecessor hPredecessorMem
            previous hPreviousValue
        rcases hOperation with hOperation | hOperation
        · exact hOperation.2.1
        · exact False.elim <|
            hOperation.1 hPreviousCardinal.1
      · rcases (aleph_limit_iff hZF 𝕀 hLimit).mp hSelected with
          ⟨range, hRange, hUnion⟩
        exact Structure.IsUnionOf.isCardinal_of_members
          hZF 𝕀 hUnion fun cardinal hCardinalRange => by
            rcases (hRange cardinal).mp hCardinalRange with
              ⟨predecessor, hPredecessor, hPredecessorValue⟩
            exact hPrevious predecessor hPredecessor
              cardinal hPredecessorValue
  exact hProperty value hValue

/--
在基数首项假设下，Aleph 的后继步就是通常的基数后继，而非总化定义的域外分支。
-/
theorem aleph_successor_cardinal_iff
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω predecessor successor value : ℳ.Domain}
    (hωCardinal : ℳ.IsCardinal 𝕀 ω)
    (hPredecessor : ℳ.IsOrdinal predecessor)
    (hSuccessor : ℳ.SuccessorOf successor predecessor) :
    ℳ.IsAlephNumber 𝕀 ω successor value ↔
      ∃ previous,
        ℳ.IsAlephNumber 𝕀 ω predecessor previous ∧
          ℳ.IsCardinalSuccessor 𝕀 value previous := by
  rw [aleph_successor_iff hZF 𝕀 hPredecessor hSuccessor]
  constructor
  · rintro ⟨previous, hPrevious, hOperation⟩
    have hPreviousCardinal :=
      aleph_isCardinal hZF 𝕀 hωCardinal
        hPredecessor hPrevious
    rcases hOperation with hOperation | hOperation
    · exact ⟨previous, hPrevious, hOperation.2⟩
    · exact False.elim <|
        hOperation.1 hPreviousCardinal.1
  · rintro ⟨previous, hPrevious, hSuccessorCardinal⟩
    exact ⟨previous, hPrevious,
      Or.inl
        ⟨(aleph_isCardinal hZF 𝕀 hωCardinal
          hPredecessor hPrevious).1,
          hSuccessorCardinal⟩⟩

/-- 在基数首项假设下，Aleph 枚举在序数指标上严格递增。 -/
theorem aleph_isIncreasingOnOrdinals
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω : ℳ.Domain}
    (hωCardinal : ℳ.IsCardinal 𝕀 ω) :
    ℳ.IsIncreasingOnOrdinals
      (fun index value =>
        ℳ.IsAlephNumber 𝕀 ω index value) := by
  let env : Env ℳ 1 := {
    bound := fun _ => ω
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hRelation :
      (Definitional.Project.BinarySchema.aleph 𝒞).denote env =
        fun index value =>
          ℳ.IsAlephNumber 𝕀 ω index value := by
    funext index value
    apply propext
    simpa [env] using
      Definitional.Project.BinarySchema.denote_aleph_iff
        𝕀 hZF.1 env index value
  have hIncreasing :
      ℳ.IsIncreasingOnOrdinals
        ((Definitional.Project.BinarySchema.aleph 𝒞).denote env) := by
    apply increasingOnOrdinals_of_progressive hZF env
      (Definitional.Project.BinarySchema.aleph 𝒞)
    intro α hα hPrevious predecessor
      hPredecessorMem predecessorValue αValue
      hPredecessorValue hαValue
    rw [hRelation] at hPrevious hPredecessorValue hαValue
    rcases hα.classify hZF.1 with
      hZero | hSuccessor | hLimit
    · exact False.elim <| hZero predecessor hPredecessorMem
    · rcases hSuccessor with
        ⟨immediate, hImmediateOrdinal, hSuccessor⟩
      rcases (aleph_successor_cardinal_iff
          hZF 𝕀 hωCardinal hImmediateOrdinal hSuccessor).mp
          hαValue with
        ⟨immediateValue, hImmediateValue, hValueSuccessor⟩
      have hImmediateMem : ℳ.mem immediate α :=
        hSuccessor.predecessor_mem
      have hImmediateValueMem : ℳ.mem immediateValue αValue :=
        hValueSuccessor.2.1
      rcases (hSuccessor predecessor).mp hPredecessorMem with
        hEarlier | hSame
      · have hEarlierValue :
            ℳ.mem predecessorValue immediateValue :=
          hPrevious immediate hImmediateMem
            predecessor hEarlier
            predecessorValue immediateValue
            hPredecessorValue hImmediateValue
        exact
          (aleph_isCardinal hZF 𝕀 hωCardinal hα hαValue).1.transitive
            immediateValue hImmediateValueMem
            predecessorValue hEarlierValue
      · have hPredecessorEq :=
          hZF.1.eq_of_same_members predecessor immediate hSame
        subst predecessor
        rcases aleph_existsUnique hZF 𝕀 ω hImmediateOrdinal with
          ⟨_, _, hUnique⟩
        have hValueEq : predecessorValue = immediateValue :=
          (hUnique predecessorValue hPredecessorValue).trans
            (hUnique immediateValue hImmediateValue).symm
        simpa [hValueEq] using hImmediateValueMem
    · rcases (aleph_limit_iff hZF 𝕀 hLimit).mp hαValue with
        ⟨range, hRange, hUnion⟩
      rcases hLimit.2.2 predecessor hPredecessorMem with
        ⟨larger, hLarger, hPredecessorLarger⟩
      rcases aleph_existsUnique hZF 𝕀 ω
          (hLimit.1.mem hLarger) with
        ⟨largerValue, hLargerValue, _⟩
      have hPredecessorValueLarger :
          ℳ.mem predecessorValue largerValue :=
        hPrevious larger hLarger
          predecessor hPredecessorLarger
          predecessorValue largerValue
          hPredecessorValue hLargerValue
      exact (hUnion predecessorValue).mpr
        ⟨largerValue,
          (hRange largerValue).mpr
            ⟨larger, hLarger, hLargerValue⟩,
          hPredecessorValueLarger⟩
  rw [hRelation] at hIncreasing
  exact hIncreasing

/-- Aleph 枚举在非零极限指标处连续。 -/
theorem aleph_isContinuousOnOrdinals
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (ω : ℳ.Domain) :
    ℳ.IsContinuousOnOrdinals
      (fun index value =>
        ℳ.IsAlephNumber 𝕀 ω index value) := by
  intro limit value hData
  exact (aleph_limit_iff hZF 𝕀 hData.1).mp hData.2

/-- 在基数首项假设下，Aleph 关系是序数类上的正规函数。 -/
theorem aleph_isNormalOrdinalFunction
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω : ℳ.Domain}
    (hωCardinal : ℳ.IsCardinal 𝕀 ω) :
    ℳ.IsNormalOrdinalFunction
      (fun index value =>
        ℳ.IsAlephNumber 𝕀 ω index value) :=
  ⟨⟨aleph_isClassFunctionOnOrdinals hZF 𝕀 ω,
      fun _ _ hIndex hValue =>
        (aleph_isCardinal hZF 𝕀 hωCardinal
          hIndex hValue).1⟩,
    aleph_isIncreasingOnOrdinals hZF 𝕀 hωCardinal,
    aleph_isContinuousOnOrdinals hZF 𝕀 ω⟩

/-- 在基数首项假设下，每个 Aleph 值都是不小于首项的无限基数。 -/
theorem aleph_isInfiniteCardinal
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω index value : ℳ.Domain}
    (hωCardinal : ℳ.IsCardinal 𝕀 ω)
    (hIndex : ℳ.IsOrdinal index)
    (hValue : ℳ.IsAlephNumber 𝕀 ω index value) :
    ℳ.IsInfiniteCardinal 𝕀 ω value := by
  refine ⟨aleph_isCardinal hZF 𝕀 hωCardinal hIndex hValue, ?_⟩
  rcases KP.exists_empty (ZF.modelsKP hZF) with
    ⟨zero, hZero⟩
  have hZeroOrdinal : ℳ.IsOrdinal zero :=
    Structure.IsOrdinal.of_no_members hZero
  have hZeroValue : ℳ.IsAlephNumber 𝕀 ω zero ω :=
    (aleph_zero_iff hZF 𝕀 hZero).mpr rfl
  rcases Structure.IsOrdinal.trichotomy hZF.1
      hZeroOrdinal hIndex
      (KP.exists_difference (ZF.modelsKP hZF))
      (KP.exists_intersection (ZF.modelsKP hZF)
        zero index) with
    hSame | hZeroIndex | hIndexZero
  · have hIndexEq :=
      hZF.1.eq_of_same_members zero index hSame
    subst index
    rcases aleph_existsUnique hZF 𝕀 ω hZeroOrdinal with
      ⟨_, _, hUnique⟩
    have hValueEq : value = ω :=
      (hUnique value hValue).trans
        (hUnique ω hZeroValue).symm
    subst value
    exact exists_inclusionInjection hZF 𝕀 fun _ h => h
  · have hωValue : ℳ.mem ω value :=
      aleph_isIncreasingOnOrdinals hZF 𝕀 hωCardinal
        zero index hZeroOrdinal hIndex hZeroIndex
        ω value hZeroValue hValue
    exact exists_inclusionInjection hZF 𝕀 <|
      (aleph_isCardinal hZF 𝕀 hωCardinal
        hIndex hValue).1.transitive ω hωValue
  · exact False.elim <| hZero index hIndexZero

end ZF

end SetTheory
end YesMetaZFC
