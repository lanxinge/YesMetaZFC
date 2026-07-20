import YesMetaZFC.SetTheory.Ord.Basic

/-!
# 超限归纳

本文件把序数良序上的最小反例论证整理为通用语义核，并将任意一元公式模式编译为
超限归纳闭句。ZF 使用全分离证明任意公式模式的超限归纳；KP 只对 `Δ₀` 模式导出
对应定理。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- `successor` 的成员恰为 `predecessor` 的成员以及其自身。 -/
def SuccessorOf (ℳ : SetTheory.Structure.{u})
    (successor predecessor : ℳ.Domain) : Prop :=
  ∀ value, ℳ.mem value successor ↔
    ℳ.mem value predecessor ∨ ℳ.SameMembers value predecessor

/-- 非零极限序数的纸面语义。 -/
def IsLimitOrdinal (ℳ : SetTheory.Structure.{u})
    (α : ℳ.Domain) : Prop :=
  ℳ.IsOrdinal α ∧
    (∃ value, ℳ.mem value α) ∧
    ∀ predecessor, ℳ.mem predecessor α →
      ∃ larger, ℳ.mem larger α ∧ ℳ.mem predecessor larger

end Structure

namespace Structure.SuccessorOf

/-- 后继对象包含其前驱。 -/
theorem predecessor_mem {ℳ : SetTheory.Structure.{u}}
    {successor predecessor : ℳ.Domain}
    (hSuccessor : ℳ.SuccessorOf successor predecessor) :
    ℳ.mem predecessor successor :=
  (hSuccessor predecessor).mpr (Or.inr fun _ => Iff.rfl)

register_prove_auto_sequent_rule predecessor_mem PRIORITY 200

end Structure.SuccessorOf

namespace Structure.IsOrdinal

/-- 序数上的最小反例归纳核。 -/
theorem induction {ℳ : SetTheory.Structure.{u}} {α : ℳ.Domain}
    (hα : Structure.IsOrdinal ℳ α) (property : ℳ.Domain → Prop)
    (hCounterexamples : ∃ counterexamples, ∀ value,
      ℳ.mem value counterexamples ↔ ℳ.mem value α ∧ ¬ property value)
    (hProgressive : ∀ β, Structure.IsOrdinal ℳ β →
      (∀ predecessor, ℳ.mem predecessor β → property predecessor) →
      property β) :
    property α := by
  classical
  apply Classical.byContradiction
  intro hαCounterexample
  have hBadPredecessor :
      ∃ predecessor, ℳ.mem predecessor α ∧ ¬ property predecessor := by
    apply Classical.byContradiction
    intro hNoBadPredecessor
    apply hαCounterexample
    apply hProgressive α hα
    intro predecessor hPredecessor
    set_option prove_auto.context.maxFacts 0 in
      prove_auto USE hNoBadPredecessor, hPredecessor
  rcases hCounterexamples with ⟨counterexamples, hCounterexamples⟩
  have hCounterexamplesSubset : ℳ.MemberSubset counterexamples α := by
    intro value hValue
    exact (hCounterexamples value).mp hValue |>.1
  have hCounterexamplesNonempty :
      ∃ value, ℳ.mem value counterexamples := by
    rcases hBadPredecessor with
      ⟨predecessor, hPredecessor, hProperty⟩
    exact ⟨predecessor, (hCounterexamples predecessor).mpr
      ⟨hPredecessor, hProperty⟩⟩
  rcases hα.wellOrder.least counterexamples hCounterexamplesSubset
      hCounterexamplesNonempty with
    ⟨least, hLeastCounterexample, hLeast⟩
  have hLeastData :=
    (hCounterexamples least).mp hLeastCounterexample
  have hLeastOrdinal : Structure.IsOrdinal ℳ least :=
    mem hα hLeastData.1
  apply hLeastData.2
  apply hProgressive least hLeastOrdinal
  intro predecessor hPredecessor
  apply Classical.byContradiction
  intro hPredecessorCounterexample
  have hPredecessorInα : ℳ.mem predecessor α :=
    hα.transitive least hLeastData.1 predecessor hPredecessor
  have hPredecessorInCounterexamples :
      ℳ.mem predecessor counterexamples :=
    (hCounterexamples predecessor).mpr
      ⟨hPredecessorInα, hPredecessorCounterexample⟩
  rcases hLeast predecessor hPredecessorInCounterexamples with
    hSameMembers | hLeastPredecessor
  · have hSelf : ℳ.mem predecessor predecessor :=
      (hSameMembers predecessor).mp hPredecessor
    exact hα.wellOrder.linear.irrefl predecessor
      hPredecessorInα hSelf
  · have hSelf : ℳ.mem least least :=
      hα.wellOrder.linear.trans least hLeastData.1
        predecessor hPredecessorInα least hLeastData.1
        hLeastPredecessor hPredecessor
    exact hα.wellOrder.linear.irrefl least hLeastData.1 hSelf

/--
固定上界内的序数归纳。

归纳步只需覆盖上界自身及其成员；这适合算子或闭包条件仅在给定序数以下成立的证明。
-/
theorem inductionWithin {ℳ : SetTheory.Structure.{u}} {α : ℳ.Domain}
    (hα : Structure.IsOrdinal ℳ α) (property : ℳ.Domain → Prop)
    (hCounterexamples : ∃ counterexamples, ∀ value,
      ℳ.mem value counterexamples ↔ ℳ.mem value α ∧ ¬ property value)
    (hProgressive : ∀ β, Structure.IsOrdinal ℳ β →
      (β = α ∨ ℳ.mem β α) →
      (∀ predecessor, ℳ.mem predecessor β →
        property predecessor) →
      property β) :
    property α := by
  let guarded : ℳ.Domain → Prop := fun β =>
    (β = α ∨ ℳ.mem β α) → property β
  rcases hCounterexamples with
    ⟨counterexamples, hCounterexamples⟩
  have hGuardedCounterexamples :
      ∃ guardedCounterexamples, ∀ value,
        ℳ.mem value guardedCounterexamples ↔
          ℳ.mem value α ∧ ¬ guarded value := by
    refine ⟨counterexamples, fun value => ?_⟩
    rw [hCounterexamples value]
    constructor
    · rintro ⟨hValue, hProperty⟩
      refine ⟨hValue, ?_⟩
      intro hGuarded
      exact hProperty (hGuarded (Or.inr hValue))
    · rintro ⟨hValue, hGuarded⟩
      refine ⟨hValue, ?_⟩
      intro hProperty
      apply hGuarded
      intro _
      exact hProperty
  have hGuarded : guarded α := by
    apply hα.induction guarded hGuardedCounterexamples
    intro β hβ hPrevious hWithin
    apply hProgressive β hβ hWithin
    intro predecessor hPredecessor
    apply hPrevious predecessor hPredecessor
    rcases hWithin with hEq | hMember
    · subst β
      exact Or.inr hPredecessor
    · exact Or.inr <|
        hα.transitive β hMember predecessor hPredecessor
  exact hGuarded (Or.inl rfl)

/-- 每个序数为空、为后继序数或为非零极限序数。 -/
theorem classify {ℳ : SetTheory.Structure.{u}} {α : ℳ.Domain}
    (hExt : Extensional ℳ) (hα : Structure.IsOrdinal ℳ α) :
    (∀ value, ¬ ℳ.mem value α) ∨
      (∃ predecessor, Structure.IsOrdinal ℳ predecessor ∧
        ℳ.SuccessorOf α predecessor) ∨
      ℳ.IsLimitOrdinal α := by
  classical
  by_cases hEmpty : ∀ value, ¬ ℳ.mem value α
  · exact Or.inl hEmpty
  · have hNonempty : ∃ value, ℳ.mem value α := by
      set_option prove_auto.context.maxFacts 0 in
        prove_auto USE hEmpty
    by_cases hGreatest : ∃ candidate,
        ℳ.mem candidate α ∧
          ∀ value, ℳ.mem value α →
            ℳ.mem value candidate ∨ ℳ.SameMembers value candidate
    · rcases hGreatest with
        ⟨predecessor, hPredecessor, hGreatest⟩
      apply Or.inr
      apply Or.inl
      refine ⟨predecessor, mem hα hPredecessor, ?_⟩
      intro value
      constructor
      · exact hGreatest value
      · intro hValue
        rcases hValue with hValuePredecessor | hSameMembers
        · exact hα.transitive predecessor hPredecessor
            value hValuePredecessor
        · have hEq := hExt.eq_of_same_members value predecessor
            hSameMembers
          prove_auto
    · apply Or.inr
      apply Or.inr
      refine ⟨hα, hNonempty, ?_⟩
      intro predecessor hPredecessor
      apply Classical.byContradiction
      intro hNoLarger
      apply hGreatest
      refine ⟨predecessor, hPredecessor, ?_⟩
      intro value hValue
      have hCompare :=
        hα.wellOrder.linear.compare value hValue
          predecessor hPredecessor
      prove_auto

end Structure.IsOrdinal

namespace Definitional
namespace Project

namespace Formula

/-- 对象公式中的空集条件与纸面语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isEmpty_iff {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) (set : Term depth) :
    satisfies env (isEmpty set) ↔
      ∀ value, ¬ ℳ.mem value (set.eval env) := by
  simp only [isEmpty, satisfies_forall_iff, satisfies_neg_iff,
    satisfies_mem_iff, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken]

/-- 对象公式中的后继关系与纸面语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isSuccessor_iff {ℳ : Structure.{u}}
    {depth : Nat} (env : Env ℳ depth)
    (successor predecessor : Term depth) :
    satisfies env (isSuccessor successor predecessor) ↔
      ℳ.SuccessorOf (successor.eval env) (predecessor.eval env) := by
  simp only [isSuccessor, Structure.SuccessorOf,
    Structure.SameMembers, satisfies_forall_iff,
    satisfies_iff_iff, satisfies_mem_iff,
    satisfies_disj_iff, satisfies_extensionalEq_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 对象公式中的极限序数定义与纸面语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isLimitOrdinal_iff {ℳ : Structure.{u}}
    {depth : Nat} (env : Env ℳ depth) (α : Term depth) :
    satisfies env (isLimitOrdinal α) ↔
      ℳ.IsLimitOrdinal (α.eval env) := by
  simp only [isLimitOrdinal, Structure.IsLimitOrdinal,
    satisfies_conj_iff, satisfies_isOrdinal_iff,
    satisfies_existsMem_iff, satisfies_forallMem_iff,
    satisfies_truth_iff, satisfies_mem_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, and_true,
    Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken]

end Formula

namespace UnarySchema

/-- 一元模式的补性质。 -/
def neg {parameterCount : Nat} (schema : UnarySchema parameterCount) :
    UnarySchema parameterCount where
  body := .neg schema.body
  freeClosed := by
    simpa [Formula.FreeClosed] using schema.freeClosed

/-- 该性质对序数递进。 -/
@[prove_auto_norm definition]
def progressiveCore {parameterCount : Nat}
    (schema : UnarySchema parameterCount) : Formula 1 parameterCount :=
  .forallE <| .imp (Formula.isOrdinal Term.newest) <|
    .imp
      (Formula.forallMem Term.newest <|
        schema.body.rename BoundEmbedding.unaryUnderOne)
      schema.body

/-- 该性质在所有序数上成立。 -/
@[prove_auto_norm definition]
def inductionCore {parameterCount : Nat}
    (schema : UnarySchema parameterCount) : Formula 1 parameterCount :=
  .forallE <| .imp (Formula.isOrdinal Term.newest) schema.body

/-- 性质在零序数处成立。 -/
@[prove_auto_norm definition]
def zeroCaseCore {parameterCount : Nat}
    (schema : UnarySchema parameterCount) : Formula 1 parameterCount :=
  .forallE <| .imp (Formula.isEmpty Term.newest) schema.body

/-- 性质对序数后继封闭。 -/
@[prove_auto_norm definition]
def successorCaseCore {parameterCount : Nat}
    (schema : UnarySchema parameterCount) : Formula 1 parameterCount :=
  .forallE <| .forallE <|
    .imp (Formula.isOrdinal (.bound 1)) <|
      .imp (schema.body.rename Fin.succ) <|
        .imp (Formula.isSuccessor Term.newest (.bound 1))
          (schema.body.rename BoundEmbedding.unaryUnderOne)

/-- 性质对非零极限序数封闭。 -/
@[prove_auto_norm definition]
def limitCaseCore {parameterCount : Nat}
    (schema : UnarySchema parameterCount) : Formula 1 parameterCount :=
  .forallE <| .imp (Formula.isLimitOrdinal Term.newest) <|
    .imp
      (Formula.forallMem Term.newest <|
        schema.body.rename BoundEmbedding.unaryUnderOne)
      schema.body

/-- 零、后继与非零极限三种闭包条件。 -/
def casesCore {parameterCount : Nat}
    (schema : UnarySchema parameterCount) : Formula 1 parameterCount :=
  .conj (zeroCaseCore schema) <|
    .conj (successorCaseCore schema) (limitCaseCore schema)

private theorem predecessorCondition_freeClosed {parameterCount : Nat}
    (schema : UnarySchema parameterCount) :
    (Formula.forallMem (Term.newest : Term (parameterCount + 1))
      (schema.body.rename BoundEmbedding.unaryUnderOne)).FreeClosed := by
  simp [Formula.forallMem, Formula.FreeClosed, schema.freeClosed]

private theorem progressiveCore_freeClosed {parameterCount : Nat}
    (schema : UnarySchema parameterCount) :
    (progressiveCore schema).FreeClosed := by
  simp [progressiveCore, Formula.isOrdinal, Formula.isTransitive,
    Formula.isWellOrderOn, Formula.isLinearOrderOn,
    Formula.isStrictPartialOrderOn, Formula.isIrreflexiveOn,
    Formula.isTransitiveOn, Formula.isLeastOf, Formula.lessOrEqual,
    Formula.forallMem, Formula.existsMem, Formula.subset,
    Formula.extensionalEq, Formula.FreeClosed, schema.freeClosed]

private theorem inductionCore_freeClosed {parameterCount : Nat}
    (schema : UnarySchema parameterCount) :
    (inductionCore schema).FreeClosed := by
  simp [inductionCore, Formula.isOrdinal, Formula.isTransitive,
    Formula.isWellOrderOn, Formula.isLinearOrderOn,
    Formula.isStrictPartialOrderOn, Formula.isIrreflexiveOn,
    Formula.isTransitiveOn, Formula.isLeastOf, Formula.lessOrEqual,
    Formula.forallMem, Formula.existsMem, Formula.subset,
    Formula.extensionalEq, Formula.FreeClosed, schema.freeClosed]

private theorem zeroCaseCore_freeClosed {parameterCount : Nat}
    (schema : UnarySchema parameterCount) :
    (zeroCaseCore schema).FreeClosed := by
  simp [zeroCaseCore, Formula.isEmpty, Formula.FreeClosed,
    schema.freeClosed]

private theorem successorCaseCore_freeClosed {parameterCount : Nat}
    (schema : UnarySchema parameterCount) :
    (successorCaseCore schema).FreeClosed := by
  simp [successorCaseCore, Formula.isOrdinal, Formula.isTransitive,
    Formula.isWellOrderOn, Formula.isLinearOrderOn,
    Formula.isStrictPartialOrderOn, Formula.isIrreflexiveOn,
    Formula.isTransitiveOn, Formula.isLeastOf, Formula.lessOrEqual,
    Formula.isSuccessor, Formula.forallMem, Formula.existsMem,
    Formula.subset, Formula.extensionalEq, Formula.FreeClosed,
    schema.freeClosed]

private theorem limitCaseCore_freeClosed {parameterCount : Nat}
    (schema : UnarySchema parameterCount) :
    (limitCaseCore schema).FreeClosed := by
  simp [limitCaseCore, Formula.isLimitOrdinal, Formula.isOrdinal,
    Formula.isTransitive, Formula.isWellOrderOn,
    Formula.isLinearOrderOn, Formula.isStrictPartialOrderOn,
    Formula.isIrreflexiveOn, Formula.isTransitiveOn,
    Formula.isLeastOf, Formula.lessOrEqual, Formula.forallMem,
    Formula.existsMem, Formula.subset, Formula.extensionalEq,
    Formula.FreeClosed, schema.freeClosed]

private theorem casesCore_freeClosed {parameterCount : Nat}
    (schema : UnarySchema parameterCount) :
    (casesCore schema).FreeClosed := by
  simpa [casesCore, Formula.FreeClosed] using
    And.intro (zeroCaseCore_freeClosed schema)
      (And.intro (successorCaseCore_freeClosed schema)
        (limitCaseCore_freeClosed schema))

/-- 超限归纳原理的闭句。 -/
@[prove_auto_unfold setTheory.ordinal.induction]
def inductionSentence {parameterCount : Nat}
    (schema : UnarySchema parameterCount) : Sentence :=
  Sentence.forallClosure
    (.imp (progressiveCore schema) (inductionCore schema)) <| by
      simpa [Formula.FreeClosed] using
        And.intro (progressiveCore_freeClosed schema)
          (inductionCore_freeClosed schema)

/-- 按零、后继与极限三类序数表述的超限归纳闭句。 -/
@[prove_auto_unfold setTheory.ordinal.induction.cases]
def caseInductionSentence {parameterCount : Nat}
    (schema : UnarySchema parameterCount) : Sentence :=
  Sentence.forallClosure
    (.imp (casesCore schema) (inductionCore schema)) <| by
      simpa [Formula.FreeClosed] using
        And.intro (casesCore_freeClosed schema)
          (inductionCore_freeClosed schema)

/-- 递进公式的语义正是序数上的递进性质。 -/
theorem satisfies_progressiveCore_iff {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (schema : UnarySchema parameterCount) :
    Formula.satisfies env (progressiveCore schema) ↔
      ∀ α, Structure.IsOrdinal ℳ α →
        (∀ predecessor, ℳ.mem predecessor α →
          Formula.satisfies (env.push predecessor) schema.body) →
        Formula.satisfies (env.push α) schema.body := by
  simp only [progressiveCore, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_rename,
    Env.reindex_push_unaryUnderOne, Definitional.Term.eval_newest]

/-- 归纳结论公式的语义是在所有序数上成立。 -/
theorem satisfies_inductionCore_iff {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (schema : UnarySchema parameterCount) :
    Formula.satisfies env (inductionCore schema) ↔
      ∀ α, Structure.IsOrdinal ℳ α →
        Formula.satisfies (env.push α) schema.body := by
  simp only [inductionCore, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isOrdinal_iff,
    Definitional.Term.eval_newest]

/-- 零序数闭包公式的直接语义。 -/
theorem satisfies_zeroCaseCore_iff {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (schema : UnarySchema parameterCount) :
    Formula.satisfies env (zeroCaseCore schema) ↔
      ∀ empty, (∀ value, ¬ ℳ.mem value empty) →
        Formula.satisfies (env.push empty) schema.body := by
  simp only [zeroCaseCore, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isEmpty_iff,
    Definitional.Term.eval_newest]

/-- 后继序数闭包公式的直接语义。 -/
theorem satisfies_successorCaseCore_iff {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (schema : UnarySchema parameterCount) :
    Formula.satisfies env (successorCaseCore schema) ↔
      ∀ predecessor successor,
        Structure.IsOrdinal ℳ predecessor →
        Formula.satisfies (env.push predecessor) schema.body →
        ℳ.SuccessorOf successor predecessor →
        Formula.satisfies (env.push successor) schema.body := by
  simp only [successorCaseCore, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_isSuccessor_iff, Formula.satisfies_rename,
    Env.reindex_push_succ, Env.reindex_push_unaryUnderOne,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest]

/-- 极限序数闭包公式的直接语义。 -/
theorem satisfies_limitCaseCore_iff {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (schema : UnarySchema parameterCount) :
    Formula.satisfies env (limitCaseCore schema) ↔
      ∀ α, ℳ.IsLimitOrdinal α →
        (∀ predecessor, ℳ.mem predecessor α →
          Formula.satisfies (env.push predecessor) schema.body) →
        Formula.satisfies (env.push α) schema.body := by
  simp only [limitCaseCore, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isLimitOrdinal_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_rename,
    Env.reindex_push_unaryUnderOne, Definitional.Term.eval_newest]

/-- 三类序数闭包公式的语义分解。 -/
theorem satisfies_casesCore_iff {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (schema : UnarySchema parameterCount) :
    Formula.satisfies env (casesCore schema) ↔
      Formula.satisfies env (zeroCaseCore schema) ∧
        Formula.satisfies env (successorCaseCore schema) ∧
          Formula.satisfies env (limitCaseCore schema) := by
  simp only [casesCore, Formula.satisfies_conj_iff]

/-- 渐进闭包与反例分离共同推出完整的超限归纳结论。 -/
theorem satisfies_inductionCore_of_progressive {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (schema : UnarySchema parameterCount)
    (hCounterexamples : ∀ α, ∃ counterexamples, ∀ value,
      ℳ.mem value counterexamples ↔
        ℳ.mem value α ∧
          ¬ Formula.satisfies (env.push value) schema.body)
    (hProgressive : Formula.satisfies env (progressiveCore schema)) :
    Formula.satisfies env (inductionCore schema) := by
  rw [satisfies_progressiveCore_iff] at hProgressive
  rw [satisfies_inductionCore_iff]
  intro α hα
  exact Structure.IsOrdinal.induction hα
    (fun value => Formula.satisfies (env.push value) schema.body)
    (hCounterexamples α) hProgressive

/-- 三类闭包与反例分离共同推出完整的超限归纳结论。 -/
theorem satisfies_inductionCore_of_cases {ℳ : Structure.{u}}
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (schema : UnarySchema parameterCount) (hExt : Extensional ℳ)
    (hCounterexamples : ∀ α, ∃ counterexamples, ∀ value,
      ℳ.mem value counterexamples ↔
        ℳ.mem value α ∧
          ¬ Formula.satisfies (env.push value) schema.body)
    (hCases : Formula.satisfies env (casesCore schema)) :
    Formula.satisfies env (inductionCore schema) := by
  rw [satisfies_casesCore_iff] at hCases
  rw [satisfies_zeroCaseCore_iff] at hCases
  rw [satisfies_successorCaseCore_iff] at hCases
  rw [satisfies_limitCaseCore_iff] at hCases
  rw [satisfies_inductionCore_iff]
  intro α hα
  apply Structure.IsOrdinal.induction hα
    (fun value => Formula.satisfies (env.push value) schema.body)
    (hCounterexamples α)
  intro current hCurrent hPredecessors
  rcases Structure.IsOrdinal.classify hExt hCurrent with
    hEmpty | hSuccessor | hLimit
  · exact hCases.1 current hEmpty
  · rcases hSuccessor with
      ⟨predecessor, hPredecessorOrdinal, hSuccessor⟩
    have hPredecessor : ℳ.mem predecessor current :=
      (hSuccessor predecessor).mpr <| Or.inr fun value => Iff.rfl
    exact hCases.2.1 predecessor current hPredecessorOrdinal
      (hPredecessors predecessor hPredecessor) hSuccessor
  · exact hCases.2.2 current hLimit hPredecessors

end UnarySchema

namespace Delta0UnarySchema

/-- `Δ₀` 一元模式对否定封闭。 -/
def neg {parameterCount : Nat}
    (schema : Delta0UnarySchema parameterCount) :
    Delta0UnarySchema parameterCount where
  toUnarySchema := schema.toUnarySchema.neg
  delta0 := .neg schema.delta0

end Delta0UnarySchema

end Project
end Definitional

namespace ZF

/-- ZF 分离为任意一元模式收集给定序数中的全部反例。 -/
private theorem ordinalCounterexamples {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF) {parameterCount : Nat}
    (schema : Definitional.Project.UnarySchema parameterCount)
    (env : Env ℳ parameterCount) :
    ∀ α, ∃ counterexamples, ∀ value,
      ℳ.mem value counterexamples ↔
        ℳ.mem value α ∧
          ¬ Definitional.Project.Formula.satisfies
            (env.push value) schema.body := by
  intro α
  simpa only [Definitional.Project.UnarySchema.neg,
    Definitional.Project.Formula.satisfies_neg_iff] using
    ZF.exists_separation hZF schema.neg env α

/-- ZF 证明任意公式模式的超限归纳。 -/
theorem ordInduction {parameterCount : Nat}
    (schema : Definitional.Project.UnarySchema parameterCount) :
    SemanticallyEntails.{0} SetTheory.ZF schema.inductionSentence := by
  intro ℳ hZF free
  change Definitional.Project.Formula.satisfies
    { bound := Fin.elim0, free := free }
    (Definitional.Project.Formula.forallClosure parameterCount
      (.imp schema.progressiveCore schema.inductionCore))
  rw [Definitional.Project.Formula.satisfies_forallClosure_iff]
  intro bound
  let env : Env ℳ parameterCount := {
    bound := bound
    free := free
  }
  change Definitional.Project.Formula.satisfies env
    (.imp schema.progressiveCore schema.inductionCore)
  rw [Definitional.Project.Formula.satisfies_imp_iff]
  exact
    (@Definitional.Project.UnarySchema.satisfies_inductionCore_of_progressive
      ℳ parameterCount env schema)
      (ordinalCounterexamples hZF schema env)

/-- ZF 中按零、后继与极限三类序数表述的超限归纳。 -/
theorem ordInductionCases {parameterCount : Nat}
    (schema : Definitional.Project.UnarySchema parameterCount) :
    SemanticallyEntails.{0} SetTheory.ZF
      schema.caseInductionSentence := by
  intro ℳ hZF free
  change Definitional.Project.Formula.satisfies
    { bound := Fin.elim0, free := free }
    (Definitional.Project.Formula.forallClosure parameterCount
      (.imp schema.casesCore schema.inductionCore))
  rw [Definitional.Project.Formula.satisfies_forallClosure_iff]
  intro bound
  let env : Env ℳ parameterCount := {
    bound := bound
    free := free
  }
  change Definitional.Project.Formula.satisfies env
    (.imp schema.casesCore schema.inductionCore)
  rw [Definitional.Project.Formula.satisfies_imp_iff]
  exact
    (@Definitional.Project.UnarySchema.satisfies_inductionCore_of_cases
      ℳ parameterCount env schema hZF.1)
      (ordinalCounterexamples hZF schema env)

end ZF

namespace KP

/-- KP 的 `Δ₀` 分离收集给定序数中的全部模式反例。 -/
private theorem delta0OrdinalCounterexamples {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) {parameterCount : Nat}
    (schema : Definitional.Project.Delta0UnarySchema parameterCount)
    (env : Env ℳ parameterCount) :
    ∀ α, ∃ counterexamples, ∀ value,
      ℳ.mem value counterexamples ↔
        ℳ.mem value α ∧
          ¬ Definitional.Project.Formula.satisfies
            (env.push value) schema.toUnarySchema.body := by
  intro α
  simpa only [Definitional.Project.Delta0UnarySchema.neg,
    Definitional.Project.UnarySchema.neg,
    Definitional.Project.Formula.satisfies_neg_iff] using
      KP.exists_separation hKP schema.neg env α

/-- KP 证明 `Δ₀` 公式模式的超限归纳。 -/
theorem delta0OrdInduction {parameterCount : Nat}
    (schema : Definitional.Project.Delta0UnarySchema parameterCount) :
    SemanticallyEntails.{0} SetTheory.KP
      schema.toUnarySchema.inductionSentence := by
  intro ℳ hKP free
  change Definitional.Project.Formula.satisfies
    { bound := Fin.elim0, free := free }
    (Definitional.Project.Formula.forallClosure parameterCount
      (.imp schema.toUnarySchema.progressiveCore
        schema.toUnarySchema.inductionCore))
  rw [Definitional.Project.Formula.satisfies_forallClosure_iff]
  intro bound
  let env : Env ℳ parameterCount := {
    bound := bound
    free := free
  }
  change Definitional.Project.Formula.satisfies env
    (.imp schema.toUnarySchema.progressiveCore
      schema.toUnarySchema.inductionCore)
  rw [Definitional.Project.Formula.satisfies_imp_iff]
  exact
    (@Definitional.Project.UnarySchema.satisfies_inductionCore_of_progressive
      ℳ parameterCount env schema.toUnarySchema)
      (delta0OrdinalCounterexamples hKP schema env)

/-- KP 中按零、后继与极限三类序数表述的 `Δ₀` 超限归纳。 -/
theorem delta0OrdInductionCases {parameterCount : Nat}
    (schema : Definitional.Project.Delta0UnarySchema parameterCount) :
    SemanticallyEntails.{0} SetTheory.KP
      schema.toUnarySchema.caseInductionSentence := by
  intro ℳ hKP free
  change Definitional.Project.Formula.satisfies
    { bound := Fin.elim0, free := free }
    (Definitional.Project.Formula.forallClosure parameterCount
      (.imp schema.toUnarySchema.casesCore
        schema.toUnarySchema.inductionCore))
  rw [Definitional.Project.Formula.satisfies_forallClosure_iff]
  intro bound
  let env : Env ℳ parameterCount := {
    bound := bound
    free := free
  }
  change Definitional.Project.Formula.satisfies env
    (.imp schema.toUnarySchema.casesCore
      schema.toUnarySchema.inductionCore)
  rw [Definitional.Project.Formula.satisfies_imp_iff]
  exact
    (@Definitional.Project.UnarySchema.satisfies_inductionCore_of_cases
      ℳ parameterCount env schema.toUnarySchema hKP.1)
      (delta0OrdinalCounterexamples hKP schema env)

end KP

end SetTheory
end YesMetaZFC
