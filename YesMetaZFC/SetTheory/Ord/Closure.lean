import YesMetaZFC.SetTheory.Ord.Normal

/-!
# 序数值闭包

本文件把“可定义类函数的值保持为序数”整理为可复用的一元归纳模式。具体序数算术
只需证明零、后继与极限步骤，不再各自复制反例分离和最小反例论证。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Definitional
namespace Project

namespace BinarySchema

/-- “当前输入处的全部函数值都是序数”的一元归纳模式。 -/
def ordinalValueClosure {parameterCount : Nat}
    (function : BinarySchema parameterCount) :
    UnarySchema parameterCount where
  body := .forallE <| .imp
    (Formula.related function
      (TermVector.boundParameters parameterCount 2)
      (.bound 1) Term.newest)
    (Formula.isOrdinal Term.newest)
  freeClosed := by
    simp [Formula.isOrdinal, Formula.isTransitive,
      Formula.isWellOrderOn, Formula.isLinearOrderOn,
      Formula.isStrictPartialOrderOn, Formula.isIrreflexiveOn,
      Formula.isTransitiveOn, Formula.isLeastOf,
      Formula.lessOrEqual, Formula.forallMem,
      Formula.existsMem, Formula.subset, Formula.extensionalEq,
      Formula.FreeClosed]

/-- “当前序数以下的函数值都严格小于当前函数值”的一元归纳模式。 -/
def ordinalIncreasingAt {parameterCount : Nat}
    (function : BinarySchema parameterCount) :
    UnarySchema parameterCount where
  body := .forallE <| .imp
    (.mem Term.newest (.bound 1)) <|
    .forallE <| .forallE <| .imp
      (.conj
        (Formula.related function
          (TermVector.boundParameters parameterCount 4)
          (.bound 2) (.bound 1))
        (Formula.related function
          (TermVector.boundParameters parameterCount 4)
          (.bound 3) Term.newest))
      (.mem (.bound 1) Term.newest)
  freeClosed := by
    simp [Formula.FreeClosed]

/-- “当前输入处的全部函数值都为空”的一元归纳模式。 -/
def emptyValueAt {parameterCount : Nat}
    (function : BinarySchema parameterCount) :
    UnarySchema parameterCount where
  body := .forallE <| .imp
    (Formula.related function
      (TermVector.boundParameters parameterCount 2)
      (.bound 1) Term.newest)
    (Formula.isEmpty Term.newest)
  freeClosed := by
    simp [Formula.isEmpty, Formula.FreeClosed]

/-- “当前输入处的全部函数值都非空”的一元归纳模式。 -/
def nonemptyValueAt {parameterCount : Nat}
    (function : BinarySchema parameterCount) :
    UnarySchema parameterCount where
  body := .forallE <| .imp
    (Formula.related function
      (TermVector.boundParameters parameterCount 2)
      (.bound 1) Term.newest)
    (.existsE <| .mem Term.newest (.bound 1))
  freeClosed := by
    simp [Formula.FreeClosed]

/-- “当前输入不大于当前函数值”的一元归纳模式。 -/
def inputLeValueAt {parameterCount : Nat}
    (function : BinarySchema parameterCount) :
    UnarySchema parameterCount where
  body := .forallE <| .imp
    (Formula.related function
      (TermVector.boundParameters parameterCount 2)
      (.bound 1) Term.newest) <|
    .disj (Formula.extensionalEq (.bound 1) Term.newest)
      (.mem (.bound 1) Term.newest)
  freeClosed := by
    simp [Formula.extensionalEq,
      Formula.FreeClosed]

/-- “两个类关系在当前输入处的任意函数值相等”的一元归纳模式。 -/
def agreeAt {parameterCount : Nat}
    (first second : BinarySchema parameterCount) :
    UnarySchema parameterCount where
  body := .forallE <| .forallE <| .imp
    (.conj
      (Formula.related first
        (TermVector.boundParameters parameterCount 3)
        (.bound 2) (.bound 1))
      (Formula.related second
        (TermVector.boundParameters parameterCount 3)
        (.bound 2) Term.newest))
    (Formula.extensionalEq (.bound 1) Term.newest)
  freeClosed := by
    simp [Formula.extensionalEq, Formula.FreeClosed]

end BinarySchema

namespace Formula

/-- 序数值闭包模式的语义正是“该输入处的全部函数值都是序数”。 -/
@[prove_auto_norm semantic]
theorem satisfies_ordinalValueClosure_iff
    {ℳ : Structure.{u}} {parameterCount : Nat}
    (env : Env ℳ parameterCount)
    (function : BinarySchema parameterCount)
    (α : ℳ.Domain) :
    satisfies (env.push α) function.ordinalValueClosure.body ↔
      ∀ value, function.denote env α value →
        ℳ.IsOrdinal value := by
  simp only [BinarySchema.ordinalValueClosure,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_related_iff, satisfies_isOrdinal_iff,
    TermVector.evalEnv_boundParameters_two,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest]

/-- 严格递增归纳模式的语义。 -/
@[prove_auto_norm semantic]
theorem satisfies_ordinalIncreasingAt_iff
    {ℳ : Structure.{u}} {parameterCount : Nat}
    (env : Env ℳ parameterCount)
    (function : BinarySchema parameterCount)
    (α : ℳ.Domain) :
    satisfies (env.push α) function.ordinalIncreasingAt.body ↔
      ∀ predecessor, ℳ.mem predecessor α →
        ∀ predecessorValue αValue,
          function.denote env predecessor predecessorValue →
          function.denote env α αValue →
            ℳ.mem predecessorValue αValue := by
  simp only [BinarySchema.ordinalIncreasingAt,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_conj_iff, satisfies_mem_iff,
    satisfies_related_iff,
    TermVector.evalEnv_boundParameters_four,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Definitional.Term.eval_newest, and_imp]

/-- 空值归纳模式的语义。 -/
@[prove_auto_norm semantic]
theorem satisfies_emptyValueAt_iff
    {ℳ : Structure.{u}} {parameterCount : Nat}
    (env : Env ℳ parameterCount)
    (function : BinarySchema parameterCount)
    (α : ℳ.Domain) :
    satisfies (env.push α) function.emptyValueAt.body ↔
      ∀ value, function.denote env α value →
        ∀ member, ¬ ℳ.mem member value := by
  simp only [BinarySchema.emptyValueAt,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_related_iff, satisfies_isEmpty_iff,
    TermVector.evalEnv_boundParameters_two,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest]

/-- 非空值归纳模式的语义。 -/
@[prove_auto_norm semantic]
theorem satisfies_nonemptyValueAt_iff
    {ℳ : Structure.{u}} {parameterCount : Nat}
    (env : Env ℳ parameterCount)
    (function : BinarySchema parameterCount)
    (α : ℳ.Domain) :
    satisfies (env.push α) function.nonemptyValueAt.body ↔
      ∀ value, function.denote env α value →
        ∃ member, ℳ.mem member value := by
  simp only [BinarySchema.nonemptyValueAt,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_exists_iff, satisfies_mem_iff,
    satisfies_related_iff,
    TermVector.evalEnv_boundParameters_two,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest]

/-- 输入不大于函数值模式的语义。 -/
@[prove_auto_norm semantic]
theorem satisfies_inputLeValueAt_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : BinarySchema parameterCount)
    (α : ℳ.Domain) :
    satisfies (env.push α) function.inputLeValueAt.body ↔
      ∀ value, function.denote env α value →
        α = value ∨ ℳ.mem α value := by
  simp only [BinarySchema.inputLeValueAt,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_disj_iff, satisfies_mem_iff,
    satisfies_related_iff,
    satisfies_extensionalEq_iff_eq hExt,
    TermVector.evalEnv_boundParameters_two,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Definitional.Term.eval_newest]

/-- 类关系逐点一致归纳模式的语义。 -/
@[prove_auto_norm semantic]
theorem satisfies_agreeAt_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (first second : BinarySchema parameterCount)
    (α : ℳ.Domain) :
    satisfies (env.push α) (first.agreeAt second).body ↔
      ∀ firstValue secondValue,
        first.denote env α firstValue →
        second.denote env α secondValue →
          firstValue = secondValue := by
  simp only [BinarySchema.agreeAt,
    satisfies_forall_iff, satisfies_imp_iff,
    satisfies_conj_iff, satisfies_related_iff,
    satisfies_extensionalEq_iff_eq hExt,
    TermVector.evalEnv_boundParameters_three,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push,
    Definitional.Term.eval_newest, and_imp]

end Formula

end Project
end Definitional

namespace ZF

/--
若可定义类函数在序数上全定义且单值，并且其序数值性质是递进的，
则它是序数值类函数。
-/
theorem ordinalClassFunction_of_progressive
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hClass : ℳ.IsClassFunctionOnOrdinals (function.denote env))
    (hProgressive : ∀ α, ℳ.IsOrdinal α →
      (∀ predecessor, ℳ.mem predecessor α →
        ∀ value, function.denote env predecessor value →
          ℳ.IsOrdinal value) →
      ∀ value, function.denote env α value →
        ℳ.IsOrdinal value) :
    ℳ.IsOrdinalClassFunction (function.denote env) := by
  refine ⟨hClass, ?_⟩
  intro α value hα hValue
  let property : ℳ.Domain → Prop := fun current =>
    ∀ output, function.denote env current output →
      ℳ.IsOrdinal output
  have hProperty : property α := by
    apply hα.induction property
    · rcases exists_separation hZF
          function.ordinalValueClosure.neg env α with
        ⟨counterexamples, hCounterexamples⟩
      refine ⟨counterexamples, fun current => ?_⟩
      rw [hCounterexamples current]
      simp [property, Definitional.Project.UnarySchema.neg,
        Definitional.Project.Formula.satisfies_neg_iff,
        Definitional.Project.Formula.satisfies_ordinalValueClosure_iff]
    · exact hProgressive
  exact hProperty value hValue

/--
若“当前序数以下的函数值都严格小于当前函数值”是递进性质，
则该可定义类关系在序数上严格递增。
-/
theorem increasingOnOrdinals_of_progressive
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hProgressive : ∀ α, ℳ.IsOrdinal α →
      (∀ predecessor, ℳ.mem predecessor α →
        ∀ earlier, ℳ.mem earlier predecessor →
          ∀ earlierValue predecessorValue,
            function.denote env earlier earlierValue →
            function.denote env predecessor predecessorValue →
              ℳ.mem earlierValue predecessorValue) →
      ∀ predecessor, ℳ.mem predecessor α →
        ∀ predecessorValue αValue,
          function.denote env predecessor predecessorValue →
          function.denote env α αValue →
            ℳ.mem predecessorValue αValue) :
    ℳ.IsIncreasingOnOrdinals (function.denote env) := by
  intro left right hLeft hRight hLeftRight
  let property : ℳ.Domain → Prop := fun α =>
    ∀ predecessor, ℳ.mem predecessor α →
      ∀ predecessorValue αValue,
        function.denote env predecessor predecessorValue →
        function.denote env α αValue →
          ℳ.mem predecessorValue αValue
  have hProperty : property right := by
    apply hRight.induction property
    · rcases exists_separation hZF
          function.ordinalIncreasingAt.neg env right with
        ⟨counterexamples, hCounterexamples⟩
      refine ⟨counterexamples, fun current => ?_⟩
      rw [hCounterexamples current]
      simp [property, Definitional.Project.UnarySchema.neg,
        Definitional.Project.Formula.satisfies_neg_iff,
        Definitional.Project.Formula.satisfies_ordinalIncreasingAt_iff]
    · exact hProgressive
  exact hProperty left hLeftRight

/--
若可定义类关系的“当前输入处全部值为空”性质是递进的，
则它在所有序数输入处都只取空值。
-/
theorem emptyValuesOnOrdinals_of_progressive
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hProgressive : ∀ α, ℳ.IsOrdinal α →
      (∀ predecessor, ℳ.mem predecessor α →
        ∀ value, function.denote env predecessor value →
          ∀ member, ¬ ℳ.mem member value) →
      ∀ value, function.denote env α value →
        ∀ member, ¬ ℳ.mem member value) :
    ∀ α, ℳ.IsOrdinal α →
      ∀ value, function.denote env α value →
        ∀ member, ¬ ℳ.mem member value := by
  intro α hα
  let property : ℳ.Domain → Prop := fun current =>
    ∀ value, function.denote env current value →
      ∀ member, ¬ ℳ.mem member value
  apply hα.induction property
  · rcases exists_separation hZF
        function.emptyValueAt.neg env α with
      ⟨counterexamples, hCounterexamples⟩
    refine ⟨counterexamples, fun current => ?_⟩
    rw [hCounterexamples current]
    simp [property, Definitional.Project.UnarySchema.neg,
      Definitional.Project.Formula.satisfies_neg_iff,
      Definitional.Project.Formula.satisfies_emptyValueAt_iff]
  · exact hProgressive

/--
若可定义类关系的“当前输入处全部值非空”性质是递进的，
则它在所有序数输入处都只取非空值。
-/
theorem nonemptyValuesOnOrdinals_of_progressive
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hProgressive : ∀ α, ℳ.IsOrdinal α →
      (∀ predecessor, ℳ.mem predecessor α →
        ∀ value, function.denote env predecessor value →
          ∃ member, ℳ.mem member value) →
      ∀ value, function.denote env α value →
        ∃ member, ℳ.mem member value) :
    ∀ α, ℳ.IsOrdinal α →
      ∀ value, function.denote env α value →
        ∃ member, ℳ.mem member value := by
  intro α hα
  let property : ℳ.Domain → Prop := fun current =>
    ∀ value, function.denote env current value →
      ∃ member, ℳ.mem member value
  apply hα.induction property
  · rcases exists_separation hZF
        function.nonemptyValueAt.neg env α with
      ⟨counterexamples, hCounterexamples⟩
    refine ⟨counterexamples, fun current => ?_⟩
    rw [hCounterexamples current]
    simp [property, Definitional.Project.UnarySchema.neg,
      Definitional.Project.Formula.satisfies_neg_iff,
      Definitional.Project.Formula.satisfies_nonemptyValueAt_iff]
  · exact hProgressive

/--
任意可定义正规序数函数都逐点不小于恒等函数。

后继步使用严格递增，极限步使用连续性；可定义性只用于收集最小反例。
-/
theorem normalValuesDominateInputs
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (function : Definitional.Project.BinarySchema parameterCount)
    (hNormal :
      ℳ.IsNormalOrdinalFunction (function.denote env)) :
    ∀ α, ℳ.IsOrdinal α →
      ∀ value, function.denote env α value →
        α = value ∨ ℳ.mem α value := by
  intro α hα
  let property : ℳ.Domain → Prop := fun current =>
    ∀ value, function.denote env current value →
      current = value ∨ ℳ.mem current value
  apply hα.induction property
  · rcases exists_separation hZF
        function.inputLeValueAt.neg env α with
      ⟨counterexamples, hCounterexamples⟩
    refine ⟨counterexamples, fun current => ?_⟩
    rw [hCounterexamples current]
    simp [property, Definitional.Project.UnarySchema.neg,
      Definitional.Project.Formula.satisfies_neg_iff,
      Definitional.Project.Formula.satisfies_inputLeValueAt_iff hZF.1]
  · intro current hCurrent hPrevious currentValue hCurrentValue
    have hCurrentValueOrdinal : ℳ.IsOrdinal currentValue :=
      hNormal.1.2 current currentValue hCurrent hCurrentValue
    rcases hCurrent.classify hZF.1 with
      hEmpty | hSuccessor | hLimit
    · by_cases hValueEmpty : ∀ member, ¬ ℳ.mem member currentValue
      · exact Or.inl <| hZF.1.eq_of_same_members _ _ <|
          fun member => iff_of_false (hEmpty member) (hValueEmpty member)
      · have hValueNonempty : ∃ member, ℳ.mem member currentValue := by
          apply Classical.byContradiction
          intro hNoMember
          apply hValueEmpty
          intro member hMember
          exact hNoMember ⟨member, hMember⟩
        exact Or.inr <|
          hCurrentValueOrdinal.empty_mem_of_nonempty
            (ZF.modelsKP hZF) hValueNonempty hEmpty
    · rcases hSuccessor with
        ⟨predecessor, hPredecessorOrdinal, hSuccessor⟩
      have hPredecessorMem : ℳ.mem predecessor current :=
        (hSuccessor predecessor).mpr
          (Or.inr fun _ => Iff.rfl)
      rcases hNormal.1.1 predecessor hPredecessorOrdinal with
        ⟨predecessorValue, hPredecessorValue, _⟩
      have hPredecessorValueCurrent :
          ℳ.mem predecessorValue currentValue :=
        hNormal.2.1 predecessor current
          hPredecessorOrdinal hCurrent hPredecessorMem
          predecessorValue currentValue
          hPredecessorValue hCurrentValue
      have hPredecessorCurrent :
          ℳ.mem predecessor currentValue := by
        rcases hPrevious predecessor hPredecessorMem
            predecessorValue hPredecessorValue with
          hEqual | hMember
        · simpa [hEqual] using hPredecessorValueCurrent
        · exact hCurrentValueOrdinal.transitive
            predecessorValue hPredecessorValueCurrent
            predecessor hMember
      have hSubset : ℳ.MemberSubset current currentValue := by
        intro member hMember
        rcases (hSuccessor member).mp hMember with
          hMemberPredecessor | hSame
        · exact hCurrentValueOrdinal.transitive
            predecessor hPredecessorCurrent
            member hMemberPredecessor
        · have hMemberEq :=
            hZF.1.eq_of_same_members member predecessor hSame
          simpa [hMemberEq] using hPredecessorCurrent
      by_cases hSame : ℳ.SameMembers current currentValue
      · exact Or.inl <| hZF.1.eq_of_same_members _ _ hSame
      · exact Or.inr <| Structure.IsOrdinal.mem_of_properSubset
          hZF.1 hCurrent hCurrentValueOrdinal
          ⟨hSubset, hSame⟩
          (KP.exists_difference (ZF.modelsKP hZF)
            current currentValue)
    · rcases hNormal.2.2 current currentValue
          ⟨hLimit, hCurrentValue⟩ with
        ⟨range, hRange, hUnion⟩
      have hSubset : ℳ.MemberSubset current currentValue := by
        intro member hMember
        rcases hLimit.2.2 member hMember with
          ⟨larger, hLarger, hMemberLarger⟩
        rcases hNormal.1.1 member
            (hLimit.1.mem hMember) with
          ⟨memberValue, hMemberValue, _⟩
        rcases hNormal.1.1 larger
            (hLimit.1.mem hLarger) with
          ⟨largerValue, hLargerValue, _⟩
        have hMemberValueLarger :
            ℳ.mem memberValue largerValue :=
          hNormal.2.1 member larger
            (hLimit.1.mem hMember) (hLimit.1.mem hLarger)
            hMemberLarger memberValue largerValue
            hMemberValue hLargerValue
        have hMemberLargerValue : ℳ.mem member largerValue := by
          rcases hPrevious member hMember
              memberValue hMemberValue with
            hEqual | hEarlier
          · simpa [hEqual] using hMemberValueLarger
          · have hLargerValueOrdinal :=
              hNormal.1.2 larger largerValue
                (hLimit.1.mem hLarger) hLargerValue
            exact hLargerValueOrdinal.transitive
              memberValue hMemberValueLarger member hEarlier
        exact (hUnion member).mpr
          ⟨largerValue,
            (hRange largerValue).mpr
              ⟨larger, hLarger, hLargerValue⟩,
            hMemberLargerValue⟩
      by_cases hSame : ℳ.SameMembers current currentValue
      · exact Or.inl <| hZF.1.eq_of_same_members _ _ hSame
      · exact Or.inr <| Structure.IsOrdinal.mem_of_properSubset
          hZF.1 hCurrent hCurrentValueOrdinal
          ⟨hSubset, hSame⟩
          (KP.exists_difference (ZF.modelsKP hZF)
            current currentValue)

/--
若两个可定义类关系在当前序数处取相同值的性质是递进的，
则它们在所有序数输入处逐点一致。
-/
theorem agreeOnOrdinals_of_progressive
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {parameterCount : Nat} (env : Env ℳ parameterCount)
    (first second : Definitional.Project.BinarySchema parameterCount)
    (hProgressive : ∀ α, ℳ.IsOrdinal α →
      (∀ predecessor, ℳ.mem predecessor α →
        ∀ firstValue secondValue,
          first.denote env predecessor firstValue →
          second.denote env predecessor secondValue →
            firstValue = secondValue) →
      ∀ firstValue secondValue,
        first.denote env α firstValue →
        second.denote env α secondValue →
          firstValue = secondValue) :
    ∀ α, ℳ.IsOrdinal α →
      ∀ firstValue secondValue,
        first.denote env α firstValue →
        second.denote env α secondValue →
          firstValue = secondValue := by
  intro α hα
  let property : ℳ.Domain → Prop := fun current =>
    ∀ firstValue secondValue,
      first.denote env current firstValue →
      second.denote env current secondValue →
        firstValue = secondValue
  apply hα.induction property
  · rcases exists_separation hZF
        (first.agreeAt second).neg env α with
      ⟨counterexamples, hCounterexamples⟩
    refine ⟨counterexamples, fun current => ?_⟩
    rw [hCounterexamples current]
    simp [property, Definitional.Project.UnarySchema.neg,
      Definitional.Project.Formula.satisfies_neg_iff,
      Definitional.Project.Formula.satisfies_agreeAt_iff hZF.1]
  · exact hProgressive

end ZF

end SetTheory
end YesMetaZFC
