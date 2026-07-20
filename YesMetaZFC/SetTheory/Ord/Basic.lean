import YesMetaZFC.SetTheory.Ord.Notation
import YesMetaZFC.SetTheory.OrderSemantics
import YesMetaZFC.SetTheory.Separation
import YesMetaZFC.SetTheory.SetConstruction
import YesMetaZFC.SetTheory.Automation.Context

/-!
# 序数的基础定理

本文件在纸面语义视图上证明序数的基础闭包、包含与比较定理；对象公式定义独立放在
`Ord.Syntax`，供统一记号编译器与自动化共同消费。
-/

namespace YesMetaZFC
namespace SetTheory

namespace Structure

/-- `α` 是传递且由隶属关系良序的对象。 -/
structure IsOrdinal (ℳ : SetTheory.Structure.{u})
    (α : ℳ.Domain) : Prop where
  transitive : ℳ.TransitiveSet α
  wellOrder : ℳ.MembershipWellOrder α

namespace IsOrdinal

/-- 传递子集继承序数上的隶属良序。 -/
theorem of_transitive_subset {ℳ : SetTheory.Structure.{u}}
    {α subset : ℳ.Domain} (hα : IsOrdinal ℳ α)
    (hSubset : ℳ.MemberSubset subset α)
    (hTransitive : ℳ.TransitiveSet subset) :
    IsOrdinal ℳ subset := by
  refine ⟨hTransitive, ?_⟩
  refine ⟨?_, ?_⟩
  · exact {
      irrefl := fun value hValue =>
        hα.wellOrder.linear.irrefl value (hSubset value hValue)
      trans := fun left hLeft middle hMiddle right hRight =>
        hα.wellOrder.linear.trans left (hSubset left hLeft)
          middle (hSubset middle hMiddle) right (hSubset right hRight)
      compare := fun left hLeft right hRight =>
        hα.wellOrder.linear.compare left (hSubset left hLeft)
          right (hSubset right hRight)
    }
  · intro part hPartSubset hNonempty
    exact hα.wellOrder.least part
      (fun value hValue => hSubset value (hPartSubset value hValue))
      hNonempty

/--
没有成员的对象满足序数定义。

自动化候选：本定理本应注册为空对象的序数闭包规则；当前 `prove_auto` 会把全称无成员
前提展开为高成本 `FIX/INTRO` 路径，诊断中需要三轮迭代与十二次回溯，故暂不注册。
-/
theorem of_no_members {ℳ : SetTheory.Structure.{u}} {empty : ℳ.Domain}
    (hEmpty : ∀ value, ¬ ℳ.mem value empty) :
    IsOrdinal ℳ empty := by
  refine ⟨?_, ?_⟩
  · intro middle hMiddle
    exact False.elim (hEmpty middle hMiddle)
  · refine ⟨?_, ?_⟩
    · exact {
        irrefl := fun value hValue => False.elim (hEmpty value hValue)
        trans := fun left hLeft => False.elim (hEmpty left hLeft)
        compare := fun left hLeft => False.elim (hEmpty left hLeft)
      }
    · rintro subset hSubset ⟨value, hValue⟩
      exact False.elim (hEmpty value (hSubset value hValue))

/--
序数的每个成员仍然是序数。

该闭包规则的隐式对象参数可由目标与已知成员前提共同确定，适合进入声明级相继式索引。
-/
theorem mem {ℳ : SetTheory.Structure.{u}} {α β : ℳ.Domain}
    (hα : IsOrdinal ℳ α) (hβ : ℳ.mem β α) :
    IsOrdinal ℳ β := by
  have hSubset : ℳ.MemberSubset β α :=
    hα.transitive β hβ
  apply of_transitive_subset hα hSubset
  intro middle hMiddle value hValue
  exact hα.wellOrder.linear.trans value
    (hα.transitive middle (hSubset middle hMiddle) value hValue)
    middle (hSubset middle hMiddle) β hβ hValue hMiddle

register_prove_auto_sequent_rule IsOrdinal.mem PRIORITY 200

/-- 两个序数之间的真包含可由差集的最小元识别为隶属。 -/
theorem mem_of_properSubset {ℳ : SetTheory.Structure.{u}}
    {α β : ℳ.Domain} (hExt : Extensional ℳ)
    (hα : IsOrdinal ℳ α) (hβ : IsOrdinal ℳ β)
    (hProper : ℳ.MemberSubset α β ∧
      ¬ ℳ.SameMembers α β)
    (hDifference : ∃ difference, ∀ value,
      ℳ.mem value difference ↔
        ℳ.mem value β ∧ ¬ ℳ.mem value α) :
    ℳ.mem α β := by
  classical
  rcases hDifference with ⟨difference, hDifference⟩
  have hNonempty : ∃ value, ℳ.mem value difference := by
    apply Classical.byContradiction
    intro hEmpty
    apply hProper.2
    intro value
    constructor
    · exact hProper.1 value
    · intro hValueβ
      apply Classical.byContradiction
      intro hValueα
      exact hEmpty ⟨value,
        (hDifference value).2 ⟨hValueβ, hValueα⟩⟩
  have hDifferenceSubset : ℳ.MemberSubset difference β := by
    intro value hValue
    exact (hDifference value).1 hValue |>.1
  rcases hβ.wellOrder.least difference hDifferenceSubset hNonempty with
    ⟨γ, hγDifference, hLeast⟩
  have hγβ : ℳ.mem γ β :=
    (hDifference γ).1 hγDifference |>.1
  have hγNotα : ¬ ℳ.mem γ α :=
    (hDifference γ).1 hγDifference |>.2
  have hSameMembers : ℳ.SameMembers α γ := by
    intro value
    constructor
    · intro hValueα
      have hValueβ := hProper.1 value hValueα
      rcases hβ.wellOrder.linear.compare value hValueβ γ hγβ with
        hSame | hValueγ | hγValue
      · have hEq := hExt.eq_of_same_members value γ hSame
        exact False.elim (hγNotα (hEq ▸ hValueα))
      · exact hValueγ
      · exact False.elim
          (hγNotα (hα.transitive value hValueα γ hγValue))
    · intro hValueγ
      have hValueβ :=
        hβ.transitive γ hγβ value hValueγ
      apply Classical.byContradiction
      intro hValueα
      have hValueDifference :=
        (hDifference value).2 ⟨hValueβ, hValueα⟩
      rcases hLeast value hValueDifference with hSame | hγValue
      · have hEq := hExt.eq_of_same_members γ value hSame
        subst value
        exact hβ.wellOrder.linear.irrefl γ hγβ hValueγ
      · have hγγ :=
          hβ.wellOrder.linear.trans γ hγβ
            value hValueβ γ hγβ hγValue hValueγ
        exact hβ.wellOrder.linear.irrefl γ hγβ hγγ
  have hEq := hExt.eq_of_same_members α γ hSameMembers
  simpa [hEq] using hγβ

/-- 任意两个序数相等，或其中一个属于另一个。 -/
theorem trichotomy {ℳ : SetTheory.Structure.{u}} {α β : ℳ.Domain}
    (hExt : Extensional ℳ) (hα : IsOrdinal ℳ α)
    (hβ : IsOrdinal ℳ β)
    (hDifference : ∀ left right, ∃ difference, ∀ value,
      ℳ.mem value difference ↔
        ℳ.mem value right ∧ ¬ ℳ.mem value left)
    (hIntersection : ∃ intersection, ∀ value,
      ℳ.mem value intersection ↔
        ℳ.mem value α ∧ ℳ.mem value β) :
    ℳ.SameMembers α β ∨ ℳ.mem α β ∨ ℳ.mem β α := by
  classical
  rcases hIntersection with ⟨intersection, hIntersection⟩
  have hIntersectionα : ℳ.MemberSubset intersection α := by
    intro value hValue
    exact (hIntersection value).1 hValue |>.1
  have hIntersectionβ : ℳ.MemberSubset intersection β := by
    intro value hValue
    exact (hIntersection value).1 hValue |>.2
  have hIntersectionTransitive : ℳ.TransitiveSet intersection := by
    intro middle hMiddle value hValue
    have hMiddleBoth := (hIntersection middle).1 hMiddle
    exact (hIntersection value).2
      ⟨hα.transitive middle hMiddleBoth.1 value hValue,
        hβ.transitive middle hMiddleBoth.2 value hValue⟩
  have hIntersectionOrdinal :=
    of_transitive_subset hα hIntersectionα
      hIntersectionTransitive
  by_cases hSameα : ℳ.SameMembers intersection α
  · have hEqα :=
      hExt.eq_of_same_members intersection α hSameα
    have hαSubsetβ : ℳ.MemberSubset α β := by
      simpa [hEqα] using hIntersectionβ
    by_cases hSame : ℳ.SameMembers α β
    · exact Or.inl hSame
    · exact Or.inr (Or.inl <|
        mem_of_properSubset hExt hα hβ
          ⟨hαSubsetβ, hSame⟩ (hDifference α β))
  · have hIntersectionMemα :=
      mem_of_properSubset hExt hIntersectionOrdinal hα
        ⟨hIntersectionα, hSameα⟩
        (hDifference intersection α)
    by_cases hSameβ : ℳ.SameMembers intersection β
    · have hEqβ :=
        hExt.eq_of_same_members intersection β hSameβ
      have hβSubsetα : ℳ.MemberSubset β α := by
        simpa [hEqβ] using hIntersectionα
      by_cases hSame : ℳ.SameMembers α β
      · exact Or.inl hSame
      · exact Or.inr (Or.inr <|
          mem_of_properSubset hExt hβ hα
            ⟨hβSubsetα,
              fun h => hSame (fun value => (h value).symm)⟩
            (hDifference β α))
    · have hIntersectionMemβ :=
        mem_of_properSubset hExt hIntersectionOrdinal hβ
          ⟨hIntersectionβ, hSameβ⟩
          (hDifference intersection β)
      have hSelf : ℳ.mem intersection intersection :=
        (hIntersection intersection).2
          ⟨hIntersectionMemα, hIntersectionMemβ⟩
      exact False.elim
        (hIntersectionOrdinal.wellOrder.linear.irrefl
          intersection hSelf hSelf)

/-- 任一空对象都属于每个非空序数。 -/
theorem empty_mem_of_nonempty
    {ℳ : SetTheory.Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP)
    {α empty : ℳ.Domain}
    (hα : IsOrdinal ℳ α)
    (hNonempty : ∃ value, ℳ.mem value α)
    (hEmpty : ∀ value, ¬ ℳ.mem value empty) :
    ℳ.mem empty α := by
  have hEmptyOrdinal : IsOrdinal ℳ empty :=
    of_no_members hEmpty
  rcases trichotomy hKP.1 hEmptyOrdinal hα
      (KP.exists_difference hKP)
      (KP.exists_intersection hKP empty α) with
    hSame | hEmptyOrdinal | hOrdinalEmpty
  · have hEq :=
      hKP.1.eq_of_same_members empty α hSame
    subst α
    rcases hNonempty with ⟨value, hValue⟩
    exact False.elim (hEmpty value hValue)
  · exact hEmptyOrdinal
  · exact False.elim (hEmpty α hOrdinalEmpty)

/-- 序数族的并仍是序数。 -/
theorem of_union {ℳ : SetTheory.Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP)
    {union family : ℳ.Domain}
    (hUnion : ℳ.IsUnionOf union family)
    (hFamily : ∀ member, ℳ.mem member family → ℳ.IsOrdinal member) :
    ℳ.IsOrdinal union := by
  have memberOrdinal {value : ℳ.Domain} (hValue : ℳ.mem value union) :
      ℳ.IsOrdinal value := by
    rcases (hUnion value).mp hValue with
      ⟨member, hMemberFamily, hValueMember⟩
    exact (hFamily member hMemberFamily).mem hValueMember
  refine ⟨?_, ?_⟩
  · intro middle hMiddle value hValue
    rcases (hUnion middle).mp hMiddle with
      ⟨member, hMemberFamily, hMiddleMember⟩
    exact (hUnion value).mpr
      ⟨member, hMemberFamily,
        (hFamily member hMemberFamily).transitive
          middle hMiddleMember value hValue⟩
  · refine ⟨?_, ?_⟩
    · refine {
        irrefl := ?_
        trans := ?_
        compare := ?_
      }
      · intro value hValue hSelf
        exact memberOrdinal hValue |>.wellOrder.linear.irrefl
          value hSelf hSelf
      · intro left _ middle _ right hRight hLeftMiddle hMiddleRight
        exact memberOrdinal hRight |>.transitive
          middle hMiddleRight left hLeftMiddle
      · intro left hLeft right hRight
        exact trichotomy hKP.1
          (memberOrdinal hLeft) (memberOrdinal hRight)
          (KP.exists_difference hKP)
          (KP.exists_intersection hKP left right)
    · intro subset hSubset hNonempty
      rcases hNonempty with ⟨pivot, hPivotSubset⟩
      rcases (hUnion pivot).mp (hSubset pivot hPivotSubset) with
        ⟨container, hContainerFamily, hPivotContainer⟩
      have hContainerOrdinal := hFamily container hContainerFamily
      rcases KP.exists_intersection hKP subset container with
        ⟨intersection, hIntersection⟩
      have hIntersectionSubset : ℳ.MemberSubset intersection container := by
        intro value hValue
        exact (hIntersection value).mp hValue |>.2
      have hIntersectionNonempty : ∃ value, ℳ.mem value intersection :=
        ⟨pivot, (hIntersection pivot).mpr
          ⟨hPivotSubset, hPivotContainer⟩⟩
      rcases hContainerOrdinal.wellOrder.least intersection
          hIntersectionSubset hIntersectionNonempty with
        ⟨candidate, hCandidateIntersection, hLeastIntersection⟩
      have hCandidateData :=
        (hIntersection candidate).mp hCandidateIntersection
      refine ⟨candidate, hCandidateData.1, ?_⟩
      intro value hValueSubset
      have hCandidateOrdinal : ℳ.IsOrdinal candidate :=
        memberOrdinal (hSubset candidate hCandidateData.1)
      have hValueOrdinal : ℳ.IsOrdinal value :=
        memberOrdinal (hSubset value hValueSubset)
      rcases trichotomy hKP.1
          hCandidateOrdinal hValueOrdinal
          (KP.exists_difference hKP)
          (KP.exists_intersection hKP candidate value) with
        hSame | hCandidateValue | hValueCandidate
      · exact Or.inl hSame
      · exact Or.inr hCandidateValue
      · have hValueContainer : ℳ.mem value container :=
          hContainerOrdinal.transitive candidate hCandidateData.2
            value hValueCandidate
        have hValueIntersection : ℳ.mem value intersection :=
          (hIntersection value).mpr ⟨hValueSubset, hValueContainer⟩
        rcases hLeastIntersection value hValueIntersection with
          hSame | hCandidateValue
        · have hEq :=
            hKP.1.eq_of_same_members candidate value hSame
          subst value
          exact False.elim <|
            hCandidateOrdinal.wellOrder.linear.irrefl
              candidate hValueCandidate hValueCandidate
        · have hSelf : ℳ.mem value value :=
            hValueOrdinal.transitive candidate hCandidateValue
              value hValueCandidate
          exact False.elim <|
            hValueOrdinal.wellOrder.linear.irrefl value hSelf hSelf

end IsOrdinal
end Structure

namespace Definitional.Project.Formula

/-- 对象公式中的传递集定义与纸面语义一致。 -/
theorem satisfies_isTransitive_iff {ℳ : SetTheory.Structure.{u}}
    {depth : Nat} (env : Env ℳ depth) (set : Term depth) :
    satisfies env (isTransitive set) ↔
      ℳ.TransitiveSet (set.eval env) := by
  simp only [isTransitive, satisfies_forallMem_iff,
    satisfies_mem_iff, SetTheory.Structure.TransitiveSet,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 对象公式中的序数定义与纸面语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isOrdinal_iff {ℳ : SetTheory.Structure.{u}}
    {depth : Nat} (env : Env ℳ depth) (α : Term depth) :
    satisfies env (isOrdinal α) ↔
      Structure.IsOrdinal ℳ (α.eval env) := by
  simp only [isOrdinal, satisfies_conj_iff, satisfies_isTransitive_iff,
    satisfies_membershipWellOrder_iff]
  constructor
  · rintro ⟨hTransitive, hWellOrder⟩
    exact ⟨hTransitive, hWellOrder⟩
  · intro hα
    exact ⟨hα.transitive, hα.wellOrder⟩

end Definitional.Project.Formula

namespace Ordinal

/-- 每个序数都是传递集。 -/
@[prove_auto_unfold setTheory.ordinal.transitive]
def transitiveSentence : Definitional.Project.Sentence :=
  sentence! ⟪∀ α, Ord(α) → Trans(α)⟫

theorem transitive :
    SemanticallyEntails.{0} Theory.empty transitiveSentence := by
  intro ℳ _
  rw [Structure.satisfiesSentence_iff]
  intro free
  simp only [transitiveSentence, Definitional.Project.Sentence.ofFormula,
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_imp_iff]
  intro α hα
  rw [Definitional.Project.Formula.satisfies_isOrdinal_iff] at hα
  rw [Definitional.Project.Formula.satisfies_isTransitive_iff]
  exact hα.transitive

/-- 没有成员的对象是序数。 -/
@[prove_auto_unfold setTheory.ordinal.empty]
def emptyOrdSentence : Definitional.Project.Sentence :=
  sentence! ⟪∀ empty,
    (∀ element, element ∉ empty) → Ord(empty)⟫

theorem emptyOrd :
    SemanticallyEntails.{0} Theory.empty emptyOrdSentence := by
  intro ℳ _
  rw [Structure.satisfiesSentence_iff]
  intro free
  simp only [emptyOrdSentence, Definitional.Project.Sentence.ofFormula,
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_imp_iff]
  intro empty hEmpty
  simp only [
    Definitional.Project.Formula.satisfies_neg_iff,
    Definitional.Project.Formula.satisfies_mem_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken] at hEmpty
  rw [Definitional.Project.Formula.satisfies_isOrdinal_iff]
  exact Structure.IsOrdinal.of_no_members hEmpty

/-- 序数的任意成员仍然是序数。 -/
@[prove_auto_unfold setTheory.ordinal.membership]
def memOrdSentence : Definitional.Project.Sentence :=
  sentence! ⟪∀ α β,
    (Ord(α) ∧ β <ₒ α) → Ord(β)⟫

theorem memOrd :
    SemanticallyEntails.{0} Theory.empty memOrdSentence := by
  intro ℳ _
  rw [Structure.satisfiesSentence_iff]
  intro free
  simp only [memOrdSentence, Definitional.Project.Sentence.ofFormula,
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_imp_iff]
  intro α β hαβ
  simp only [Definitional.Project.Formula.satisfies_conj_iff,
    Definitional.Project.Formula.satisfies_mem_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken] at hαβ
  rw [Definitional.Project.Formula.satisfies_isOrdinal_iff] at hαβ ⊢
  exact Structure.IsOrdinal.mem hαβ.1 hαβ.2

/-- 对序数而言，真包含等价于严格隶属的正向部分。 -/
@[prove_auto_unfold setTheory.ordinal.comparison]
def subsetMemSentence : Definitional.Project.Sentence :=
  sentence! ⟪∀ α β,
    (Ord(α) ∧ Ord(β) ∧ α ⊊ β) → α <ₒ β⟫

theorem subsetMem :
    SemanticallyEntails.{0} SetTheory.KP subsetMemSentence := by
  intro ℳ hKP
  rw [Structure.satisfiesSentence_iff]
  intro free
  simp only [subsetMemSentence, Definitional.Project.Sentence.ofFormula,
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_imp_iff]
  intro α β h
  simp only [Definitional.Project.Formula.satisfies_conj_iff] at h
  rw [Definitional.Project.Formula.satisfies_isOrdinal_iff] at h
  rw [Definitional.Project.Formula.satisfies_isOrdinal_iff] at h
  rw [Definitional.Project.Formula.satisfies_properSubset_iff] at h
  rw [Definitional.Project.Formula.satisfies_mem_iff]
  simp only [Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  exact Structure.IsOrdinal.mem_of_properSubset hKP.1
    h.1 h.2.1 h.2.2 (KP.exists_difference hKP α β)

/-- 任意两个序数满足相等或严格隶属的三歧律。 -/
@[prove_auto_unfold setTheory.ordinal.comparison]
def trichotomySentence : Definitional.Project.Sentence :=
  sentence! ⟪∀ α β,
    (Ord(α) ∧ Ord(β)) →
      (α = β ∨ α <ₒ β ∨ β <ₒ α)⟫

theorem trichotomy :
    SemanticallyEntails.{0} SetTheory.KP trichotomySentence := by
  intro ℳ hKP
  rw [Structure.satisfiesSentence_iff]
  intro free
  simp only [trichotomySentence, Definitional.Project.Sentence.ofFormula,
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_imp_iff]
  intro α β h
  simp only [Definitional.Project.Formula.satisfies_conj_iff] at h
  rw [Definitional.Project.Formula.satisfies_isOrdinal_iff] at h
  rw [Definitional.Project.Formula.satisfies_isOrdinal_iff] at h
  have hCompare := Structure.IsOrdinal.trichotomy hKP.1
    h.1 h.2 (KP.exists_difference hKP)
    (KP.exists_intersection hKP α β)
  simpa only [Definitional.Project.Formula.satisfies_disj_iff,
    Definitional.Project.Formula.satisfies_extensionalEq_iff,
    Definitional.Project.Formula.satisfies_mem_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Structure.SameMembers] using hCompare

end Ordinal
end SetTheory
end YesMetaZFC
