import YesMetaZFC.SetTheory.Definitional.Project.Order

/-!
# 隶属序的纸面语义

本层把对象语言中的子集、传递集、隶属线序与隶属良序整理成普通 Lean 谓词。序数证明
可以直接沿用数学定义组合这些结构，而对象公式与 de Bruijn 环境之间的机械对应集中在
本文件处理。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- 两个对象具有完全相同的成员。 -/
def SameMembers (ℳ : Structure.{u}) (left right : ℳ.Domain) : Prop :=
  ∀ value, ℳ.mem value left ↔ ℳ.mem value right

/-- `left` 的每个成员也是 `right` 的成员。 -/
def MemberSubset (ℳ : Structure.{u}) (left right : ℳ.Domain) : Prop :=
  ∀ value, ℳ.mem value left → ℳ.mem value right

/-- `set` 关于隶属关系是传递的。 -/
def TransitiveSet (ℳ : Structure.{u}) (set : ℳ.Domain) : Prop :=
  ∀ middle, ℳ.mem middle set →
    ∀ value, ℳ.mem value middle → ℳ.mem value set

/-- 原始隶属关系线序 `carrier`。 -/
structure MembershipLinearOrder
    (ℳ : Structure.{u}) (carrier : ℳ.Domain) : Prop where
  irrefl :
    ∀ value, ℳ.mem value carrier → ¬ ℳ.mem value value
  trans :
    ∀ left, ℳ.mem left carrier →
      ∀ middle, ℳ.mem middle carrier →
        ∀ right, ℳ.mem right carrier →
          ℳ.mem left middle → ℳ.mem middle right → ℳ.mem left right
  compare :
    ∀ left, ℳ.mem left carrier →
      ∀ right, ℳ.mem right carrier →
        SameMembers ℳ left right ∨ ℳ.mem left right ∨ ℳ.mem right left

/-- 原始隶属关系良序 `carrier`。 -/
structure MembershipWellOrder
    (ℳ : Structure.{u}) (carrier : ℳ.Domain) : Prop where
  linear : MembershipLinearOrder ℳ carrier
  least :
    ∀ subset, MemberSubset ℳ subset carrier →
      (∃ value, ℳ.mem value subset) →
        ∃ candidate, ℳ.mem candidate subset ∧
          ∀ value, ℳ.mem value subset →
            SameMembers ℳ candidate value ∨ ℳ.mem candidate value

end Structure

namespace Definitional.Project.Formula

/-- 对象公式中的真子集定义与纸面语义一致。 -/
theorem satisfies_properSubset_iff {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) (left right : Term depth) :
    satisfies env (properSubset left right) ↔
      ℳ.MemberSubset (left.eval env) (right.eval env) ∧
        ¬ ℳ.SameMembers (left.eval env) (right.eval env) := by
  simp [properSubset, extensionalNe, Structure.MemberSubset,
    Structure.SameMembers, satisfies_conj_iff, satisfies_neg_iff,
    satisfies_subset_iff, satisfies_extensionalEq_iff]

/-- 对象公式中的隶属良序定义与纸面语义一致。 -/
theorem satisfies_membershipWellOrder_iff
    {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) (carrier : Term depth) :
    satisfies env
        (isWellOrderOn RelationSchema.membership TermVector.empty carrier) ↔
      ℳ.MembershipWellOrder (carrier.eval env) := by
  simp [isWellOrderOn, isLinearOrderOn, isStrictPartialOrderOn,
    isIrreflexiveOn, isTransitiveOn, isLeastOf, lessOrEqual,
    related_membership, satisfies_forallMem_iff, satisfies_existsMem_iff,
    satisfies_subset_iff, satisfies_extensionalEq_iff,
    satisfies_falsum_iff, satisfies_truth_iff, satisfies_mem_iff,
    satisfies_neg_iff, satisfies_conj_iff, satisfies_disj_iff,
    satisfies_imp_iff, satisfies_iff_iff, satisfies_forall_iff,
    satisfies_exists_iff, and_assoc]
  constructor
  · rintro ⟨hIrrefl, hTrans, hCompare, hLeast⟩
    refine ⟨⟨hIrrefl, hTrans, ?_⟩, ?_⟩
    · simpa [Structure.SameMembers] using hCompare
    · rintro subset hSubset ⟨value, hValue⟩
      exact hLeast subset hSubset value hValue
  · rintro ⟨⟨hIrrefl, hTrans, hCompare⟩, hLeast⟩
    refine ⟨hIrrefl, hTrans, ?_, ?_⟩
    · simpa [Structure.SameMembers] using hCompare
    · intro subset hSubset value hValue
      exact hLeast subset hSubset ⟨value, hValue⟩

end Definitional.Project.Formula

end SetTheory
end YesMetaZFC
