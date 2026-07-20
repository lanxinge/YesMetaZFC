import YesMetaZFC.SetTheory.Definitional.Project.FlatPairing
import YesMetaZFC.SetTheory.Foundation
import YesMetaZFC.SetTheory.Ord.Arithmetic.Recursion

/-!
# 最小归纳集与自然数归纳

本文件为对象公式 `isInductive`、`isOmega` 补上纸面语义，并从 ZF 的无穷与分离公理
构造最小归纳集。随后证明最小归纳集是非零极限序数，并整理出供序数算术复用的自然数
归纳核。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- `set` 包含某个空集，并且对集合后继封闭。 -/
def IsInductive (ℳ : Structure.{u}) (set : ℳ.Domain) : Prop :=
  (∃ empty,
      (∀ value, ¬ ℳ.mem value empty) ∧
        ℳ.mem empty set) ∧
    ∀ predecessor, ℳ.mem predecessor set →
      ∃ successor,
        ℳ.SuccessorOf successor predecessor ∧
          ℳ.mem successor set

/-- `ω` 是包含于每个归纳集的归纳集。 -/
def IsOmega (ℳ : Structure.{u}) (ω : ℳ.Domain) : Prop :=
  ℳ.IsInductive ω ∧
    ∀ set, ℳ.IsInductive set → ℳ.MemberSubset ω set

namespace IsOmega

/-- 最小归纳集包含某个序数一。 -/
theorem exists_ordinalOne_mem {ℳ : Structure.{u}} {ω : ℳ.Domain}
    (hω : ℳ.IsOmega ω) :
    ∃ one, ℳ.IsOrdinalOne one ∧ ℳ.mem one ω := by
  rcases hω.1.1 with ⟨zero, hZero, hZeroOmega⟩
  rcases hω.1.2 zero hZeroOmega with
    ⟨one, hSuccessor, hOneOmega⟩
  exact ⟨one, ⟨zero, hZero, hSuccessor⟩, hOneOmega⟩

/--
最小归纳集上的自然数归纳核。

性质只需在 `ω` 中可分离、对空集成立并且对后继封闭。
-/
theorem induction {ℳ : Structure.{u}} {ω : ℳ.Domain}
    (hω : ℳ.IsOmega ω) (property : ℳ.Domain → Prop)
    (hPropertySet : ∃ propertySet, ∀ value,
      ℳ.mem value propertySet ↔
        ℳ.mem value ω ∧ property value)
    (hEmpty : ∀ empty,
      (∀ value, ¬ ℳ.mem value empty) → property empty)
    (hSuccessor : ∀ predecessor, ℳ.mem predecessor ω →
      property predecessor →
      ∀ successor, ℳ.SuccessorOf successor predecessor →
        property successor) :
    ∀ value, ℳ.mem value ω → property value := by
  rcases hPropertySet with ⟨propertySet, hPropertySet⟩
  have hPropertySetInductive : ℳ.IsInductive propertySet := by
    constructor
    · rcases hω.1.1 with ⟨empty, hEmptySet, hEmptyOmega⟩
      exact ⟨empty, hEmptySet,
        (hPropertySet empty).mpr
          ⟨hEmptyOmega, hEmpty empty hEmptySet⟩⟩
    · intro predecessor hPredecessor
      have hPredecessorData :=
        (hPropertySet predecessor).mp hPredecessor
      rcases hω.1.2 predecessor hPredecessorData.1 with
        ⟨successor, hSuccessorOf, hSuccessorOmega⟩
      exact ⟨successor, hSuccessorOf,
        (hPropertySet successor).mpr
          ⟨hSuccessorOmega,
            hSuccessor predecessor hPredecessorData.1
              hPredecessorData.2 successor hSuccessorOf⟩⟩
  intro value hValue
  exact (hPropertySet value).mp
    (hω.2 propertySet hPropertySetInductive value hValue) |>.2

end IsOmega

end Structure

namespace Definitional
namespace Project
namespace Formula

/-- 对象公式中的归纳集定义与纸面语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isInductive_iff {ℳ : Structure.{u}}
    {depth : Nat} (env : Env ℳ depth) (set : Term depth) :
    satisfies env (isInductive set) ↔
      ℳ.IsInductive (set.eval env) := by
  simp only [isInductive, satisfies_conj_iff, satisfies_exists_iff,
    satisfies_forallMem_iff, satisfies_conj_iff,
    satisfies_isEmpty_iff,
    satisfies_isSuccessor_iff, satisfies_mem_iff,
    Structure.IsInductive, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken, Term.eval_bound_zero_push,
    Term.eval_bound_one_push]

/-- 对象公式中的最小归纳集定义与纸面语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isOmega_iff {ℳ : Structure.{u}}
    {depth : Nat} (env : Env ℳ depth) (ω : Term depth) :
    satisfies env (isOmega ω) ↔
      ℳ.IsOmega (ω.eval env) := by
  simp only [isOmega, satisfies_conj_iff,
    satisfies_isInductive_iff, satisfies_forall_iff,
    satisfies_imp_iff, satisfies_subset_iff,
    Structure.IsOmega, Structure.MemberSubset,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

end Formula
end Project
end Definitional

namespace Axioms

/-- 无穷公理的项目核语义正是存在归纳集。 -/
theorem satisfies_infinity_iff {ℳ : Structure.{u}}
    (free : FreeVarId → ℳ.Domain) :
    Definitional.Project.Formula.satisfies
        ({ bound := Fin.elim0, free := free } : Env ℳ 0)
        infinity.formula ↔
      ∃ set, ℳ.IsInductive set := by
  unfold infinity
  dsimp only [Definitional.Project.Sentence.ofFormula]
  change
    Definitional.Project.Formula.satisfies
        ({ bound := Fin.elim0, free := free } : Env ℳ 0)
        (.existsE <| Definitional.Project.Formula.isInductive
          Definitional.Project.Term.newest) ↔
      ∃ set, ℳ.IsInductive set
  simp only [Definitional.Project.Formula.satisfies_exists_iff,
    Definitional.Project.Formula.satisfies_isInductive_iff,
    Definitional.Term.eval_newest]

end Axioms

namespace KP

/-- KP 的无穷公理给出一个归纳集。 -/
theorem exists_inductive {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) :
    ∃ set, ℳ.IsInductive set := by
  let free : FreeVarId → ℳ.Domain := fun _ =>
    Classical.choice ℳ.nonempty
  exact (Axioms.satisfies_infinity_iff free).mp <|
    hKP.2 Axioms.infinity Axiom.infinity free

end KP

namespace ZF

/-- “属于每个归纳集”的无参数分离模式。 -/
private def omegaSchema : Definitional.Project.UnarySchema 0 where
  body := .forallE <| .imp
    (Definitional.Project.Formula.isInductive
      Definitional.Project.Term.newest)
    (.mem (.bound 1) Definitional.Project.Term.newest)
  freeClosed := by
    simp [Definitional.Project.Formula.isInductive,
      Definitional.Project.Formula.isEmpty,
      Definitional.Project.Formula.isSuccessor,
      Definitional.Project.Formula.forallMem,
      Definitional.Project.Formula.extensionalEq,
      Definitional.Formula.FreeClosed,
      Definitional.Term.newest]

/-- ZF 中存在最小归纳集。 -/
theorem exists_omega {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF) :
    ∃ ω, ℳ.IsOmega ω := by
  rcases KP.exists_inductive (modelsKP hZF) with
    ⟨inductiveSet, hInductiveSet⟩
  let env : Env ℳ 0 := {
    bound := Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_separation hZF omegaSchema env inductiveSet with
    ⟨ω, hω⟩
  have hOmegaSemantic :
      ∀ value, ℳ.mem value ω ↔
        ℳ.mem value inductiveSet ∧
          ∀ set, ℳ.IsInductive set → ℳ.mem value set := by
    intro value
    rw [hω value]
    simp only [omegaSchema,
      Definitional.Project.Formula.satisfies_forall_iff,
      Definitional.Project.Formula.satisfies_imp_iff,
      Definitional.Project.Formula.satisfies_isInductive_iff,
      Definitional.Project.Formula.satisfies_mem_iff,
      Definitional.Project.Term.eval_bound_one_push,
      Definitional.Project.Term.eval_bound_zero_push,
      Definitional.Term.eval_newest]
  have hOmegaInductive : ℳ.IsInductive ω := by
    constructor
    · rcases hInductiveSet.1 with
        ⟨empty, hEmpty, hEmptyInductiveSet⟩
      refine ⟨empty, hEmpty, (hOmegaSemantic empty).mpr
        ⟨hEmptyInductiveSet, ?_⟩⟩
      intro set hSet
      rcases hSet.1 with ⟨setEmpty, hSetEmpty, hSetEmptyMem⟩
      have hEmptyEq : empty = setEmpty := by
        apply hZF.1.eq_of_same_members
        intro value
        exact iff_of_false (hEmpty value) (hSetEmpty value)
      simpa [hEmptyEq] using hSetEmptyMem
    · intro predecessor hPredecessor
      have hPredecessorData :=
        (hOmegaSemantic predecessor).mp hPredecessor
      rcases hInductiveSet.2 predecessor hPredecessorData.1 with
        ⟨successor, hSuccessor, hSuccessorInductiveSet⟩
      refine ⟨successor, hSuccessor,
        (hOmegaSemantic successor).mpr
          ⟨hSuccessorInductiveSet, ?_⟩⟩
      intro set hSet
      have hPredecessorSet := hPredecessorData.2 set hSet
      rcases hSet.2 predecessor hPredecessorSet with
        ⟨setSuccessor, hSetSuccessor, hSetSuccessorMem⟩
      have hSuccessorEq :=
        Structure.SuccessorOf.eq hZF.1
          hSuccessor hSetSuccessor
      simpa [hSuccessorEq] using hSetSuccessorMem
  exact ⟨ω, hOmegaInductive, fun set hSet value hValue =>
    (hOmegaSemantic value).mp hValue |>.2 set hSet⟩

/-- “当前对象是序数”的无参数分离模式。 -/
private def ordinalSchema : Definitional.Project.UnarySchema 0 where
  body := Definitional.Project.Formula.isOrdinal (.bound 0)
  freeClosed := by
    simp [Definitional.Project.Formula.isOrdinal,
      Definitional.Project.Formula.isTransitive,
      Definitional.Project.Formula.isWellOrderOn,
      Definitional.Project.Formula.isLinearOrderOn,
      Definitional.Project.Formula.isStrictPartialOrderOn,
      Definitional.Project.Formula.isIrreflexiveOn,
      Definitional.Project.Formula.isTransitiveOn,
      Definitional.Project.Formula.isLeastOf,
      Definitional.Project.Formula.lessOrEqual,
      Definitional.Project.Formula.forallMem,
      Definitional.Project.Formula.existsMem,
      Definitional.Project.Formula.subset,
      Definitional.Project.Formula.extensionalEq,
      Definitional.Formula.FreeClosed,
      Definitional.Term.newest]

/-- “当前对象包含于给定参数”的一参数分离模式。 -/
private def subsetParameterSchema : Definitional.Project.UnarySchema 1 where
  body := Definitional.Project.Formula.subset (.bound 0) (.bound 1)
  freeClosed := by
    simp [Definitional.Project.Formula.subset,
      Definitional.Formula.FreeClosed,
      Definitional.Term.freeSupport_bound]

/-- “当前自然数为空或为 `ω` 中某个自然数的后继”的分离模式。 -/
private def emptyOrSuccessorInOmegaSchema : Definitional.Project.UnarySchema 1 where
  body := .disj
    (Definitional.Project.Formula.isEmpty (.bound 0)) <|
    .existsE <| .conj
      (.mem Definitional.Project.Term.newest (.bound 2))
      (Definitional.Project.Formula.isSuccessor
        (.bound 1) Definitional.Project.Term.newest)
  freeClosed := by
    simp [Definitional.Project.Formula.isEmpty,
      Definitional.Project.Formula.isSuccessor,
      Definitional.Project.Formula.extensionalEq,
      Definitional.Formula.FreeClosed,
      Definitional.Term.newest]

/-- 固定左自然数后，序数加法在 `ω` 中封闭。 -/
private def ordinalAdditionClosedInOmegaSchema
    (𝒞 : Definitional.Project.OrderedPairConvention) :
    Definitional.Project.UnarySchema 2 where
  body := .forallE <| .imp
    (Definitional.Project.Formula.isOrdinalAddition 𝒞
      Definitional.Project.Term.newest (.bound 2) (.bound 1))
    (.mem Definitional.Project.Term.newest (.bound 3))
  freeClosed := by
    simp [Definitional.Project.Formula.isOrdinalAddition,
      Definitional.Project.Formula.related,
      Definitional.Formula.FreeClosed,
      Definitional.Term.newest]
    apply Definitional.Project.Formula.related_freeClosed_of_closed <;>
      simp [Definitional.TermVector.FreeClosed,
        Definitional.TermVector.singleton]

/-- 固定左自然数后，序数乘法在 `ω` 中封闭。 -/
private def ordinalMultiplicationClosedInOmegaSchema
    (𝒞 : Definitional.Project.OrderedPairConvention) :
    Definitional.Project.UnarySchema 2 where
  body := .forallE <| .imp
    (Definitional.Project.Formula.isOrdinalMultiplication 𝒞
      Definitional.Project.Term.newest (.bound 2) (.bound 1))
    (.mem Definitional.Project.Term.newest (.bound 3))
  freeClosed := by
    simp [Definitional.Project.Formula.isOrdinalMultiplication,
      Definitional.Project.Formula.related,
      Definitional.Formula.FreeClosed,
      Definitional.Term.newest]
    apply Definitional.Project.Formula.related_freeClosed_of_closed <;>
      simp [Definitional.TermVector.FreeClosed,
        Definitional.TermVector.singleton]

/-- 自然数加法封闭模式的模型语义。 -/
private theorem satisfies_ordinalAdditionClosedInOmegaSchema_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 2)
    (right : ℳ.Domain) :
    Definitional.Project.Formula.satisfies
        (env.push right)
        (ordinalAdditionClosedInOmegaSchema 𝒞).body ↔
      ∀ sum,
        ℳ.IsOrdinalAddition 𝕀 sum (env.bound 0) right →
          ℳ.mem sum (env.bound 1) := by
  simp only [ordinalAdditionClosedInOmegaSchema,
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_imp_iff,
    Definitional.Project.Formula.satisfies_isOrdinalAddition_iff 𝕀 hExt,
    Definitional.Project.Formula.satisfies_mem_iff,
    Definitional.Project.Term.eval_bound_zero_push,
    Definitional.Project.Term.eval_bound_one_push,
    Definitional.Project.Term.eval_bound_two_push,
    Definitional.Project.Term.eval_bound_three_push,
    Definitional.Term.eval_newest]
  rfl

/-- 自然数乘法封闭模式的模型语义。 -/
private theorem satisfies_ordinalMultiplicationClosedInOmegaSchema_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ) (env : Env ℳ 2)
    (right : ℳ.Domain) :
    Definitional.Project.Formula.satisfies
        (env.push right)
        (ordinalMultiplicationClosedInOmegaSchema 𝒞).body ↔
      ∀ product,
        ℳ.IsOrdinalMultiplication 𝕀 product (env.bound 0) right →
          ℳ.mem product (env.bound 1) := by
  simp only [ordinalMultiplicationClosedInOmegaSchema,
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_imp_iff,
    Definitional.Project.Formula.satisfies_isOrdinalMultiplication_iff
      𝕀 hExt,
    Definitional.Project.Formula.satisfies_mem_iff,
    Definitional.Project.Term.eval_bound_zero_push,
    Definitional.Project.Term.eval_bound_one_push,
    Definitional.Project.Term.eval_bound_two_push,
    Definitional.Project.Term.eval_bound_three_push,
    Definitional.Term.eval_newest]
  rfl

end ZF

namespace Structure.IsOmega

/-- 最小归纳集的每个成员都是序数。 -/
theorem members_areOrdinals {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {ω : ℳ.Domain} (hω : ℳ.IsOmega ω) :
    ∀ value, ℳ.mem value ω → ℳ.IsOrdinal value := by
  let env : Env ℳ 0 := {
    bound := Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply hω.induction
      (fun value => ℳ.IsOrdinal value)
  · rcases ZF.exists_separation hZF ZF.ordinalSchema
        env ω with ⟨ordinals, hOrdinals⟩
    refine ⟨ordinals, fun value => ?_⟩
    rw [hOrdinals value]
    constructor
    · rintro ⟨hValue, hValueOrdinal⟩
      exact ⟨hValue,
        (Definitional.Project.Formula.satisfies_isOrdinal_iff
          (env.push value) (.bound 0)).mp hValueOrdinal⟩
    · rintro ⟨hValue, hValueOrdinal⟩
      exact ⟨hValue,
        (Definitional.Project.Formula.satisfies_isOrdinal_iff
          (env.push value) (.bound 0)).mpr hValueOrdinal⟩
  · intro empty hEmpty
    exact Structure.IsOrdinal.of_no_members hEmpty
  · intro predecessor _ hPredecessor successor hSuccessor
    exact KP.successor_isOrdinal (ZF.modelsKP hZF)
      hPredecessor hSuccessor

/-- 最小归纳集是传递集。 -/
theorem transitive {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {ω : ℳ.Domain} (hω : ℳ.IsOmega ω) :
    ℳ.TransitiveSet ω := by
  let env : Env ℳ 1 := {
    bound := fun _ => ω
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hMembersClosed :
      ∀ predecessor, ℳ.mem predecessor ω →
        ℳ.MemberSubset predecessor ω := by
    apply hω.induction
        (fun predecessor => ℳ.MemberSubset predecessor ω)
    · rcases ZF.exists_separation hZF
          ZF.subsetParameterSchema env ω with
        ⟨closed, hClosed⟩
      refine ⟨closed, fun value => ?_⟩
      rw [hClosed value]
      constructor
      · rintro ⟨hValue, hSubset⟩
        exact ⟨hValue,
          (Definitional.Project.Formula.satisfies_subset_iff
            (env.push value) (.bound 0) (.bound 1)).mp
            hSubset⟩
      · rintro ⟨hValue, hSubset⟩
        exact ⟨hValue,
          (Definitional.Project.Formula.satisfies_subset_iff
            (env.push value) (.bound 0) (.bound 1)).mpr
            hSubset⟩
    · intro empty hEmpty value hValue
      exact False.elim (hEmpty value hValue)
    · intro predecessor hPredecessor hSubset
        successor hSuccessor value hValue
      rcases (hSuccessor value).mp hValue with
        hValuePredecessor | hSame
      · exact hSubset value hValuePredecessor
      · have hEq :=
          hZF.1.eq_of_same_members value predecessor hSame
        simpa [hEq] using hPredecessor
  intro predecessor hPredecessor
  exact hMembersClosed predecessor hPredecessor

/-- `ω` 中每个非零成员都是某个仍属于 `ω` 的自然数的后继。 -/
theorem exists_predecessor_of_mem_of_nonempty
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {ω number : ℳ.Domain} (hω : ℳ.IsOmega ω)
    (hNumberOmega : ℳ.mem number ω)
    (hNumberNonempty : ∃ member, ℳ.mem member number) :
    ∃ predecessor,
      ℳ.mem predecessor ω ∧
        ℳ.SuccessorOf number predecessor := by
  let env : Env ℳ 1 := {
    bound := fun _ => ω
    free := fun _ => Classical.choice ℳ.nonempty
  }
  let property : ℳ.Domain → Prop := fun current =>
    (∀ member, ¬ ℳ.mem member current) ∨
      ∃ predecessor,
        ℳ.mem predecessor ω ∧
          ℳ.SuccessorOf current predecessor
  have hProperty :
      ∀ current, ℳ.mem current ω → property current := by
    apply hω.induction property
    · rcases ZF.exists_separation hZF
          ZF.emptyOrSuccessorInOmegaSchema env ω with
        ⟨classified, hClassified⟩
      refine ⟨classified, fun current => ?_⟩
      rw [hClassified current]
      simp [ZF.emptyOrSuccessorInOmegaSchema,
        Definitional.Project.Formula.satisfies_disj_iff,
        Definitional.Project.Formula.satisfies_exists_iff,
        Definitional.Project.Formula.satisfies_conj_iff,
        Definitional.Project.Formula.satisfies_mem_iff,
        Definitional.Project.Formula.satisfies_isEmpty_iff,
        Definitional.Project.Formula.satisfies_isSuccessor_iff,
        property, env]
      intro _
      rfl
    · intro empty hEmpty
      exact Or.inl hEmpty
    · intro predecessor hPredecessor _ successor hSuccessor
      exact Or.inr ⟨predecessor, hPredecessor, hSuccessor⟩
  rcases hProperty number hNumberOmega with
    hEmpty | hSuccessor
  · rcases hNumberNonempty with ⟨member, hMember⟩
    exact False.elim (hEmpty member hMember)
  · exact hSuccessor

/-- 最小归纳集由隶属关系良序。 -/
theorem membershipWellOrder {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {ω : ℳ.Domain} (hω : ℳ.IsOmega ω) :
    ℳ.MembershipWellOrder ω := by
  have hMembersOrdinal := hω.members_areOrdinals hZF
  refine ⟨?_, ?_⟩
  · refine {
      irrefl := ?_
      trans := ?_
      compare := ?_
    }
    · intro value hValue hSelf
      exact (hMembersOrdinal value hValue).wellOrder.linear.irrefl
        value hSelf hSelf
    · intro left _ middle _ right hRight hLeftMiddle hMiddleRight
      exact (hMembersOrdinal right hRight).transitive
        middle hMiddleRight left hLeftMiddle
    · intro left hLeft right hRight
      exact Structure.IsOrdinal.trichotomy hZF.1
        (hMembersOrdinal left hLeft)
        (hMembersOrdinal right hRight)
        (KP.exists_difference (ZF.modelsKP hZF))
        (KP.exists_intersection (ZF.modelsKP hZF) left right)
  · intro subset hSubset hNonempty
    rcases KP.exists_mem_minimal
        (ZF.modelsKP hZF) hNonempty with
      ⟨minimal, hMinimalSubset, hMinimal⟩
    refine ⟨minimal, hMinimalSubset, ?_⟩
    intro value hValueSubset
    rcases Structure.IsOrdinal.trichotomy hZF.1
        (hMembersOrdinal minimal (hSubset minimal hMinimalSubset))
        (hMembersOrdinal value (hSubset value hValueSubset))
        (KP.exists_difference (ZF.modelsKP hZF))
        (KP.exists_intersection (ZF.modelsKP hZF)
          minimal value) with
      hSame | hMinimalValue | hValueMinimal
    · exact Or.inl hSame
    · exact Or.inr hMinimalValue
    · exact False.elim (hMinimal value hValueSubset hValueMinimal)

/-- 最小归纳集是序数。 -/
theorem isOrdinal {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {ω : ℳ.Domain} (hω : ℳ.IsOmega ω) :
    ℳ.IsOrdinal ω :=
  ⟨hω.transitive hZF,
    hω.membershipWellOrder hZF⟩

/-- 最小归纳集是非零极限序数。 -/
theorem isLimitOrdinal {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF)
    {ω : ℳ.Domain} (hω : ℳ.IsOmega ω) :
    ℳ.IsLimitOrdinal ω := by
  refine ⟨hω.isOrdinal hZF, ?_, ?_⟩
  · rcases hω.1.1 with ⟨empty, _, hEmptyOmega⟩
    exact ⟨empty, hEmptyOmega⟩
  · intro predecessor hPredecessor
    rcases hω.1.2 predecessor hPredecessor with
      ⟨successor, hSuccessor, hSuccessorOmega⟩
    exact ⟨successor, hSuccessorOmega,
      (hSuccessor predecessor).mpr
        (Or.inr fun _ => Iff.rfl)⟩

end Structure.IsOmega

namespace ZF

/-- 两个自然数的序数加法值仍是自然数。 -/
theorem ordinalAddition_mem_omega
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω left right sum : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hLeft : ℳ.mem left ω)
    (hRight : ℳ.mem right ω)
    (hSum : ℳ.IsOrdinalAddition 𝕀 sum left right) :
    ℳ.mem sum ω := by
  let env : Env ℳ 2 := {
    bound := fun index => Fin.cases left (fun _ => ω) index
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hClosed :
      ∀ current, ℳ.mem current ω →
        ∀ value,
          ℳ.IsOrdinalAddition 𝕀 value left current →
            ℳ.mem value ω := by
    apply hω.induction
        (fun current =>
          ∀ value,
            ℳ.IsOrdinalAddition 𝕀 value left current →
              ℳ.mem value ω)
    · rcases exists_separation hZF
          (ordinalAdditionClosedInOmegaSchema 𝒞) env ω with
        ⟨closed, hClosed⟩
      refine ⟨closed, fun current => ?_⟩
      rw [hClosed current,
        satisfies_ordinalAdditionClosedInOmegaSchema_iff
          𝕀 hZF.1 env current]
      change
        (ℳ.mem current ω ∧
          ∀ value,
            ℳ.IsOrdinalAddition 𝕀 value left current →
              ℳ.mem value ω) ↔
        ℳ.mem current ω ∧
          ∀ value,
            ℳ.IsOrdinalAddition 𝕀 value left current →
              ℳ.mem value ω
      rfl
    · intro empty hEmpty value hValue
      have hValueEq :=
        (ordinalAddition_zero_iff hZF 𝕀 hEmpty).mp hValue
      simpa [hValueEq] using hLeft
    · intro predecessor hPredecessor hPredecessorClosed
        successor hSuccessor value hValue
      have hPredecessorOrdinal :=
        hω.members_areOrdinals hZF predecessor hPredecessor
      rcases (ordinalAddition_successor_iff
          hZF 𝕀 hPredecessorOrdinal hSuccessor).mp hValue with
        ⟨previous, hPrevious, hValueSuccessor⟩
      have hPreviousOmega :=
        hPredecessorClosed previous hPrevious
      rcases hω.1.2 previous hPreviousOmega with
        ⟨selected, hSelectedSuccessor, hSelectedOmega⟩
      have hSelectedEq :=
        Structure.SuccessorOf.eq hZF.1
          hSelectedSuccessor hValueSuccessor
      simpa [hSelectedEq] using hSelectedOmega
  exact hClosed right hRight sum hSum

/-- 两个自然数的序数乘法值仍是自然数。 -/
theorem ordinalMultiplication_mem_omega
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {ω left right product : ℳ.Domain}
    (hω : ℳ.IsOmega ω)
    (hLeft : ℳ.mem left ω)
    (hRight : ℳ.mem right ω)
    (hProduct : ℳ.IsOrdinalMultiplication 𝕀 product left right) :
    ℳ.mem product ω := by
  let env : Env ℳ 2 := {
    bound := fun index => Fin.cases left (fun _ => ω) index
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hClosed :
      ∀ current, ℳ.mem current ω →
        ∀ value,
          ℳ.IsOrdinalMultiplication 𝕀 value left current →
            ℳ.mem value ω := by
    apply hω.induction
        (fun current =>
          ∀ value,
            ℳ.IsOrdinalMultiplication 𝕀 value left current →
              ℳ.mem value ω)
    · rcases exists_separation hZF
          (ordinalMultiplicationClosedInOmegaSchema 𝒞) env ω with
        ⟨closed, hClosed⟩
      refine ⟨closed, fun current => ?_⟩
      rw [hClosed current,
        satisfies_ordinalMultiplicationClosedInOmegaSchema_iff
          𝕀 hZF.1 env current]
      change
        (ℳ.mem current ω ∧
          ∀ value,
            ℳ.IsOrdinalMultiplication 𝕀 value left current →
              ℳ.mem value ω) ↔
        ℳ.mem current ω ∧
          ∀ value,
            ℳ.IsOrdinalMultiplication 𝕀 value left current →
              ℳ.mem value ω
      rfl
    · intro empty hEmpty value hValue
      have hValueEmpty :=
        (ordinalMultiplication_zero_iff
          hZF 𝕀
          (hω.members_areOrdinals hZF left hLeft)
          hEmpty).mp hValue
      rcases hω.1.1 with
        ⟨omegaEmpty, hOmegaEmpty, hOmegaEmptyMem⟩
      have hValueEq : value = omegaEmpty := by
        apply hZF.1.eq_of_same_members
        intro member
        exact iff_of_false
          (hValueEmpty member) (hOmegaEmpty member)
      simpa [hValueEq] using hOmegaEmptyMem
    · intro predecessor hPredecessor hPredecessorClosed
        successor hSuccessor value hValue
      have hLeftOrdinal :=
        hω.members_areOrdinals hZF left hLeft
      have hPredecessorOrdinal :=
        hω.members_areOrdinals hZF predecessor hPredecessor
      rcases (ordinalMultiplication_successor_iff
          hZF 𝕀 hLeftOrdinal hPredecessorOrdinal hSuccessor).mp hValue with
        ⟨previous, hPrevious, hValueAddition⟩
      have hPreviousOmega :=
        hPredecessorClosed previous hPrevious
      exact ordinalAddition_mem_omega
        hZF 𝕀 hω hPreviousOmega hLeft hValueAddition
  exact hClosed right hRight product hProduct

end ZF

end SetTheory
end YesMetaZFC
