import YesMetaZFC.SetTheory.Extension
import YesMetaZFC.SetTheory.FunctionSemantics

/-!
# 基础集合构造的模型语义接口

本层从 KP 的空集、配对与并集公理提取普通 Lean 可消费的存在定理，并组合出单元素集
与向集合插入一个元素的构造。这里还统一放置不交、二元并和笛卡尔积等跨章节复用的
集合构造语义。ZF 和 ZFC 通过理论扩张自动拥有同一接口。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- `singleton` 恰好只含有 `element`。 -/
def IsSingletonOf (ℳ : Structure.{u})
    (singleton element : ℳ.Domain) : Prop :=
  ∀ member, ℳ.mem member singleton ↔ member = element

/-- `union` 恰好是集合族 `family` 的并集。 -/
def IsUnionOf (ℳ : Structure.{u})
    (union family : ℳ.Domain) : Prop :=
  ∀ value, ℳ.mem value union ↔
    ∃ member, ℳ.mem member family ∧ ℳ.mem value member

/-- `power` 恰好由 `set` 的全部子集组成。 -/
def IsPowerSetOf (ℳ : Structure.{u})
    (power set : ℳ.Domain) : Prop :=
  ∀ subset, ℳ.mem subset power ↔
    ∀ element, ℳ.mem element subset → ℳ.mem element set

/-- `left` 与 `right` 没有公共成员。 -/
def IsDisjoint (ℳ : Structure.{u})
    (left right : ℳ.Domain) : Prop :=
  ∀ value, ¬ (ℳ.mem value left ∧ ℳ.mem value right)

/-- `union` 的成员恰好来自 `left` 或 `right`。 -/
def IsUnionOfTwo (ℳ : Structure.{u})
    (union left right : ℳ.Domain) : Prop :=
  ∀ value,
    ℳ.mem value union ↔ ℳ.mem value left ∨ ℳ.mem value right

/-- `product` 恰好是 `left × right` 的有序对编码集合。 -/
def IsCartesianProduct {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (product left right : ℳ.Domain) : Prop :=
  ∀ pair,
    ℳ.mem pair product ↔
      ∃ leftValue, ℳ.mem leftValue left ∧
        ∃ rightValue, ℳ.mem rightValue right ∧
          𝕀.Codes pair leftValue rightValue

/-- `space` 恰好由所有从 `source` 到 `target` 的集合编码函数组成。 -/
def IsFunctionSpace {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (space source target : ℳ.Domain) : Prop :=
  ∀ function,
    ℳ.mem function space ↔
      ℳ.IsSetFunctionFromTo 𝕀 function source target

namespace IsSingletonOf

/-- 同一对象的两个单元素集相等。 -/
theorem eq {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {left right element : ℳ.Domain}
    (hLeft : ℳ.IsSingletonOf left element)
    (hRight : ℳ.IsSingletonOf right element) :
    left = right := by
  apply hExt.eq_of_same_members
  intro member
  rw [hLeft member, hRight member]

end IsSingletonOf

namespace IsUnionOf

/-- 同一集合族的两个并集相等。 -/
theorem eq {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {left right family : ℳ.Domain}
    (hLeft : ℳ.IsUnionOf left family)
    (hRight : ℳ.IsUnionOf right family) :
    left = right := by
  apply hExt.eq_of_same_members
  intro value
  rw [hLeft value, hRight value]

end IsUnionOf

register_prove_auto_sequent_rule IsUnionOf.eq PRIORITY 200

namespace IsPowerSetOf

/-- 同一集合的两个幂集相等。 -/
theorem eq {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {left right set : ℳ.Domain}
    (hLeft : ℳ.IsPowerSetOf left set)
    (hRight : ℳ.IsPowerSetOf right set) :
    left = right := by
  apply hExt.eq_of_same_members
  intro subset
  rw [hLeft subset, hRight subset]

end IsPowerSetOf

namespace IsFunctionSpace

/-- 同一源集和目标集的两个函数集相等。 -/
theorem eq {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    (hExt : Extensional ℳ)
    {left right source target : ℳ.Domain}
    (hLeft : ℳ.IsFunctionSpace 𝕀 left source target)
    (hRight : ℳ.IsFunctionSpace 𝕀 right source target) :
    left = right := by
  apply hExt.eq_of_same_members
  intro function
  rw [hLeft function, hRight function]

end IsFunctionSpace

namespace IsDisjoint

/-- 不交关系交换左右参数后仍成立。 -/
theorem symm {ℳ : Structure.{u}}
    {left right : ℳ.Domain}
    (hDisjoint : ℳ.IsDisjoint left right) :
    ℳ.IsDisjoint right left := by
  intro value hBoth
  exact hDisjoint value ⟨hBoth.2, hBoth.1⟩

end IsDisjoint

namespace IsUnionOfTwo

/-- 二元并的两个分量可以交换。 -/
theorem swap {ℳ : Structure.{u}}
    {union left right : ℳ.Domain}
    (hUnion : ℳ.IsUnionOfTwo union left right) :
    ℳ.IsUnionOfTwo union right left := by
  intro value
  rw [hUnion value]
  exact or_comm

end IsUnionOfTwo

end Structure

namespace Definitional.Project.Formula

/-- `left` 与 `right` 不相交。 -/
def isDisjoint {depth : Nat}
    (left right : Term depth) : Formula 1 depth :=
  .forallE <|
    .neg <| .conj
      (.mem Term.newest left.weaken)
      (.mem Term.newest right.weaken)

/-- `union` 的成员恰好来自 `left` 或 `right`。 -/
def isUnionOfTwo {depth : Nat}
    (union left right : Term depth) : Formula 1 depth :=
  .forallE <|
    .iff (.mem Term.newest union.weaken) <|
      .disj
        (.mem Term.newest left.weaken)
        (.mem Term.newest right.weaken)

/-- `product` 是 `left × right` 的有序对编码集合。 -/
def isCartesianProduct (𝒞 : OrderedPairConvention)
    {depth : Nat} (product left right : Term depth) : Formula 1 depth :=
  .forallE <|
    .iff (.mem Term.newest product.weaken) <|
      Formula.existsMem left.weaken <|
        Formula.existsMem right.weaken.weaken <|
          𝒞.code (.bound 2) (.bound 1) Term.newest

/-- `space` 是从 `source` 到 `target` 的全部函数组成的集合。 -/
def isFunctionSpace (𝒞 : OrderedPairConvention)
    {depth : Nat} (space source target : Term depth) : Formula 1 depth :=
  .forallE <|
    .iff (.mem Term.newest space.weaken) <|
      isFunctionFromTo 𝒞 Term.newest source.weaken target.weaken

/-- 单元素集公式与纸面单元素集语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isSingleton_iff
    {ℳ : Structure.{u}} (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (singleton element : Term depth) :
    satisfies env (isSingleton singleton element) ↔
      ℳ.IsSingletonOf (singleton.eval env) (element.eval env) := by
  simp only [isSingleton, isUnorderedPair, Structure.IsSingletonOf,
    satisfies_forall_iff, satisfies_iff_iff,
    satisfies_mem_iff, satisfies_disj_iff,
    satisfies_extensionalEq_iff_eq hExt,
    or_self,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 并集公式与纸面并集语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isUnion_iff {ℳ : Structure.{u}}
    {depth : Nat} (env : Env ℳ depth)
    (union family : Term depth) :
    satisfies env (isUnion union family) ↔
      ℳ.IsUnionOf (union.eval env) (family.eval env) := by
  simp only [isUnion, Structure.IsUnionOf,
    satisfies_forall_iff, satisfies_iff_iff,
    satisfies_mem_iff, satisfies_exists_iff,
    satisfies_conj_iff, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push]

/-- 幂集公式与纸面幂集语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isPowerSet_iff
    {ℳ : Structure.{u}} {depth : Nat} (env : Env ℳ depth)
    (power set : Term depth) :
    satisfies env (isPowerSet power set) ↔
      ℳ.IsPowerSetOf (power.eval env) (set.eval env) := by
  simp only [isPowerSet, Structure.IsPowerSetOf,
    satisfies_forall_iff, satisfies_iff_iff,
    satisfies_mem_iff, satisfies_subset_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 不相交公式与纸面语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isDisjoint_iff
    {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) (left right : Term depth) :
    satisfies env (isDisjoint left right) ↔
      ℳ.IsDisjoint (left.eval env) (right.eval env) := by
  simp only [isDisjoint, Structure.IsDisjoint,
    satisfies_forall_iff, satisfies_neg_iff,
    satisfies_conj_iff, satisfies_mem_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 二元并公式与纸面语义一致。 -/
@[prove_auto_norm semantic]
theorem satisfies_isUnionOfTwo_iff
    {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) (union left right : Term depth) :
    satisfies env (isUnionOfTwo union left right) ↔
      ℳ.IsUnionOfTwo (union.eval env)
        (left.eval env) (right.eval env) := by
  simp only [isUnionOfTwo, Structure.IsUnionOfTwo,
    satisfies_forall_iff, satisfies_iff_iff,
    satisfies_mem_iff, satisfies_disj_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 笛卡尔积公式与纸面有序对编码语义一致。 -/
theorem satisfies_isCartesianProduct_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (product left right : Term depth) :
    satisfies env
        (isCartesianProduct 𝒞 product left right) ↔
      ℳ.IsCartesianProduct 𝕀
        (product.eval env) (left.eval env) (right.eval env) := by
  simp only [isCartesianProduct, Structure.IsCartesianProduct,
    satisfies_forall_iff, satisfies_iff_iff,
    satisfies_mem_iff, satisfies_existsMem_iff,
    𝕀.satisfies_code_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push]

/-- 函数集公式与纸面函数图集合语义一致。 -/
theorem satisfies_isFunctionSpace_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (space source target : Term depth) :
    satisfies env (isFunctionSpace 𝒞 space source target) ↔
      ℳ.IsFunctionSpace 𝕀
        (space.eval env) (source.eval env) (target.eval env) := by
  simp only [isFunctionSpace, Structure.IsFunctionSpace,
    satisfies_forall_iff, satisfies_iff_iff,
    satisfies_mem_iff, satisfies_isFunctionFromTo_iff 𝕀 hExt,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

end Formula
end Project
end Definitional

namespace Axioms

/-- 空集公理的项目核语义。 -/
theorem satisfies_emptySet_iff {ℳ : Structure.{u}}
    (free : FreeVarId → ℳ.Domain) :
    Definitional.Project.Formula.satisfies
        ({ bound := Fin.elim0, free := free } : Env ℳ 0)
        emptySet.formula ↔
      ∃ empty, ∀ value, ¬ ℳ.mem value empty := by
  unfold emptySet
  dsimp only [Definitional.Project.Sentence.ofFormula]
  rw [Definitional.Project.Formula.satisfies_exists_iff]
  simp only [
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_neg_iff,
    Definitional.Project.Formula.satisfies_mem_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 配对公理的项目核语义。 -/
theorem satisfies_pairing_iff {ℳ : Structure.{u}}
    (free : FreeVarId → ℳ.Domain) :
    Definitional.Project.Formula.satisfies
        ({ bound := Fin.elim0, free := free } : Env ℳ 0)
        pairing.formula ↔
      ∀ left right, ∃ pair, ∀ value,
        ℳ.mem value pair ↔
            (∀ element, ℳ.mem element value ↔ ℳ.mem element left) ∨
              (∀ element, ℳ.mem element value ↔ ℳ.mem element right) := by
  unfold pairing
  dsimp only [Definitional.Project.Sentence.ofFormula]
  simp only [
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_exists_iff,
    Definitional.Project.Formula.satisfies_iff_iff,
    Definitional.Project.Formula.satisfies_mem_iff,
    Definitional.Project.Formula.satisfies_disj_iff,
    Definitional.Project.Formula.satisfies_extensionalEq_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 并集公理的项目核语义。 -/
theorem satisfies_union_iff {ℳ : Structure.{u}}
    (free : FreeVarId → ℳ.Domain) :
    Definitional.Project.Formula.satisfies
        ({ bound := Fin.elim0, free := free } : Env ℳ 0)
        union.formula ↔
      ∀ family, ∃ union, ∀ value,
        ℳ.mem value union ↔
          ∃ member, ℳ.mem member family ∧ ℳ.mem value member := by
  unfold union
  dsimp only [Definitional.Project.Sentence.ofFormula]
  simp only [
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_exists_iff,
    Definitional.Project.Formula.satisfies_existsMem_iff,
    Definitional.Project.Formula.satisfies_iff_iff,
    Definitional.Project.Formula.satisfies_mem_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 幂集公理的项目核语义。 -/
theorem satisfies_powerSet_iff {ℳ : Structure.{u}}
    (free : FreeVarId → ℳ.Domain) :
    Definitional.Project.Formula.satisfies
        ({ bound := Fin.elim0, free := free } : Env ℳ 0)
        powerSet.formula ↔
      ∀ set, ∃ power, ∀ subset,
        ℳ.mem subset power ↔
          ∀ element, ℳ.mem element subset → ℳ.mem element set := by
  unfold powerSet
  dsimp only [Definitional.Project.Sentence.ofFormula]
  simp only [
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_exists_iff,
    Definitional.Project.Formula.satisfies_iff_iff,
    Definitional.Project.Formula.satisfies_mem_iff,
    Definitional.Project.Formula.satisfies_subset_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

end Axioms

namespace KP

/-- KP 模型中存在空集。 -/
theorem exists_empty {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) :
    ∃ empty, ∀ value, ¬ ℳ.mem value empty := by
  let free : FreeVarId → ℳ.Domain := fun _ =>
    Classical.choice ℳ.nonempty
  exact (Axioms.satisfies_emptySet_iff free).mp <|
    hKP.2 Axioms.emptySet Axiom.emptySet free

/-- KP 模型中任意两个对象都有无序对。 -/
theorem exists_pair {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) (left right : ℳ.Domain) :
    ∃ pair, ∀ value,
      ℳ.mem value pair ↔ value = left ∨ value = right := by
  let free : FreeVarId → ℳ.Domain := fun _ =>
    Classical.choice ℳ.nonempty
  have hPairing :=
    (Axioms.satisfies_pairing_iff free).mp <|
      hKP.2 Axioms.pairing Axiom.pairing free
  rcases hPairing left right with ⟨pair, hPair⟩
  refine ⟨pair, fun value => ?_⟩
  have hPairValue := hPair value
  change ℳ.mem value pair ↔
    (∀ element, ℳ.mem element value ↔ ℳ.mem element left) ∨
      (∀ element, ℳ.mem element value ↔ ℳ.mem element right) at hPairValue
  rw [hPairValue]
  constructor
  · intro h
    rcases h with hLeft | hRight
    · exact Or.inl <| hKP.1.eq_of_same_members value left hLeft
    · exact Or.inr <| hKP.1.eq_of_same_members value right hRight
  · intro h
    rcases h with rfl | rfl
    · exact Or.inl fun _ => Iff.rfl
    · exact Or.inr fun _ => Iff.rfl

/-- KP 模型中任意对象都有单元素集。 -/
theorem exists_singleton {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) (value : ℳ.Domain) :
    ∃ singleton, ∀ member,
      ℳ.mem member singleton ↔ member = value := by
  rcases exists_pair hKP value value with ⟨singleton, hSingleton⟩
  exact ⟨singleton, fun member => by
    simpa only [or_self] using hSingleton member⟩

/-- KP 模型中任意集合族都有并集。 -/
theorem exists_union {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) (family : ℳ.Domain) :
    ∃ union, ∀ value,
      ℳ.mem value union ↔
        ∃ member, ℳ.mem member family ∧ ℳ.mem value member := by
  let free : FreeVarId → ℳ.Domain := fun _ =>
    Classical.choice ℳ.nonempty
  exact (Axioms.satisfies_union_iff free).mp
    (hKP.2 Axioms.union Axiom.union free) family

/-- KP 模型中可以向一个集合插入单个对象。 -/
theorem exists_insert {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) (set value : ℳ.Domain) :
    ∃ insert, ∀ member,
      ℳ.mem member insert ↔ ℳ.mem member set ∨ member = value := by
  rcases exists_singleton hKP value with
    ⟨singleton, hSingleton⟩
  rcases exists_pair hKP set singleton with
    ⟨family, hFamily⟩
  rcases exists_union hKP family with
    ⟨insert, hInsert⟩
  refine ⟨insert, fun member => ?_⟩
  rw [hInsert member]
  constructor
  · rintro ⟨part, hPart, hMember⟩
    rcases (hFamily part).mp hPart with rfl | rfl
    · exact Or.inl hMember
    · exact Or.inr <| (hSingleton member).mp hMember
  · intro h
    rcases h with hMember | hEq
    · exact ⟨set, (hFamily set).mpr (Or.inl rfl), hMember⟩
    · subst member
      exact ⟨singleton, (hFamily singleton).mpr (Or.inr rfl),
        (hSingleton value).mpr rfl⟩

/-- KP 中任意两个集合都有二元并。 -/
theorem exists_unionOfTwo {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) (left right : ℳ.Domain) :
    ∃ union, ℳ.IsUnionOfTwo union left right := by
  rcases exists_pair hKP left right with ⟨family, hFamily⟩
  rcases exists_union hKP family with ⟨union, hUnion⟩
  refine ⟨union, fun value => ?_⟩
  rw [hUnion value]
  constructor
  · rintro ⟨part, hPart, hValue⟩
    rcases (hFamily part).mp hPart with rfl | rfl
    · exact Or.inl hValue
    · exact Or.inr hValue
  · intro hValue
    rcases hValue with hValue | hValue
    · exact ⟨left, (hFamily left).mpr <| Or.inl rfl, hValue⟩
    · exact ⟨right, (hFamily right).mpr <| Or.inr rfl, hValue⟩

end KP

namespace ZF

/-- ZF 模型中任意集合都有幂集。 -/
theorem exists_powerSet {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF) (set : ℳ.Domain) :
    ∃ power, ℳ.IsPowerSetOf power set := by
  let free : FreeVarId → ℳ.Domain := fun _ =>
    Classical.choice ℳ.nonempty
  have hPowerSet :=
    (Axioms.satisfies_powerSet_iff free).mp <|
      hZF.2 Axioms.powerSet Axiom.powerSet free
  rcases hPowerSet set with ⟨power, hPower⟩
  refine ⟨power, fun subset => ?_⟩
  have hSubset := hPower subset
  change ℳ.mem subset power ↔
    ∀ element, ℳ.mem element subset → ℳ.mem element set at hSubset
  exact hSubset

end ZF

end SetTheory
end YesMetaZFC
