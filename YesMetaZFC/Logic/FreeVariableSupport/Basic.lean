import YesMetaZFC.Logic.Syntax

/-!
# 上下文内在的自由变量支持

自由变量不再由全局自然数命名，而是由当前 free 上下文中的类型化位置确定。因此支持
也直接表示成该有限上下文上的布尔掩码：不存在的变量位置无法进入接口，成员判断保持
可计算，环境覆盖不需要经典选择。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

/-- free 上下文上的有限可计算支持。 -/
abbrev FreeSupport (σ : Signature.{u, v, w}) (free : SortContext σ) :=
  Fin free.length → Bool

namespace FreeSupport

/-- 空支持。 -/
def empty {σ : Signature.{u, v, w}} {free : SortContext σ} :
    FreeSupport σ free :=
  fun _ => false

/-- 只包含一个上下文位置的支持。 -/
def singleton {σ : Signature.{u, v, w}} {free : SortContext σ}
    {sort : σ.SortSymbol} (entry : Variable free sort) :
    FreeSupport σ free :=
  fun position => decide (position = entry.position)

/-- 两个支持的并。 -/
def union {σ : Signature.{u, v, w}} {free : SortContext σ}
    (left right : FreeSupport σ free) : FreeSupport σ free :=
  fun position => left position || right position

/-- 一个位置属于支持。 -/
def Contains {σ : Signature.{u, v, w}} {free : SortContext σ}
    (support : FreeSupport σ free) (position : Fin free.length) : Prop :=
  support position = true

/-- 左支持包含于右支持。 -/
def Subset {σ : Signature.{u, v, w}} {free : SortContext σ}
    (left right : FreeSupport σ free) : Prop :=
  ∀ position, left.Contains position → right.Contains position

/-- 两个支持不相交。 -/
def Disjoint {σ : Signature.{u, v, w}} {free : SortContext σ}
    (left right : FreeSupport σ free) : Prop :=
  ∀ position, left.Contains position → right.Contains position → False

@[simp] theorem contains_empty {σ : Signature.{u, v, w}}
    {free : SortContext σ} (position : Fin free.length) :
    ¬ (empty : FreeSupport σ free).Contains position := by
  exact Bool.false_ne_true

@[simp] theorem contains_singleton_self {σ : Signature.{u, v, w}}
    {free : SortContext σ} {sort : σ.SortSymbol}
    (entry : Variable free sort) :
    (singleton entry).Contains entry.position := by
  exact decide_eq_true rfl

@[simp] theorem contains_union {σ : Signature.{u, v, w}}
    {free : SortContext σ} {left right : FreeSupport σ free}
    {position : Fin free.length} :
    (union left right).Contains position ↔
      left.Contains position ∨ right.Contains position := by
  change (left position || right position) = true ↔
    left position = true ∨ right position = true
  cases left position <;> cases right position
  · exact ⟨Or.inl, fun h => h.elim id id⟩
  · exact ⟨fun _ => Or.inr rfl, fun _ => rfl⟩
  · exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  · exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩

/-- 支持不交关系是对称的。 -/
theorem Disjoint.symm {σ : Signature.{u, v, w}}
    {free : SortContext σ} {left right : FreeSupport σ free}
    (hDisjoint : Disjoint left right) : Disjoint right left :=
  fun position hRight hLeft => hDisjoint position hLeft hRight

end FreeSupport

mutual

/-- 项的自由变量支持。 -/
def Term.freeSupport {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol} :
    Term σ bound free sort → FreeSupport σ free
  | .bvar _ => FreeSupport.empty
  | .fvar entry => FreeSupport.singleton entry
  | .app _ arguments => Arguments.freeSupport arguments

/-- 异质参数列的自由变量支持。 -/
def Arguments.freeSupport {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sorts : List σ.SortSymbol} :
    Arguments σ bound free sorts → FreeSupport σ free
  | .nil => FreeSupport.empty
  | .cons term rest =>
      FreeSupport.union term.freeSupport rest.freeSupport

end

namespace Formula

/-- 公式的自由变量支持。 -/
def freeSupport {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} :
    Formula σ bound free → FreeSupport σ free
  | .falsum => FreeSupport.empty
  | .truth => FreeSupport.empty
  | .rel _ arguments => arguments.freeSupport
  | .equal left right =>
      FreeSupport.union left.freeSupport right.freeSupport
  | .neg body => freeSupport body
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      FreeSupport.union (freeSupport left) (freeSupport right)
  | .forallE _ body
  | .existsE _ body => freeSupport body

end Formula
end FirstOrder
end Logic
end YesMetaZFC
