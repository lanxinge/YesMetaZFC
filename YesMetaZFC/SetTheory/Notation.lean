import YesMetaZFC.Logic.Notation.Relation
import YesMetaZFC.SetTheory.Language
import YesMetaZFC.SetTheory.Notation.Surface

/-!
# 纯集合论记号入口

对象公式使用 `set[depth] ⟪...⟫` 或 `set! ⟪...⟫`。类表达式使用
`class[depth] ⟪x | ...⟫` 或 `class! ⟪x | ...⟫`。

类运算记号放在 `SetTheoryClass` scope 中，避免污染 Lean 自带的集合与类型记号。

典型写法：

```lean
sentence! ⟪∀ x y, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y⟫
sentence! ⟪∀ y, ∀ x ∈ y, x ∈ y⟫
sentence! ⟪∀ x family, x ∈ ⋃ family ↔ ∃ member ∈ family, x ∈ member⟫
sentence! ⟪∀ subset set, subset ∈ 𝒫(set) ↔ subset ⊆ set⟫
sentence! ⟪∀ α β, (Ord(α) ∧ β <ₒ α) → Ord(β)⟫
class! ⟪x | x = x⟫
```

其中 `=` 不产生原生等词节点，而是编译为项目核的外延等同原子。
序数记号 `α <ₒ β` 展开为 `α ∈ β`，`α ≤ₒ β` 展开为 `α ⊆ β`。

关系与函数记号显式携带有序对编码约定：

```lean
set! ⟪⟨#ᶠ[0], #ᶠ[1]⟩[pairing] ∈ #ᶠ[2]⟫
set! ⟪Fun[pairing](#ᶠ[0])⟫
set! ⟪#ᶠ[0] :[pairing] #ᶠ[1] ⟶ #ᶠ[2]⟫
```

省略方括号时使用 `Definitional.Project.FlatPairing.convention`：

```lean
set! ⟪⟨#ᶠ[0], #ᶠ[1]⟩ ∈ #ᶠ[2]⟫
set! ⟪Fun(#ᶠ[0])⟫
set! ⟪#ᶠ[0] : #ᶠ[1] ⟶ #ᶠ[2]⟫
```

语言核心没有默认 Kuratowski 编码；显式方括号版本仍可切换其他编码。
-/

namespace YesMetaZFC
namespace SetTheory

instance : Logic.FirstOrder.Surface.MembershipRelation signature where
  mem := RelationSymbol.membership

namespace SetTheoryClass

scoped notation "𝒱" => Definitional.Project.DefinableClass.universal
scoped prefix:40 "∁ᶜ " => Definitional.Project.DefinableClass.complement
scoped infixr:35 " ∩ᶜ " => Definitional.Project.DefinableClass.inter
scoped infixr:30 " ∪ᶜ " => Definitional.Project.DefinableClass.union
scoped infixl:30 " ∖ᶜ " => Definitional.Project.DefinableClass.diff
scoped prefix:max "⋃ᶜ " => Definitional.Project.DefinableClass.sUnion
scoped infix:50 " ≈ᶜ " => Definitional.Project.DefinableClass.equal
scoped infix:50 " ⊆ᶜ " => Definitional.Project.DefinableClass.subset

end SetTheoryClass

end SetTheory
end YesMetaZFC
