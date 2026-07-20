import YesMetaZFC.SetTheory.Definitional.Project.FlatPairing
import YesMetaZFC.SetTheory.Notation.Surface

/-!
# 项目原子核的集合论公理公式

固定公理和模式实例全部构造为项目 `Sentence`。定义原子保持在语法叶节点，只有需要
审计旧纯核时才通过 `Definitional.Audit` 展开。
-/

namespace YesMetaZFC
namespace SetTheory

namespace Axioms

/-- 外延性公理。 -/
def extensionality : Definitional.Project.Sentence :=
  sentence! ⟪∀ left right,
    (∀ element, element ∈ left ↔ element ∈ right) → left = right⟫

/-- 空集公理。 -/
def emptySet : Definitional.Project.Sentence :=
  sentence! ⟪∃ empty, ∀ element, element ∉ empty⟫

/-- 配对公理。 -/
def pairing : Definitional.Project.Sentence :=
  sentence! ⟪∀ left right, ∃ pair, ∀ element,
    element ∈ pair ↔ (element = left ∨ element = right)⟫

/-- 并集公理。 -/
def union : Definitional.Project.Sentence :=
  sentence! ⟪∀ family, ∃ union, ∀ element,
    element ∈ union ↔ ∃ member ∈ family, element ∈ member⟫

/-- 幂集公理。 -/
def powerSet : Definitional.Project.Sentence :=
  sentence! ⟪∀ set, ∃ power, ∀ subset,
    subset ∈ power ↔ subset ⊆ set⟫

/-- 无穷公理。 -/
def infinity : Definitional.Project.Sentence :=
  sentence! ⟪∃ omegaSet,
    (∃ empty, (∀ element, element ∉ empty) ∧ empty ∈ omegaSet) ∧
    (∀ set ∈ omegaSet, ∃ successor,
      ((∀ element,
        element ∈ successor ↔ (element ∈ set ∨ element = set)) ∧
        successor ∈ omegaSet))⟫

/-- 正则/基础公理。 -/
def foundation : Definitional.Project.Sentence :=
  sentence! ⟪∀ set,
    (∃ element, element ∈ set) →
      ∃ minimal ∈ set, ∀ element ∈ set, element ∉ minimal⟫

/-- 选择公理的选择集形式。 -/
def choice : Definitional.Project.Sentence :=
  sentence! ⟪∀ family,
    ((∀ member ∈ family, ∃ element, element ∈ member) ∧
      (∀ first ∈ family, ∀ second ∈ family,
        first ≠ second →
          ¬ (∃ element, element ∈ first ∧ element ∈ second))) → ∃ choice,
      ∀ member ∈ family, ∃ selected,
        ((selected ∈ choice ∧ selected ∈ member) ∧
          (∀ other,
            (other ∈ choice ∧ other ∈ member) → other = selected))⟫

namespace Schema

/-- 分离模式在参数上下文中的核心公式。 -/
def separationCore {parameterCount : Nat}
    (schema : Definitional.Project.UnarySchema parameterCount) :
    Definitional.Project.Formula 1 parameterCount :=
  .forallE <| .existsE <| .forallE <|
    .iff (.mem (.bound 0) (.bound 1)) <|
      .conj (.mem (.bound 0) (.bound 2))
        (schema.body.rename BoundEmbedding.unaryUnderTwo)

/-- 分离模式实例。 -/
def separation {parameterCount : Nat}
    (schema : Definitional.Project.UnarySchema parameterCount) :
    Definitional.Project.Sentence :=
  Definitional.Project.Sentence.forallClosure (separationCore schema) <| by
    simp [Definitional.Formula.FreeClosed, separationCore,
      schema.freeClosed]

/-- 收集模式在参数上下文中的核心公式。 -/
def collectionCore {parameterCount : Nat}
    (schema : Definitional.Project.BinarySchema parameterCount) :
    Definitional.Project.Formula 1 parameterCount :=
  .forallE <|
    .imp
      (Definitional.Project.Formula.forallMem (.bound 0) <| .existsE <|
        schema.body.rename BoundEmbedding.binaryUnderOne)
      (.existsE <|
        Definitional.Project.Formula.forallMem (.bound 1) <|
          Definitional.Project.Formula.existsMem (.bound 1) <|
            schema.body.rename BoundEmbedding.binaryUnderTwo)

/-- 收集模式实例。 -/
def collection {parameterCount : Nat}
    (schema : Definitional.Project.BinarySchema parameterCount) :
    Definitional.Project.Sentence :=
  Definitional.Project.Sentence.forallClosure (collectionCore schema) <| by
    simp [Definitional.Formula.FreeClosed, collectionCore,
      Definitional.Project.Formula.forallMem,
      Definitional.Project.Formula.existsMem,
      Definitional.Project.Term.newest,
      schema.freeClosed]

namespace ReplacementEmbedding

/-- 替换模式唯一性前件中的第一个输出。 -/
def firstOutput {parameterCount : Nat} :
    Fin (parameterCount + 2) → Fin (parameterCount + 3) :=
  Fin.cases 1 <| Fin.cases 2 fun parameter =>
    ⟨parameter.val + 3, by omega⟩

/-- 替换模式唯一性前件中的第二个输出。 -/
def secondOutput {parameterCount : Nat} :
    Fin (parameterCount + 2) → Fin (parameterCount + 3) :=
  Fin.cases 0 <| Fin.cases 2 fun parameter =>
    ⟨parameter.val + 3, by omega⟩

/-- 替换模式像集定义中的输入/输出位置。 -/
def imageBody {parameterCount : Nat} :
    Fin (parameterCount + 2) → Fin (parameterCount + 4) :=
  Fin.cases 1 <| Fin.cases 0 fun parameter =>
    ⟨parameter.val + 4, by omega⟩

end ReplacementEmbedding

/-- Jech 风格替换模式在参数上下文中的核心公式。 -/
def replacementCore {parameterCount : Nat}
    (schema : Definitional.Project.BinarySchema parameterCount) :
    Definitional.Project.Formula 1 parameterCount :=
  .imp
    (.forallE <| .forallE <| .forallE <|
      .imp
        (.conj
          (schema.body.rename ReplacementEmbedding.firstOutput)
          (schema.body.rename ReplacementEmbedding.secondOutput))
        (Definitional.Project.Formula.extensionalEq (.bound 1) (.bound 0)))
    (.forallE <| .existsE <| .forallE <|
      .iff (.mem (.bound 0) (.bound 1)) <|
        Definitional.Project.Formula.existsMem (.bound 2) <|
          schema.body.rename ReplacementEmbedding.imageBody)

/-- Jech 风格替换模式实例。 -/
def replacement {parameterCount : Nat}
    (schema : Definitional.Project.BinarySchema parameterCount) :
    Definitional.Project.Sentence :=
  Definitional.Project.Sentence.forallClosure (replacementCore schema) <| by
    simp [Definitional.Formula.FreeClosed, replacementCore,
      Definitional.Project.Formula.existsMem,
      Definitional.Project.Term.newest, schema.freeClosed]

end Schema

end Axioms
end SetTheory
end YesMetaZFC
