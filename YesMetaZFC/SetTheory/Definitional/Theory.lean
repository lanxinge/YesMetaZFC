import YesMetaZFC.SetTheory.Definitional.Semantics

/-!
# 带定义原子的原生理论

理论、模型和语义蕴涵全部只依赖新核及其不透明原子解释。旧纯 `∈` 理论的展开与保守性
证明位于显式导入的 `YesMetaZFC.SetTheory.Definitional.Audit`。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional

universe u v

/-- 新核理论是新核句子的谓词。 -/
abbrev Theory (σ : AtomSignature.{u}) :=
  Sentence σ → Prop

namespace Theory

/-- 空理论。 -/
def empty {σ : AtomSignature.{u}} : Theory σ :=
  fun _ => False

/-- 单句理论。 -/
def singleton {σ : AtomSignature.{u}} (sentence : Sentence σ) :
    Theory σ :=
  fun candidate => candidate = sentence

/-- 向理论加入一个句子。 -/
def insert {σ : AtomSignature.{u}} (sentence : Sentence σ)
    (theory : Theory σ) : Theory σ :=
  fun candidate => candidate = sentence ∨ theory candidate

end Theory

namespace Structure

/-- 一个结构满足新核句子。 -/
def SatisfiesSentence {σ : AtomSignature.{u}} (kernel : Kernel.{u, v} σ)
    (ℳ : SetTheory.Structure.{v}) (sentence : Sentence σ) : Prop :=
  ∀ free : FreeVarId → ℳ.Domain,
    Semantics.satisfies kernel.interpretation {
      bound := Fin.elim0
      free := free
    } sentence.formula

/-- 一个外延隶属结构满足新核理论中的全部句子。 -/
def Models {σ : AtomSignature.{u}} (kernel : Kernel.{u, v} σ)
    (ℳ : SetTheory.Structure.{v}) (theory : Theory σ) : Prop :=
  Extensional ℳ ∧
    ∀ sentence, theory sentence →
      SatisfiesSentence kernel ℳ sentence

end Structure

/-- 固定模型 universe 的新核语义蕴涵。 -/
def SemanticallyEntails {σ : AtomSignature.{u}} (kernel : Kernel.{u, v} σ)
    (theory : Theory σ) (target : Sentence σ) : Prop :=
  ∀ ℳ : SetTheory.Structure.{v},
    Structure.Models kernel ℳ theory →
      Structure.SatisfiesSentence kernel ℳ target

scoped infix:50 " ⊨ₐ " => SemanticallyEntails

end Definitional
end SetTheory
end YesMetaZFC
