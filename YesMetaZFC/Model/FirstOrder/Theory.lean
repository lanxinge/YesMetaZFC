import YesMetaZFC.Model.FirstOrder.Semantics
import YesMetaZFC.Logic.Theory.Basic

/-!
# 闭句理论的 Tarski 语义

理论只包含闭句，因此模型满足和语义蕴涵不再携带任意变量环境。每个闭句都在唯一的
空环境中解释，这直接消除了理论层的大量环境无关性与闭合性桥接。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w x

namespace Formula

/-- 闭句在结构中为真。 -/
def TrueIn {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ) (sentence : Sentence σ) : Prop :=
  satisfies (Env.empty (M := M)) sentence

end Formula

namespace Theory

/-- 结构满足理论中的全部闭句。 -/
def Models {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ) (T : Theory σ) : Prop :=
  ∀ sentence, T sentence → sentence.TrueIn M

/-- 固定模型 universe 的闭句语义蕴涵。 -/
def SemanticallyEntails {σ : Signature.{u, v, w}}
    (T : Theory σ) (sentence : Sentence σ) : Prop :=
  ∀ M : Structure.{u, v, w, x} σ,
    Models M T → sentence.TrueIn M

scoped infix:50 " ⊨ₛ " => SemanticallyEntails

/-- 每个结构都满足空理论。 -/
theorem models_empty {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ) :
    Models M (empty : Theory σ) := by
  intro sentence hSentence
  cases hSentence

/-- 满足插入理论等价于同时满足新闭句与原理论。 -/
theorem models_insert {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {T : Theory σ} {sentence : Sentence σ} :
    Models M (insert sentence T) ↔
      sentence.TrueIn M ∧ Models M T := by
  constructor
  · intro hModels
    exact ⟨hModels sentence (Or.inl rfl), by
      intro candidate hCandidate
      exact hModels candidate (Or.inr hCandidate)⟩
  · rintro ⟨hSentence, hModels⟩ candidate hCandidate
    rcases hCandidate with hEq | hMem
    · simpa [hEq] using hSentence
    · exact hModels candidate hMem

/-- 理论成员总是其语义后承。 -/
theorem entails_of_mem {σ : Signature.{u, v, w}}
    {T : Theory σ} {sentence : Sentence σ} (hMem : T sentence) :
    SemanticallyEntails.{u, v, w, x} T sentence := by
  intro M hModels
  exact hModels sentence hMem

/-- 语义后承沿理论加强保持。 -/
theorem entails_weaken {σ : Signature.{u, v, w}}
    {T U : Theory σ} {sentence : Sentence σ}
    (hSub : ∀ candidate, U candidate → T candidate)
    (hEntails : SemanticallyEntails.{u, v, w, x} U sentence) :
    SemanticallyEntails.{u, v, w, x} T sentence := by
  intro M hModels
  exact hEntails M (by
    intro candidate hCandidate
    exact hModels candidate (hSub candidate hCandidate))

end Theory
end FirstOrder
end Logic
end YesMetaZFC
