import YesMetaZFC.Logic.Syntax

/-!
# 闭句理论

可信理论只由闭句组成。开放公式属于证明前端或 schema 接口，不再混入理论成员关系，
因此理论公理进入任意自由变量上下文时不需要额外的闭合性证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

/-- 一阶理论是闭句上的外延谓词。 -/
abbrev Theory (σ : Signature.{u, v, w}) := Sentence σ → Prop

namespace Theory

/-- 空理论。 -/
def empty {σ : Signature.{u, v, w}} : Theory σ :=
  fun _ => False

/-- 单公理理论。 -/
def singleton {σ : Signature.{u, v, w}}
    (sentence : Sentence σ) : Theory σ :=
  fun candidate => candidate = sentence

/-- 向理论加入一条闭句公理。 -/
def insert {σ : Signature.{u, v, w}}
    (sentence : Sentence σ) (T : Theory σ) : Theory σ :=
  fun candidate => candidate = sentence ∨ T candidate

/-- 两个理论的并。 -/
def union {σ : Signature.{u, v, w}}
    (T U : Theory σ) : Theory σ :=
  fun sentence => T sentence ∨ U sentence

/-- 理论包含关系。 -/
def Extends {σ : Signature.{u, v, w}}
    (strong weak : Theory σ) : Prop :=
  ∀ {sentence}, weak sentence → strong sentence

/-- 理论外延相等。 -/
@[ext] theorem ext {σ : Signature.{u, v, w}}
    {T U : Theory σ}
    (h : ∀ sentence, T sentence ↔ U sentence) : T = U := by
  funext sentence
  exact propext (h sentence)

/-- 有限公理化只枚举闭句。 -/
def FinitelyAxiomatized {σ : Signature.{u, v, w}}
    (T : Theory σ) : Prop :=
  ∃ axioms : List (Sentence σ),
    ∀ sentence, T sentence ↔ sentence ∈ axioms

/-- 空理论是有限公理化的。 -/
theorem finitely_axiomatized_empty
    {σ : Signature.{u, v, w}} :
    FinitelyAxiomatized (empty : Theory σ) := by
  refine ⟨[], ?_⟩
  intro sentence
  exact ⟨False.elim, fun h => nomatch h⟩

/-- 单公理理论是有限公理化的。 -/
theorem finitely_axiomatized_singleton
    {σ : Signature.{u, v, w}} (sentence : Sentence σ) :
    FinitelyAxiomatized (singleton sentence) := by
  refine ⟨[sentence], ?_⟩
  intro candidate
  constructor
  · intro h
    cases h
    exact .head []
  · intro h
    cases h with
    | head => rfl
    | tail _ h => exact nomatch h

/-- 在有限公理化理论中加入闭句仍然有限公理化。 -/
theorem finitely_axiomatized_insert
    {σ : Signature.{u, v, w}}
    {sentence : Sentence σ} {T : Theory σ}
    (hT : FinitelyAxiomatized T) :
    FinitelyAxiomatized (insert sentence T) := by
  rcases hT with ⟨axioms, hAxioms⟩
  refine ⟨sentence :: axioms, ?_⟩
  intro candidate
  constructor
  · intro h
    cases h with
    | inl h => cases h; exact .head axioms
    | inr h => exact .tail sentence ((hAxioms candidate).mp h)
  · intro h
    cases h with
    | head => exact Or.inl rfl
    | tail _ h => exact Or.inr ((hAxioms candidate).mpr h)

/-- 有限公理化理论的并仍然有限公理化。 -/
theorem finitely_axiomatized_union
    {σ : Signature.{u, v, w}}
    {T U : Theory σ}
    (hT : FinitelyAxiomatized T)
    (hU : FinitelyAxiomatized U) :
    FinitelyAxiomatized (union T U) := by
  rcases hT with ⟨left, hLeft⟩
  rcases hU with ⟨right, hRight⟩
  refine ⟨left ++ right, ?_⟩
  intro sentence
  constructor
  · intro h
    cases h with
    | inl h => exact List.mem_append_left right ((hLeft sentence).mp h)
    | inr h => exact List.mem_append_right left ((hRight sentence).mp h)
  · intro h
    have split_mem : ∀ (xs : List (Sentence σ)),
        sentence ∈ xs ++ right → sentence ∈ xs ∨ sentence ∈ right := by
      intro xs
      induction xs with
      | nil => exact fun hx => Or.inr hx
      | cons x xs ih =>
          intro hx
          cases hx with
          | head => exact Or.inl (.head xs)
          | tail _ hx =>
              cases ih hx with
              | inl hxs => exact Or.inl (.tail x hxs)
              | inr hr => exact Or.inr hr
    cases split_mem left h with
    | inl h => exact Or.inl ((hLeft sentence).mpr h)
    | inr h => exact Or.inr ((hRight sentence).mpr h)

end Theory
end FirstOrder
end Logic
end YesMetaZFC
