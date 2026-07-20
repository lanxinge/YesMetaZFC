import YesMetaZFC.Logic.Semantics

/-!
# 语义理论与蕴涵

这一层替代旧内核里“理论是一组公式”的职责，但暂不引入 Hilbert/LCF 推导关系。
后续 DAG replay 的 soundness 应优先落到语义蕴涵，再按需要补可检查证明对象。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w x

/-- 理论是公式谓词。这里保持 extensional 表示，方便章节公理和搜索证书注入。 -/
abbrev Theory (σ : Signature.{u, v, w}) := Formula σ → Prop

namespace Theory

def empty {σ : Signature.{u, v, w}} : Theory σ :=
  fun _ => False

def singleton {σ : Signature.{u, v, w}} (φ : Formula σ) : Theory σ :=
  fun ψ => ψ = φ

def insert {σ : Signature.{u, v, w}} (φ : Formula σ) (T : Theory σ) : Theory σ :=
  fun ψ => ψ = φ ∨ T ψ

def union {σ : Signature.{u, v, w}} (T U : Theory σ) : Theory σ :=
  fun φ => T φ ∨ U φ

/-- 一个赋值满足理论中的所有公式。 -/
def Models {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (T : Theory σ) (env : Env M) : Prop :=
  ∀ φ, T φ → Formula.satisfies env φ

/-- 固定模型 universe 的语义蕴涵。 -/
def SemanticallyEntails {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (T : Theory σ) (φ : Formula σ) : Prop :=
  ∀ {M : Structure.{u, v, w, x} σ}, ∀ env : Env M,
    Models T env → Formula.satisfies env φ

scoped infix:50 " ⊨ₛ " => SemanticallyEntails

theorem models_empty {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (env : Env M) :
    Models (empty : Theory σ) env := by
  intro φ hφ
  cases hφ

theorem models_insert {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} {T : Theory σ} {φ : Formula σ}
    {env : Env M} :
    Models (insert φ T) env ↔ Formula.satisfies env φ ∧ Models T env := by
  constructor
  · intro h
    exact ⟨h φ (Or.inl rfl), by
      intro ψ hψ
      exact h ψ (Or.inr hψ)⟩
  · intro h ψ hψ
    rcases h with ⟨hφ, hT⟩
    rcases hψ with hEq | hMem
    · simpa [hEq] using hφ
    · exact hT ψ hMem

theorem entails_of_mem {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {φ : Formula σ} (hMem : T φ) :
    SemanticallyEntails.{u, v, w, x} T φ := by
  intro M env hModels
  exact hModels φ hMem

theorem entails_weaken {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T U : Theory σ} {φ : Formula σ}
    (hSub : ∀ ψ, U ψ → T ψ)
    (hEntails : SemanticallyEntails.{u, v, w, x} U φ) :
    SemanticallyEntails.{u, v, w, x} T φ := by
  intro M env hModels
  exact hEntails env (by
    intro ψ hψ
    exact hModels ψ (hSub ψ hψ))

end Theory

end FirstOrder
end Logic
end YesMetaZFC
