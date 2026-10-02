import YesMetaZFC.Tactic.FirstOrderDerives
import YesMetaZFC.Logic.FirstOrder.Metatheory.Notation

/-!
# 基本一阶元数理定理

本模块提供后续元数学和自动化共同消费的基础命题逻辑定理。所有公式都由同一个
free 上下文索引；良构性与变量可容许性已由语法类型保证，不再进入定理参数。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
namespace Derives

universe u v w

/-- 交换两个嵌套蕴含的前件。 -/
theorem imp_exchange {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ θ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] ((θ ⟶ₘ (φ ⟶ₘ ψ)) ⟶ₘ (φ ⟶ₘ (θ ⟶ₘ ψ))) := by
  derive_prop

/-- 蕴含传递律，外层先给出前半段。 -/
theorem imp_trans_left {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ θ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] ((φ ⟶ₘ ψ) ⟶ₘ ((θ ⟶ₘ φ) ⟶ₘ (θ ⟶ₘ ψ))) := by
  derive_prop

/-- 蕴含传递律，外层先给出后半段。 -/
theorem imp_trans_right {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ θ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] ((θ ⟶ₘ φ) ⟶ₘ ((φ ⟶ₘ ψ) ⟶ₘ (θ ⟶ₘ ψ))) := by
  derive_prop

/-- 两个已证明蕴含的传递合成。 -/
theorem imp_trans {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ θ : OpenFormula σ free}
    (hFirst : Γ ⊢ₘ[T] φ ⟶ₘ ψ)
    (hSecond : Γ ⊢ₘ[T] ψ ⟶ₘ θ) :
    Γ ⊢ₘ[T] φ ⟶ₘ θ := by
  derive_prop

/-- 合取可以推出“由左侧推出右侧”的蕴含。 -/
theorem conj_to_imp {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] (φ ∧ₘ ψ) ⟶ₘ (φ ⟶ₘ ψ) := by
  derive_prop

/-- 两个蕴含可以逐分量映射一个合取。 -/
theorem conj_imp_mono {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ₁ φ₂ ψ₁ ψ₂ : OpenFormula σ free} :
    Γ ⊢ₘ[T]
      (φ₁ ⟶ₘ ψ₁) ⟶ₘ
        ((φ₂ ⟶ₘ ψ₂) ⟶ₘ ((φ₁ ∧ₘ φ₂) ⟶ₘ (ψ₁ ∧ₘ ψ₂))) := by
  derive_prop

/-- 若在否定 `φ` 的局部上下文中同时推出 `ψ` 与 `¬ψ`，则原上下文推出 `φ`。 -/
theorem of_neg_assumption_contradiction {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free}
    (hPositive : (¬ₘ φ :: Γ) ⊢ₘ[T] ψ)
    (hNegative : (¬ₘ φ :: Γ) ⊢ₘ[T] ¬ₘ ψ) :
    Γ ⊢ₘ[T] φ := by
  derive_prop

/-- 若从 `φ` 与 `¬φ` 两个扩张上下文都能推出 `ψ`，则原上下文已经推出 `ψ`。 -/
theorem by_formula_cases {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free}
    (hNegative : (¬ₘ φ :: Γ) ⊢ₘ[T] ψ)
    (hPositive : (φ :: Γ) ⊢ₘ[T] ψ) :
    Γ ⊢ₘ[T] ψ := by
  derive_prop

/-- 双重否定消去的蕴含形式。 -/
theorem double_negation_elim_imp {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ : OpenFormula σ free} :
    Γ ⊢ₘ[T] ¬ₘ ¬ₘ φ ⟶ₘ φ := by
  derive_prop

/-- 若 `φ` 推出 `¬φ`，则推出 `¬φ`。 -/
theorem self_negation_elim {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ : OpenFormula σ free} :
    Γ ⊢ₘ[T] (φ ⟶ₘ ¬ₘ φ) ⟶ₘ ¬ₘ φ := by
  derive_prop

/-- 双重否定引入的蕴含形式。 -/
theorem double_negation_intro_imp {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ : OpenFormula σ free} :
    Γ ⊢ₘ[T] φ ⟶ₘ ¬ₘ ¬ₘ φ := by
  derive_prop

/-- 经典逆否命题：逆否蕴含可以还原原蕴含。 -/
theorem contraposition_reverse {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] (¬ₘ ψ ⟶ₘ ¬ₘ φ) ⟶ₘ (φ ⟶ₘ ψ) := by
  derive_prop

/-- 从蕴含推出其逆否命题。 -/
theorem contraposition {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] (φ ⟶ₘ ψ) ⟶ₘ (¬ₘ ψ ⟶ₘ ¬ₘ φ) := by
  derive_prop

/-- 以 `¬ₘ (φ ⟶ₘ ¬ₘ ψ)` 表示的 Hilbert 合取引入。 -/
theorem encoded_conj_intro {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] φ ⟶ₘ (ψ ⟶ₘ ¬ₘ (φ ⟶ₘ ¬ₘ ψ)) := by
  derive_prop

/-- 两个共同前件下的结论可以组成 Hilbert 编码合取。 -/
theorem encoded_conj_intro_under {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ θ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T]
      (θ ⟶ₘ φ) ⟶ₘ
        ((θ ⟶ₘ ψ) ⟶ₘ (θ ⟶ₘ ¬ₘ (φ ⟶ₘ ¬ₘ ψ))) := by
  derive_prop

/-- 否定一个蕴含会推出其后件的否定。 -/
theorem not_imp_elim_right {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] ¬ₘ (φ ⟶ₘ ψ) ⟶ₘ ¬ₘ ψ := by
  derive_prop

/-- 否定一个蕴含会推出其前件。 -/
theorem not_imp_elim_left {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] ¬ₘ (φ ⟶ₘ ψ) ⟶ₘ φ := by
  derive_prop

/-- Hilbert 编码合取推出右侧公式。 -/
theorem encoded_conj_elim_right {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] ¬ₘ (φ ⟶ₘ ¬ₘ ψ) ⟶ₘ ψ := by
  derive_prop

/-- Hilbert 编码合取推出左侧公式。 -/
theorem encoded_conj_elim_left {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] ¬ₘ (φ ⟶ₘ ¬ₘ ψ) ⟶ₘ φ := by
  derive_prop

/-- 原生合取与 Hilbert 编码合取在经典 `Derives` 中等价。 -/
theorem conj_iff_encoded {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] (φ ∧ₘ ψ) ↔ₘ ¬ₘ (φ ⟶ₘ ¬ₘ ψ) := by
  derive_prop

end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
