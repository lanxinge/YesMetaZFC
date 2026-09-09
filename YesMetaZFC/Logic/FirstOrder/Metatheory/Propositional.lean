import YesMetaZFC.Logic.FirstOrder.Metatheory.Basic

/-!
# 命题联结词元定理

本模块收纳不涉及量词和等词的经典联结词代数。所有公式共享同一个 free 上下文；
文献使用的 Hilbert 编码只作为对象公式保留，不再附带任何良构性旁证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
namespace Derives

universe u v w

/-- 两个否定结论可以交换蕴含的前件。 -/
theorem neg_imp_swap_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] (ψ ⟶ₘ ¬ₘ φ) ⟶ₘ (φ ⟶ₘ ¬ₘ ψ) := by
  derive_prop

/-- Hilbert 编码合取的交换律。 -/
theorem conj_encoded_comm_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] ¬ₘ (φ ⟶ₘ ¬ₘ ψ) ⟶ₘ ¬ₘ (ψ ⟶ₘ ¬ₘ φ) := by
  derive_prop

/-- 原生合取的交换律。 -/
theorem conj_comm_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] (φ ∧ₘ ψ) ⟶ₘ (ψ ∧ₘ φ) := by
  derive_prop

/-- 逻辑等价的自反性。 -/
theorem iff_refl_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ : OpenFormula σ free} :
    Γ ⊢ₘ[T] φ ↔ₘ φ := by
  derive_prop

/-- 逻辑等价的对称性。 -/
theorem iff_symm_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] (ψ ↔ₘ φ) ⟶ₘ (φ ↔ₘ ψ) := by
  derive_prop

/-- 已经导出的逻辑等价可直接交换两端。 -/
theorem iff_symm {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free}
    (hEquivalent : Γ ⊢ₘ[T] φ ↔ₘ ψ) :
    Γ ⊢ₘ[T] ψ ↔ₘ φ := by
  derive_prop

/-- 逻辑等价的传递性。 -/
theorem iff_trans_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ θ : OpenFormula σ free} :
    Γ ⊢ₘ[T] (ψ ↔ₘ φ) ⟶ₘ ((φ ↔ₘ θ) ⟶ₘ (ψ ↔ₘ θ)) := by
  derive_prop

/-- 两个已经导出的逻辑等价可直接传递合成。 -/
theorem iff_trans {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ θ : OpenFormula σ free}
    (hFirst : Γ ⊢ₘ[T] φ ↔ₘ ψ)
    (hSecond : Γ ⊢ₘ[T] ψ ↔ₘ θ) :
    Γ ⊢ₘ[T] φ ↔ₘ θ := by
  derive_prop

/-- 经典逻辑中，`¬φ → ψ` 与原生析取 `φ ∨ ψ` 等价。 -/
theorem neg_imp_disj_iff_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] ((¬ₘ φ) ⟶ₘ ψ) ↔ₘ (φ ∨ₘ ψ) := by
  derive_prop

/-- 逻辑等价可在另一个等价式的右侧合同替换。 -/
theorem iff_right_congr_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ θ : OpenFormula σ free}
    (hEquivalent : Γ ⊢ₘ[T] ψ ↔ₘ θ) :
    Γ ⊢ₘ[T] (φ ↔ₘ ψ) ↔ₘ (φ ↔ₘ θ) := by
  derive_prop

/-- 右结合三重合取与文献 Hilbert 编码的等价。 -/
theorem conj_right_assoc_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ θ : OpenFormula σ free} :
    Γ ⊢ₘ[T]
      (φ ∧ₘ (ψ ∧ₘ θ)) ↔ₘ ¬ₘ (φ ⟶ₘ (ψ ⟶ₘ ¬ₘ θ)) := by
  derive_prop

/-- 左结合三重合取与文献 Hilbert 编码的等价。 -/
theorem conj_left_assoc_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ θ : OpenFormula σ free} :
    Γ ⊢ₘ[T]
      ((φ ∧ₘ ψ) ∧ₘ θ) ↔ₘ ¬ₘ (φ ⟶ₘ (ψ ⟶ₘ ¬ₘ θ)) := by
  derive_prop

/-- 原生合取的结合律。 -/
theorem conj_assoc_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ θ : OpenFormula σ free} :
    Γ ⊢ₘ[T] (φ ∧ₘ (ψ ∧ₘ θ)) ↔ₘ ((φ ∧ₘ ψ) ∧ₘ θ) := by
  derive_prop

/-- 以 `¬ₘ φ ⟶ₘ ψ` 表示析取时的交换律。 -/
theorem disj_encoded_comm_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] (¬ₘ φ ⟶ₘ ψ) ⟶ₘ (¬ₘ ψ ⟶ₘ φ) := by
  derive_prop

/-- 原生析取的交换律。 -/
theorem disj_comm_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ : OpenFormula σ free} :
    Γ ⊢ₘ[T] (φ ∨ₘ ψ) ⟶ₘ (ψ ∨ₘ φ) := by
  derive_prop

/-- 原生析取的幂等律。 -/
theorem disj_idem_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ : OpenFormula σ free} :
    Γ ⊢ₘ[T] (φ ∨ₘ φ) ↔ₘ φ := by
  derive_prop

/-- 以 `¬ₘ φ ⟶ₘ ψ` 表示析取时的结合律。 -/
theorem disj_encoded_assoc_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ θ : OpenFormula σ free} :
    Γ ⊢ₘ[T]
      (¬ₘ φ ⟶ₘ (¬ₘ ψ ⟶ₘ θ)) ↔ₘ
        (¬ₘ (¬ₘ φ ⟶ₘ ψ) ⟶ₘ θ) := by
  derive_prop

/-- 原生析取的结合律。 -/
theorem disj_assoc_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {φ ψ θ : OpenFormula σ free} :
    Γ ⊢ₘ[T] (φ ∨ₘ (ψ ∨ₘ θ)) ↔ₘ ((φ ∨ₘ ψ) ∨ₘ θ) := by
  derive_prop

/-- guard 等价且 guard 下正文等价时，携带共同前件的两个合取等价。 -/
theorem guarded_conj_congr_m {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {common left right source target : OpenFormula σ free}
    (hGuard : Γ ⊢ₘ[T] left ↔ₘ right)
    (hBody : Γ ⊢ₘ[T] left ⟶ₘ (source ↔ₘ target)) :
    Γ ⊢ₘ[T] (common ∧ₘ (left ∧ₘ source)) ↔ₘ
      (common ∧ₘ (right ∧ₘ target)) := by
  derive_prop

end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
