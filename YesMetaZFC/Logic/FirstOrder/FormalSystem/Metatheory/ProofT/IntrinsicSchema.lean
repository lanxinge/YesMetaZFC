import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Hierarchy
import YesMetaZFC.Logic.FirstOrder.Derivation.Propositional

/-!
# ProofT 的内在 schema 分支

schema 分支直接保存带上下文索引的条件函数，因此分支组合不再需要 `FreeVarId`、
`Admissible` 或外部新鲜性证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace IntrinsicSchema

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 二元条件表 -/

/-- 一个带证书标签的二元内在条件分支。 -/
structure BinaryBranch where
  tag : Nat
  condition :
    ∀ {bound free : SetContext},
      SetTerm bound free → SetTerm bound free → SetFormula bound free
  delta0 :
    ∀ {bound free : SetContext}
      (formula certificate : SetTerm bound free),
      Formula.IsDelta0 set_levy_bound
        (condition formula certificate)

/-- 二元分支表的右结合有限析取。 -/
def binary_condition_list
    (branches : List BinaryBranch)
    {bound free : SetContext}
  (formula certificate : SetTerm bound free) :
    SetFormula bound free :=
  match branches with
  | [] => Formula.falsum
  | branch :: rest =>
      branch.condition formula certificate ∨ₘ
        binary_condition_list rest formula certificate

theorem binary_condition_list_delta0
    (branches : List BinaryBranch)
    {bound free : SetContext}
    (formula certificate : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (binary_condition_list branches formula certificate) := by
  induction branches with
  | nil =>
      exact Formula.IsDelta0.falsum
  | cons branch rest ih =>
      simpa [binary_condition_list] using
        Formula.IsDelta0.disj
          (branch.delta0 formula certificate)
          ih

theorem disj_neg
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    {left right : SetOpenFormula free}
    (hLeft : Γ ⊢ₘ[T] ¬ₘ left)
    (hRight : Γ ⊢ₘ[T] ¬ₘ right) :
    Γ ⊢ₘ[T] ¬ₘ(left ∨ₘ right) := by
  derive_prop

theorem binary_condition_list_neg
    {T : SetTheory}
    {free : SetContext}
    {branches : List BinaryBranch}
    {Γ : Context signature free}
    {formula certificate : SetOpenTerm free}
    (hReject :
      ∀ branch, branch ∈ branches →
        Γ ⊢ₘ[T] ¬ₘ branch.condition formula certificate) :
    Γ ⊢ₘ[T] ¬ₘ(binary_condition_list branches formula certificate) := by
  induction branches with
  | nil =>
      exact FirstOrder.Derives.neg_intro
        (FirstOrder.Derives.assumption List.mem_cons_self)
  | cons head rest ih =>
      have hHeadNeg : Γ ⊢ₘ[T] ¬ₘ(head.condition formula certificate) := by
        exact hReject head (by simp)
      have hRestNeg : Γ ⊢ₘ[T]
          ¬ₘ(binary_condition_list rest formula certificate) := by
        apply ih
        intro branch hBranch
        exact hReject branch (by simp [hBranch])
      simpa [binary_condition_list] using
        disj_neg hHeadNeg hRestNeg

theorem binary_condition_of_mem
    {T : SetTheory}
    {branches : List BinaryBranch}
    {branch : BinaryBranch}
    (hBranch : branch ∈ branches)
    {free : SetContext}
    {Γ : Context signature free}
    {formula certificate : SetOpenTerm free}
    (hCondition :
      Γ ⊢ₘ[T] branch.condition formula certificate) :
    Γ ⊢ₘ[T] binary_condition_list branches formula certificate := by
  induction branches with
  | nil =>
      simp at hBranch
  | cons head rest ih =>
      rcases List.mem_cons.mp hBranch with rfl | hBranch
      · simpa [binary_condition_list] using
          FirstOrder.Derives.disj_intro_left hCondition
      · simpa [binary_condition_list] using
          FirstOrder.Derives.disj_intro_right
            (ih hBranch)

/-! ## 三元 schema 条件 -/

/--
一个 schema 分支的内在签名。三个 free 槽位依次表示 formula、certificate、base。
-/
structure TernaryBranch where
  tag : Nat
  condition :
    ∀ {bound free : SetContext},
      SetTerm bound free → SetTerm bound free → SetTerm bound free →
        SetFormula bound free
  delta0 :
    ∀ {bound free : SetContext}
      (formula certificate base : SetTerm bound free),
      Formula.IsDelta0 set_levy_bound
        (condition formula certificate base)

/-- schema 分支表的右结合有限析取。 -/
def condition_list
    (branches : List TernaryBranch)
    {bound free : SetContext}
  (formula certificate base : SetTerm bound free) :
    SetFormula bound free :=
  match branches with
  | [] => Formula.falsum
  | branch :: rest =>
      branch.condition formula certificate base ∨ₘ
        condition_list rest formula certificate base

theorem condition_list_delta0
    (branches : List TernaryBranch)
    {bound free : SetContext}
    (formula certificate base : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (condition_list branches formula certificate base) := by
  induction branches with
  | nil =>
      exact Formula.IsDelta0.falsum
  | cons branch rest ih =>
      simpa [condition_list] using
        Formula.IsDelta0.disj
          (branch.delta0 formula certificate base)
          ih

theorem condition_list_neg
    {T : SetTheory}
    {free : SetContext}
    {branches : List TernaryBranch}
    {Γ : Context signature free}
    {formula certificate base : SetOpenTerm free}
    (hReject :
      ∀ branch, branch ∈ branches →
        Γ ⊢ₘ[T] ¬ₘ branch.condition formula certificate base) :
    Γ ⊢ₘ[T] ¬ₘ(condition_list branches formula certificate base) := by
  induction branches with
  | nil =>
      exact FirstOrder.Derives.neg_intro
        (FirstOrder.Derives.assumption List.mem_cons_self)
  | cons head rest ih =>
      have hHeadNeg : Γ ⊢ₘ[T] ¬ₘ(head.condition formula certificate base) := by
        exact hReject head (by simp)
      have hRestNeg : Γ ⊢ₘ[T]
          ¬ₘ(condition_list rest formula certificate base) := by
        apply ih
        intro branch hBranch
        exact hReject branch (by simp [hBranch])
      simpa [condition_list] using
        disj_neg hHeadNeg hRestNeg

theorem condition_of_mem
    {T : SetTheory}
    {branches : List TernaryBranch}
    {branch : TernaryBranch}
    (hBranch : branch ∈ branches)
    {free : SetContext}
    {Γ : Context signature free}
    {formula certificate base : SetOpenTerm free}
    (hCondition :
      Γ ⊢ₘ[T] branch.condition formula certificate base) :
    Γ ⊢ₘ[T] condition_list branches formula certificate base := by
  induction branches with
  | nil =>
      simp at hBranch
  | cons head rest ih =>
      rcases List.mem_cons.mp hBranch with rfl | hBranch
      · simpa [condition_list] using
          FirstOrder.Derives.disj_intro_left hCondition
      · simpa [condition_list] using
          FirstOrder.Derives.disj_intro_right
            (ih hBranch)

end IntrinsicSchema
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
