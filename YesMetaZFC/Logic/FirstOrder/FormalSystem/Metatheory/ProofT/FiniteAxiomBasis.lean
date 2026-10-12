import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.AxiomPresentation

/-! # 原理论内部的有限公理基

公理基的每一项仍是原公理；原理论的任意公理均可由该基作普通 Hilbert 推导。
理论切换由既有 theory_cut 完成，适用于任意自由上下文和局部假设。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
open Nonlogical.BasicSetTheory
set_option autoImplicit false

structure FiniteAxiomBasis (T : SetTheory) where
  axioms : List SetSentence
  sound : ∀ φ, φ ∈ axioms → T φ
  complete : ∀ {φ}, T φ → Derives (fun ψ => ψ ∈ axioms) [] φ

namespace FiniteAxiomBasis
def theory {T : SetTheory} (basis : FiniteAxiomBasis T) : SetTheory := fun φ => φ ∈ basis.axioms

def singleton (φ : SetSentence) : FiniteAxiomBasis (Theory.singleton φ) where
  axioms := [φ]
  sound _ h := by
    cases h with
    | head => rfl
    | tail _ h => cases h
  complete h := by
    cases h
    exact FirstOrder.Derives.theory_axiom (.head _)

def union {T U : SetTheory} (left : FiniteAxiomBasis T) (right : FiniteAxiomBasis U) :
    FiniteAxiomBasis (Theory.union T U) where
  axioms := left.axioms ++ right.axioms
  sound φ h := by
    have append_cases (xs ys : List SetSentence)
        (h : φ ∈ xs ++ ys) : φ ∈ xs ∨ φ ∈ ys := by
      induction xs with
      | nil => exact Or.inr h
      | cons head tail ih =>
        cases h with
        | head => exact Or.inl (.head _)
        | tail _ h =>
          cases ih h with
          | inl h => exact Or.inl (.tail _ h)
          | inr h => exact Or.inr h
    rcases append_cases left.axioms right.axioms h with h | h
    · exact Or.inl (left.sound φ h)
    · exact Or.inr (right.sound φ h)
  complete h := by
    rcases h with h | h
    · exact (left.complete h).theory_weaken (fun h => List.mem_append_left _ h)
    · exact (right.complete h).theory_weaken (fun h => List.mem_append_right _ h)

def insert (φ : SetSentence) {T : SetTheory} (basis : FiniteAxiomBasis T) :
    FiniteAxiomBasis (Theory.insert φ T) := union (singleton φ) basis

def congr {T U : SetTheory} (basis : FiniteAxiomBasis T) (h : ∀ φ, T φ ↔ U φ) :
    FiniteAxiomBasis U where
  axioms := basis.axioms
  sound φ hφ := (h φ).mp (basis.sound φ hφ)
  complete hφ := basis.complete ((h _).mpr hφ)

theorem derives_iff {T : SetTheory} (basis : FiniteAxiomBasis T)
    {free : SetContext} {Γ : Context signature free} {φ : SetOpenFormula free} :
    Derives basis.theory Γ φ ↔ Derives T Γ φ :=
  ⟨fun h => h.theory_weaken (basis.sound _), fun h => FirstOrder.Derives.theory_cut basis.complete h⟩

private instance : BEq SetSentence where
  beq φ ψ := decide (QuineEncoding.SyntaxCoding.formula_code φ = QuineEncoding.SyntaxCoding.formula_code ψ)

private instance : LawfulBEq SetSentence where
  eq_of_beq h := QuineEncoding.SyntaxCoding.formula_code_injective (of_decide_eq_true h)
  rfl := by intro φ; exact decide_eq_true rfl

/-- 理论并产生的重复公理只保留一次；结构相等是可计算的，不使用经典选择判定。 -/
def compact {T : SetTheory} (basis : FiniteAxiomBasis T) : FiniteAxiomBasis T where
  axioms := basis.axioms.eraseDups
  sound φ h := basis.sound φ (List.mem_eraseDups.mp h)
  complete h := (basis.complete h).theory_weaken (fun h => List.mem_eraseDups.mpr h)
end FiniteAxiomBasis
end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT
