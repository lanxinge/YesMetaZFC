import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Core
import YesMetaZFC.Logic.FirstOrder.Metatheory.Equality.Basic

/-!
# ProofT 内在 Gödel 配对反演

本模块迁移配对反演的数学核心。项的排序与作用域由内在语法携带，故不再为每个
坐标维护 `Admissible`、自由变量支撑或 token 合法性证明。有限穷尽仍由
`ProofT.CertificateCore.member_elim` 提供。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace IntrinsicPairing

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode

set_option autoImplicit false

private theorem lift_closed
    {T : SetTheory} {free : SetContext}
    {formula : SetSentence}
    (hFormula :
      Derives T ([] : Context signature []) formula) :
    Derives T ([] : Context signature free)
      (Formula.renameFree
        (VariableRenaming.empty : VariableRenaming [] free)
        formula) := by
  simpa using
    FirstOrder.Derives.free_renaming
      (T := T)
      (ρ := (VariableRenaming.empty : VariableRenaming [] free))
      hFormula

private theorem pair_formula_rename_empty
    {free : SetContext} (tag value : Nat) :
    Formula.renameFree
        (VariableRenaming.empty : VariableRenaming [] free)
        (godel_pairₘ(
          (numₘ(tag) : SetTerm [] []),
          (numₘ(value) : SetTerm [] [])) ≐ₘ
          (numₘ(godel_pair_value tag value) : SetTerm [] [])) =
      (godel_pairₘ(
        (numₘ(tag) : SetTerm [] free),
        (numₘ(value) : SetTerm [] free)) ≐ₘ
        (numₘ(godel_pair_value tag value) : SetTerm [] free)) := by
  simp only [Formula.renameFree, Formula.rename, Renaming.free,
    Formula.renameMapped, Term.renameMapped, Arguments.renameMapped,
    finite_numeral_term_renameMapped]

private theorem neg_numeral_equality_rename_empty
    {free : SetContext} (left right : Nat) :
    Formula.renameFree
        (VariableRenaming.empty : VariableRenaming [] free)
        (¬ₘ ((numₘ(left) : SetTerm [] []) ≐ₘ
          (numₘ(right) : SetTerm [] []))) =
      (¬ₘ ((numₘ(left) : SetTerm [] free) ≐ₘ
        (numₘ(right) : SetTerm [] free))) := by
  simp only [Formula.renameFree, Formula.rename, Renaming.free,
    Formula.renameMapped, finite_numeral_term_renameMapped]

private def pair_right_context {free : SetContext}
    (tag : Nat) : SetTerm [SetSort.set] free :=
  godel_pairing_term
    (Term.weakenBound SetSort.set (numₘ(tag) : SetTerm [] free))
    (.bvar .here)

private def pair_left_context {free : SetContext}
    (right : SetTerm [] free) : SetTerm [SetSort.set] free :=
  godel_pairing_term
    (.bvar .here)
    (Term.weakenBound SetSort.set right)

private def pair_right_context_of_left {free : SetContext}
    (left : SetTerm [] free) : SetTerm [SetSort.set] free :=
  godel_pairing_term
    (Term.weakenBound SetSort.set left)
    (.bvar .here)

/-- 固定左坐标时，等式可穿过 Gödel 配对项。 -/
theorem tagged_code_congr
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (tag : Nat) (payload : SetTerm [] free) (value : Nat)
    (hEquality :
      Γ ⊢ₘ[T]
        payload ≐ₘ numₘ(value)) :
    Γ ⊢ₘ[T]
      godel_pairₘ(numₘ(tag), payload) ≐ₘ
        godel_pairₘ(numₘ(tag), numₘ(value)) := by
  have hCong :=
    Metatheory.Derives.term_context_congr_of_equality
      (T := T) (Γ := Γ)
      (pair_right_context tag)
      hEquality
  simpa only [pair_right_context,
    Term.instantiateTop_app,
    Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil,
    Term.instantiateTop_weakenBound,
    Term.instantiateTop_bvar_here] using! hCong

/-- 两个坐标的等式可同时穿过 Gödel 配对项。 -/
theorem pair_congr_of_equalities
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (left₁ left₂ right₁ right₂ : SetTerm [] free)
    (hLeftEquality :
      Γ ⊢ₘ[T] left₁ ≐ₘ left₂)
    (hRightEquality :
      Γ ⊢ₘ[T] right₁ ≐ₘ right₂) :
    Γ ⊢ₘ[T]
      godel_pairₘ(left₁, right₁) ≐ₘ
        godel_pairₘ(left₂, right₂) := by
  have hLeft :=
    Metatheory.Derives.term_context_congr_of_equality
      (T := T) (Γ := Γ)
      (pair_left_context right₁)
      hLeftEquality
  have hRight :=
    Metatheory.Derives.term_context_congr_of_equality
      (T := T) (Γ := Γ)
      (pair_right_context_of_left left₂)
      hRightEquality
  have hLeft' :
      Γ ⊢ₘ[T]
        godel_pairₘ(left₁, right₁) ≐ₘ
          godel_pairₘ(left₂, right₁) := by
    simpa only [pair_left_context,
      Term.instantiateTop_app,
      Arguments.instantiateTop_cons,
      Arguments.instantiateTop_nil,
      Term.instantiateTop_weakenBound,
      Term.instantiateTop_bvar_here] using! hLeft
  have hRight' :
      Γ ⊢ₘ[T]
        godel_pairₘ(left₂, right₁) ≐ₘ
          godel_pairₘ(left₂, right₂) := by
    simpa only [pair_right_context_of_left,
      Term.instantiateTop_app,
      Arguments.instantiateTop_cons,
      Arguments.instantiateTop_nil,
      Term.instantiateTop_weakenBound,
      Term.instantiateTop_bvar_here] using! hRight
  exact Metatheory.Derives.equality_trans hLeft' hRight'

/-- 无效的标准配对值直接给出对象层矛盾。 -/
theorem falsum_of_tagged_code
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    {free : SetContext}
    {Γ : Context signature free}
    (tag value raw : Nat)
    (certificateCode payload : SetTerm [] free)
    (hCertificateAt :
      Γ ⊢ₘ[T]
        certificateCode ≐ₘ numₘ(raw))
    (hCode :
      Γ ⊢ₘ[T]
        certificateCode ≐ₘ
          godel_pairₘ(numₘ(tag), payload))
    (hPayloadEquality :
      Γ ⊢ₘ[T]
        payload ≐ₘ numₘ(value))
    (hInvalid : raw ≠ godel_pair_value tag value) :
    Γ ⊢ₘ[T] Formula.falsum := by
  have hCodeGround :=
    tagged_code_congr tag payload value hPayloadEquality
  have hGround :
      Derives T ([] : Context signature []) (
        godel_pairₘ(numₘ(tag), numₘ(value)) ≐ₘ
          numₘ(godel_pair_value tag value)) :=
    C.pair_value tag value
  have hGroundAt :
      Γ ⊢ₘ[T]
        godel_pairₘ(numₘ(tag), numₘ(value)) ≐ₘ
          numₘ(godel_pair_value tag value) :=
    by
      have hGroundFree := lift_closed (free := free) hGround
      rw [pair_formula_rename_empty] at hGroundFree
      have hGroundContext :=
        FirstOrder.Derives.context_weaken
          (Γ := ([] : Context signature free))
          (Δ := Γ) (by simp) hGroundFree
      exact hGroundContext
  have hNumeralEquality :
      Γ ⊢ₘ[T]
        numₘ(raw) ≐ₘ numₘ(godel_pair_value tag value) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hCertificateAt)
      (Metatheory.Derives.equality_trans
        hCode
        (Metatheory.Derives.equality_trans
          hCodeGround hGroundAt))
  exact FirstOrder.Derives.neg_elim
    hNumeralEquality
    (by
      have hNumeralFree :=
        lift_closed
          (free := free)
          (C.numeral_ne hInvalid)
      have hNumeralContext :=
        FirstOrder.Derives.context_weaken
          (Γ := ([] : Context signature free))
          (Δ := Γ) (by simp) hNumeralFree
      rw [neg_numeral_equality_rename_empty] at hNumeralContext
      exact hNumeralContext)

/-- 地面配对等式唯一锁定右坐标。 -/
theorem pair_right_unique
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    {free : SetContext}
    {Γ : Context signature free}
    (raw tag : Nat)
    (payload : SetTerm [] free)
    (hPayloadBound :
      Γ ⊢ₘ[T]
        payload ∈ₘ Sₘ(numₘ(raw)))
    (hPair :
      Γ ⊢ₘ[T]
        numₘ(raw) ≐ₘ
          godel_pairₘ(numₘ(tag), payload)) :
    Γ ⊢ₘ[T]
      payload ≐ₘ
        numₘ((godel_unpair_value raw).2) := by
  have hPayloadMember :
      Γ ⊢ₘ[T]
        payload ∈ₘ numₘ(raw + 1) := by
    simpa [finite_numeral_term, successor_term] using
      hPayloadBound
  let conclusion : SetOpenFormula free :=
    payload ≐ₘ numₘ((godel_unpair_value raw).2)
  apply C.member_elim
    (raw + 1) payload conclusion hPayloadMember
  intro value hValueBound
  let equality : SetOpenFormula free := payload ≐ₘ numₘ(value)
  let Δ : Context signature free := equality :: Γ
  change Δ ⊢ₘ[T] conclusion
  have hPayloadEquality :
      Δ ⊢ₘ[T] payload ≐ₘ numₘ(value) := by
    simpa [Δ, equality] using
      (FirstOrder.Derives.assumption
        (T := T)
        (Γ := Δ)
        (formula := equality)
        (by simp [Δ]))
  have hPairAt :
      Δ ⊢ₘ[T]
        numₘ(raw) ≐ₘ
          godel_pairₘ(numₘ(tag), payload) :=
    FirstOrder.Derives.context_weaken_cons hPair
  by_cases hCode : raw = godel_pair_value tag value
  · have hCoordinates :
        tag = (godel_unpair_value raw).1 ∧
          value = (godel_unpair_value raw).2 := by
      apply godel_pair_value_eq_iff.mp
      rw [← hCode, godel_unpair_value_spec]
    simpa [conclusion, hCoordinates.2] using hPayloadEquality
  · have hFalse :
        Δ ⊢ₘ[T] Formula.falsum :=
      falsum_of_tagged_code
        C
        tag value raw
        (numₘ(raw)) payload
        (FirstOrder.Derives.eq_refl
          (T := T) (Γ := Δ) (numₘ(raw)))
        hPairAt hPayloadEquality hCode
    exact FirstOrder.Derives.falsum_elim hFalse

/-- 地面配对等式唯一锁定左坐标。 -/
theorem pair_left_unique
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    {free : SetContext}
    {Γ : Context signature free}
    (raw : Nat)
    (left right : SetTerm [] free)
    (hLeftBound :
      Γ ⊢ₘ[T]
        left ∈ₘ Sₘ(numₘ(raw)))
    (hRightBound :
      Γ ⊢ₘ[T]
        right ∈ₘ Sₘ(numₘ(raw)))
    (hPair :
      Γ ⊢ₘ[T]
        numₘ(raw) ≐ₘ
          godel_pairₘ(left, right)) :
    Γ ⊢ₘ[T]
      left ≐ₘ
        numₘ((godel_unpair_value raw).1) := by
  have hLeftMember :
      Γ ⊢ₘ[T]
        left ∈ₘ numₘ(raw + 1) := by
    simpa [finite_numeral_term, successor_term] using
      hLeftBound
  let conclusion : SetOpenFormula free :=
    left ≐ₘ numₘ((godel_unpair_value raw).1)
  apply C.member_elim
    (raw + 1) left conclusion hLeftMember
  intro value hValueBound
  let equality : SetOpenFormula free := left ≐ₘ numₘ(value)
  let Δ : Context signature free := equality :: Γ
  change Δ ⊢ₘ[T] conclusion
  have hLeftEquality :
      Δ ⊢ₘ[T] left ≐ₘ numₘ(value) := by
    simpa [Δ, equality] using
      (FirstOrder.Derives.assumption
        (T := T)
        (Γ := Δ)
        (formula := equality)
        (by simp [Δ]))
  have hPairAt :
      Δ ⊢ₘ[T]
        numₘ(raw) ≐ₘ godel_pairₘ(left, right) :=
    FirstOrder.Derives.context_weaken_cons hPair
  have hPairAtValue :
      Δ ⊢ₘ[T]
        godel_pairₘ(left, right) ≐ₘ
          godel_pairₘ(numₘ(value), right) := by
    have hCong :=
      Metatheory.Derives.term_context_congr_of_equality
        (T := T) (Γ := Δ)
        (pair_left_context right)
        hLeftEquality
    simpa [pair_left_context] using! hCong
  have hPairValue :
      Δ ⊢ₘ[T]
        numₘ(raw) ≐ₘ godel_pairₘ(numₘ(value), right) :=
    Metatheory.Derives.equality_trans hPairAt hPairAtValue
  have hRightEquality :
      Δ ⊢ₘ[T]
        right ≐ₘ numₘ((godel_unpair_value raw).2) :=
    pair_right_unique
      C raw value right
      (FirstOrder.Derives.context_weaken_cons hRightBound)
      hPairValue
  by_cases hCode :
      raw =
        godel_pair_value value
          (godel_unpair_value raw).2
  · have hCoordinates :
        value = (godel_unpair_value raw).1 := by
      apply And.left <| godel_pair_value_eq_iff.mp
        (show
          godel_pair_value value (godel_unpair_value raw).2 =
            godel_pair_value
              (godel_unpair_value raw).1
              (godel_unpair_value raw).2 by
          calc
            _ = raw := hCode.symm
            _ = _ := (godel_unpair_value_spec raw).symm)
    simpa [conclusion, hCoordinates] using hLeftEquality
  · exact FirstOrder.Derives.falsum_elim <|
      falsum_of_tagged_code
        C
        value (godel_unpair_value raw).2 raw
        (numₘ(raw)) right
        (FirstOrder.Derives.eq_refl
          (T := T) (Γ := Δ) (numₘ(raw)))
        hPairValue hRightEquality hCode

end IntrinsicPairing
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
