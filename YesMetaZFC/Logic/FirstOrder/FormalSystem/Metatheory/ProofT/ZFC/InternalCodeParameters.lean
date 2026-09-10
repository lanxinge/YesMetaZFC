import YesMetaZFC.Automation.ObjectCodeParameters
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalBoundedInduction

/-! # 数码参数环境的实际公式表示与最终阶段对应 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceNumerals PureSourceInfinity
open ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 4096
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def codeArgs : (free : SetContext) → (Nat → 𝒩.Carrier .set) → Values 𝒩.Carrier free
  | .nil, _ => .nil
  | .set :: free, values => .cons (values 0) (codeArgs free (fun i => values (i + 1)))

def parameterValues (free : SetContext) (values : Nat → 𝒩.Carrier .set) (index : Nat) : 𝒩.Carrier .set :=
  (ObjectCodeParameters.terms free index).eval (templateEnv (codeArgs free values) : Env 𝒩 [] free)

theorem parameterValues_succ (free : SetContext) (values : Nat → 𝒩.Carrier .set) (i : Nat) :
    parameterValues (.set :: free) values (i + 1) = parameterValues free (fun i => values (i + 1)) i :=
  weakened_parameter_eval (𝒩 := 𝒩) (codeArgs free (fun i => values (i + 1))) (values 0) (ObjectCodeParameters.terms free i)

theorem parameterValues_in_range (free : SetContext) (values : Nat → 𝒩.Carrier .set) (index : Nat)
    (hi : index < free.length) : parameterValues free values index = values index := by
  induction free generalizing values index with
  | nil => cases hi
  | cons sort free ih =>
    cases sort
    cases index with
    | zero => rfl
    | succ index =>
      exact (parameterValues_succ free values index).trans
        (ih (fun i => values (i + 1)) index (Nat.lt_of_succ_lt_succ hi))

theorem parameterValues_numerals (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (free : SetContext) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values) :
    NumeralValues 𝒩 (parameterValues free values) := by
  induction free generalizing values with
  | nil =>
    intro i
    simp only [parameterValues, ObjectCodeParameters.terms, numeral_eval]
    exact ⟨numeral_natural h𝒩 _, z 𝒩, (omega_closed h𝒩).1, PureSourceNumeralSyntax.zero h𝒩⟩
  | cons sort free ih =>
    cases sort
    intro i
    cases i with
    | zero => exact hv 0
    | succ i =>
      exact Eq.mpr (congrArg (fun named => mem 𝒩 named (w 𝒩) ∧
        ∃ input, mem 𝒩 input (w 𝒩) ∧ PureSourceNumeralSyntax.Graph 𝒩 input named)
        (parameterValues_succ free values i)) (ih (fun i => values (i + 1)) (fun i => hv (i + 1)) i)

theorem parameterValues_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (free : SetContext) (values : Nat → 𝒩.Carrier .set) (i : Nat) :
    (ObjectCodeParameters.terms free i).eval (templateEnv (codeArgs free values) : Env 𝒩 [] free) =
    (ObjectCodeParameters.terms free i).eval (templateEnv (codeArgs (𝒩 := 𝒩) free values) : Env (canonical h𝒩) [] free) := by
  induction free generalizing values i with
  | nil =>
    simp only [ObjectCodeParameters.terms, numeral_eval]
    exact numeral_agrees h𝒩 _
  | cons sort free ih =>
    cases sort
    cases i with
    | zero => rfl
    | succ i =>
      exact (weakened_parameter_eval (𝒩 := 𝒩) (codeArgs free (fun i => values (i + 1))) (values 0)
        (ObjectCodeParameters.terms free i)).trans
          ((ih (fun i => values (i + 1)) i).trans
            (weakened_parameter_eval (𝒩 := canonical h𝒩) (codeArgs (𝒩 := 𝒩) free (fun i => values (i + 1)))
              (values 0) (ObjectCodeParameters.terms free i)).symm)

/-- 任意有限数码参数均有实际公式表示，内部归纳所需对应不再留给调用者。 -/
theorem bounded_bundle (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (body : SetOpenFormula (.set :: free))
    (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {limit named : 𝒩.Carrier .set} (hl : mem 𝒩 limit (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 limit named)
    (hp : ∀ input, mem 𝒩 input (w 𝒩) → mem 𝒩 input limit →
      ∀ code, mem 𝒩 code (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 input code →
        ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend code values) body)) :
    ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend named values) (ObjectBoundedReflection.allBody body)) := by
  have hc (code : 𝒩.Carrier .set) (input : SetOpenFormula (.set :: free)) :
      formula 𝒩 (ObjectCodeInstantiation.prepend code (parameterValues free values)) input =
        formula 𝒩 (ObjectCodeInstantiation.prepend code values) input := by
    apply ObjectCodeInstantiation.formula_values_congr
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact parameterValues_in_range free values i (Nat.lt_of_succ_lt_succ hi)
  have h := bounded_bundle_parameters h𝒩 (codeArgs free values) body (ObjectCodeParameters.terms free)
    (parameterValues_numerals h𝒩 free values hv) (parameterValues_agrees h𝒩 free values) hl hn hg (by
      intro input hi hm code hCode hg
      exact (hc code body).symm ▸ hp input hi hm code hCode hg)
  exact hc named (ObjectBoundedReflection.allBody body) ▸ h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
