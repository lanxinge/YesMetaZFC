import YesMetaZFC.Automation.ObjectNumeralSyntax
import YesMetaZFC.Automation.ObjectSyntaxTransformConcrete

/-! # 当前 quotation 的保参数数码自代入关系

先构造 numeral 项码，再用完整同时自由代入图替换首槽，尾部参数逐槽恒等。
每个有限参数上下文对应一个三元模板；正负推导与对象唯一性复用原图和最小见证层。
-/
namespace YesMetaZFC.Automation.ObjectDiagonal
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT IntrinsicQuotation QuineEncoding ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

abbrev UnaryFormula := SetOpenFormula [SetSort.set]
abbrev ParameterFormula_m (parameters : SetContext) := SetOpenFormula (SetSort.set :: parameters)

/-- 空参数时保留原空替换；非空参数逐槽恒等。 -/
def parameterIdentity_m : (parameters : SetContext) → VariableSubstitution signature parameters [] parameters
  | [] => VariableSubstitution.empty
  | _ :: _ => VariableSubstitution.freeId

theorem parameterIdentity_apply_m {parameters : SetContext} {s : SetSort} (v : Variable parameters s) :
    parameterIdentity_m parameters v = .fvar v := by
  cases parameters with
  | nil => cases v
  | cons s ps => rfl

def parameterCodes_m (parameters : SetContext) : List Nat :=
  (SyntaxEncode.argumentsList (SyntaxEncode.substitutionArguments parameters
    (parameterIdentity_m parameters))).map treeValue

def code {parameters : SetContext} (body : ParameterFormula_m parameters) : Nat :=
  treeValue (SyntaxEncode.formula body)
def instantiate {parameters : SetContext} (body : ParameterFormula_m parameters)
    (number : Nat) : SetOpenFormula parameters :=
  body.substituteFree (VariableSubstitution.cons (numₘ(number)) (parameterIdentity_m parameters))
def value {parameters : SetContext} (body : ParameterFormula_m parameters) (number : Nat) : Nat :=
  treeValue (SyntaxEncode.formula (instantiate body number))

theorem instantiate_eq_m {parameters : SetContext} (body : ParameterFormula_m parameters) (number : Nat) :
    instantiate body number = body.instantiateFreeTop (numₘ(number)) := by
  simp only [instantiate, Formula.substituteFree, Formula.substitute,
    Substitution.free_map, Formula.instantiateFreeTop, Substitution.instantiateFreeTop]
  congr 1
  funext s v
  cases v with
  | here => rfl
  | there v => exact parameterIdentity_apply_m v

/-- 已有支撑公理的具体能力包；没有加入任何额外理论公理。 -/
structure Support (T : SetTheory) where
  certificate : CertificateCore T
  core : Core T
  sequences : FiniteSequenceGraphSupport T
  power : ∀ {φ}, power_set_operator_theory φ → T φ
  infinity : ∀ {φ}, infinity_theory φ → T φ
  numeral_domain : ∀ number, Derives T [] (core.code_domain.condition (numₘ(number) : Code))

def numeral : FormulaTemplate.Ternary where
  body := ObjectNumeralSyntax.condition (.fvar .here) (.fvar (.there (.there .here)))
@[simp] theorem numeral_apply {bound free : SetContext} (input parameter output : SetTerm bound free) :
    numeral input parameter output = ObjectNumeralSyntax.condition input output := by
  simp [numeral, FormulaTemplate.apply_three, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

def substitutionCondition {parameters : SetContext} {bound free : SetContext} (input parameter output : SetTerm bound free) : SetFormula bound free :=
  ObjectSyntaxTransform.condition (numₘ(3)) (numₘ(0))
    (structural_list_code_term (parameter :: (parameterCodes_m parameters).map (fun n => numₘ(n)))) input output
@[simp] theorem substitutionCondition_substituteMapped {parameters : SetContext} {sb sf tb tf : SetContext}
    (input parameter output : SetTerm sb sf) (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (substitutionCondition (parameters := parameters) input parameter output).substituteMapped bs fs =
      substitutionCondition (parameters := parameters) (input.substituteMapped bs fs) (parameter.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [substitutionCondition, List.map_map, Function.comp_def]

def substitution {parameters : SetContext} : FormulaTemplate.Ternary where
  body := substitutionCondition (parameters := parameters) (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
@[simp] theorem substitution_apply {parameters : SetContext} {bound free : SetContext} (input parameter output : SetTerm bound free) :
    substitution (parameters := parameters) input parameter output = substitutionCondition (parameters := parameters) input parameter output := by
  simp [substitution, FormulaTemplate.apply_three, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

private theorem substitution_row_m {parameters : SetContext} {T : SetTheory} (C : CertificateCore T) (input parameter output : Nat) :
    Derives T ([] : Context signature []) (IntrinsicQuotation.node 3 [numₘ(3), numₘ(0), numₘ(listValue (parameter :: parameterCodes_m parameters)), numₘ(input), numₘ(output)] ≐ₘ
      IntrinsicQuotation.node 3 [numₘ(3), numₘ(0), structural_list_code_term ((parameter :: parameterCodes_m parameters).map (fun n => numₘ(n))), numₘ(input), numₘ(output)]) :=
  node_congr 3 (.cons (Metatheory.Derives.equality_refl _)
    (.cons (Metatheory.Derives.equality_refl _)
      (.cons (FirstOrder.Derives.eq_symm (numeral_list_evaluate C (parameter :: parameterCodes_m parameters)))
        (.cons (Metatheory.Derives.equality_refl _) (.cons (Metatheory.Derives.equality_refl _) .nil)))))

private theorem substitution_checked {parameters : SetContext} (body : ParameterFormula_m parameters) (number output : Nat) :
    ObjectSyntaxTransform.checked 3 0 (listValue (ObjectNumeralSyntax.value number :: parameterCodes_m parameters)) (code body) output = true ↔
      value body number = output := by
  simpa only [code, value, instantiate, ← ObjectNumeralSyntax.value_encode_m, SyntaxEncode.substitutionArguments,
    SyntaxEncode.argumentsList, VariableSubstitution.cons, List.map_cons, parameterCodes_m]
    using ObjectSyntaxTransform.checked_substituteFree body
      (VariableSubstitution.cons (numₘ(number) : SetOpenTerm parameters) (parameterIdentity_m parameters)) output

theorem numeral_positive {T : SetTheory} (S : Support T) (number : Nat) :
    Derives T [] (numeral (numₘ(number)) (numₘ(0)) (numₘ(ObjectNumeralSyntax.value number) : Code)) := by
  rw [numeral_apply]
  exact ObjectNumeralSyntax.positive S.certificate S.sequences S.power S.infinity number

theorem numeral_negative {T : SetTheory} (S : Support T) (number output : Nat) (h : ObjectNumeralSyntax.value number ≠ output) :
    Derives T [] (¬ₘ numeral (numₘ(number)) (numₘ(0)) (numₘ(output) : Code)) := by
  rw [numeral_apply]
  exact ObjectNumeralSyntax.negative S.certificate S.sequences.toArithmeticSupport number output h

theorem substitution_positive {parameters : SetContext} {T : SetTheory} (S : Support T) (body : ParameterFormula_m parameters) (number : Nat) :
    Derives T [] (substitution (parameters := parameters) (numₘ(code body)) (numₘ(ObjectNumeralSyntax.value number)) (numₘ(value body number) : Code)) := by
  rw [substitution_apply]
  change Derives T [] (ObjectHorn.condition ObjectSyntaxTransform.rules _)
  have h := ObjectSyntaxTransform.positive S.certificate S.sequences S.power S.infinity _ _ _ _ _
    ((substitution_checked body number _).mpr rfl)
  exact ObjectHorn.transport ObjectSyntaxTransform.rules
    (substitution_row_m (parameters := parameters) S.certificate (code body) (ObjectNumeralSyntax.value number) (value body number)) h

theorem substitution_negative {parameters : SetContext} {T : SetTheory} (S : Support T) (body : ParameterFormula_m parameters) (number output : Nat)
    (h : value body number ≠ output) :
    Derives T [] (¬ₘ substitution (parameters := parameters) (numₘ(code body)) (numₘ(ObjectNumeralSyntax.value number)) (numₘ(output) : Code)) := by
  rw [substitution_apply]
  change Derives T [] (¬ₘ ObjectHorn.condition ObjectSyntaxTransform.rules _)
  have hCheck : ObjectSyntaxTransform.checked 3 0 (listValue (ObjectNumeralSyntax.value number :: parameterCodes_m parameters)) (code body) output = false :=
    Bool.eq_false_iff.mpr (fun hTrue => h ((substitution_checked body number output).mp hTrue))
  have h := ObjectSyntaxTransform.negative S.certificate S.sequences.toArithmeticSupport _ _ _ _ _ hCheck
  exact ObjectHorn.transport_negative ObjectSyntaxTransform.rules
    (substitution_row_m (parameters := parameters) S.certificate (code body) (ObjectNumeralSyntax.value number) output) h

end YesMetaZFC.Automation.ObjectDiagonal
