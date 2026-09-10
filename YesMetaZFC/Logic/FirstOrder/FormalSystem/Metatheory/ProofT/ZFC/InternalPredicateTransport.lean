import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalBooleanReflection

/-! # 内部图谓词在复合项与数码之间的传输

模板可包含任意量词。项求值给出内部等式证明，类型化模板同余负责传输整个公式；
不展开具体图，也不要求模型对象来自标准自然数。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
set_option maxHeartbeats 100000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {free : SetContext}

def predicateTerms (template : FormulaTemplate.Binary) (positive : Bool)
    (left right : SetOpenTerm free) : SetOpenFormula (.set :: .set :: free) :=
  polarity positive (template (liftTwo left) (liftTwo right))

def predicateNames (template : FormulaTemplate.Binary) (positive : Bool) : SetOpenFormula (.set :: .set :: free) :=
  polarity positive (template (.fvar (.there .here)) (.fvar .here))

def transportFrom (toNames : Bool) (template : FormulaTemplate.Binary) (positive : Bool)
    (left right : SetOpenTerm free) : SetOpenFormula (.set :: .set :: free) :=
  if toNames then predicateTerms template positive left right else predicateNames template positive

def transportTo (toNames : Bool) (template : FormulaTemplate.Binary) (positive : Bool)
    (left right : SetOpenTerm free) : SetOpenFormula (.set :: .set :: free) :=
  transportFrom (!toNames) template positive left right

theorem predicate_transport_derives (toNames : Bool) (template : FormulaTemplate.Binary) (positive : Bool)
    (left right : SetOpenTerm free) :
    Derives intrinsic_zfc_theory [] (.imp (atomicLeft left) (.imp (atomicRight right)
      (.imp (transportFrom toNames template positive left right) (transportTo toNames template positive left right)))) := by
  apply source_complete
  intro 𝒩 _ env
  cases toNames <;> cases positive <;>
    simp only [atomicLeft, atomicRight, transportFrom, transportTo, predicateTerms, predicateNames,
      polarity, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true, Formula.satisfies,
      NaturalRosserSemantics.binary_satisfies]
  all_goals intro hl hr hp; simpa only [hl, hr] using hp

theorem predicate_terms_code (values : Nat → 𝒩.Carrier .set) (first second : 𝒩.Carrier .set)
    (template : FormulaTemplate.Binary) (positive : Bool) (left right : SetOpenTerm free) :
    formula 𝒩 (ObjectCodeInstantiation.prepend second (ObjectCodeInstantiation.prepend first values))
      (predicateTerms template positive left right) = formula 𝒩 values (polarity positive (template left right)) := by
  have ht (input : SetOpenTerm free) : ObjectCodeInstantiation.term (node 𝒩)
      (ObjectCodeInstantiation.prepend second (ObjectCodeInstantiation.prepend first values)) (liftTwo input) =
        ObjectCodeInstantiation.term (node 𝒩) values input := liftTwo_code values first second input
  cases positive <;> simp only [predicateTerms, polarity, Bool.false_eq_true, if_false, if_true,
    formula, ObjectCodeInstantiation.formula, ObjectCodeInstantiation.binary_template,
    ht]

theorem predicate_names_code (values : Nat → 𝒩.Carrier .set) (first second : 𝒩.Carrier .set)
    (template : FormulaTemplate.Binary) (positive : Bool) :
    formula 𝒩 (ObjectCodeInstantiation.prepend second (ObjectCodeInstantiation.prepend first values))
      (predicateNames (free := free) template positive) =
    formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) (polarity positive template.body) := by
  cases positive <;> simp only [predicateNames, polarity, Bool.false_eq_true, if_false, if_true,
    formula, ObjectCodeInstantiation.formula, ObjectCodeInstantiation.binary_template]
  all_goals rfl

/-- 两个方向以及正负公式共用同一同余证明。 -/
theorem predicate_transport (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (toNames : Bool) (template : FormulaTemplate.Binary) (positive : Bool) (left right : SetOpenTerm free)
    (hl : TermEvaluates env values left) (hr : TermEvaluates env values right)
    {first second : 𝒩.Carrier .set} (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 (left.eval env) first)
    (hSecond : PureSourceNumeralSyntax.Graph 𝒩 (right.eval env) second)
    (hp : ProvableCode 𝒩 (if toNames then formula 𝒩 values (polarity positive (template left right))
      else formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) (polarity positive template.body))) :
    ProvableCode 𝒩 (if toNames then
      formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) (polarity positive template.body)
      else formula 𝒩 values (polarity positive (template left right))) := by
  let extended := ObjectCodeInstantiation.prepend second (ObjectCodeInstantiation.prepend first values)
  have he := numeralValues_prepend (numeralValues_prepend hv hl.1 hf hFirst) hr.1 hs hSecond
  have hL : formula 𝒩 extended (atomicLeft left) = termEqualityCode 𝒩 values left first := by
    change node 𝒩 3 [term 𝒩 extended (liftTwo left), first] = _
    rw [liftTwo_code]; rfl
  have hR : formula 𝒩 extended (atomicRight right) = termEqualityCode 𝒩 values right second := by
    change node 𝒩 3 [term 𝒩 extended (liftTwo right), second] = _
    rw [liftTwo_code]; rfl
  have hPremise : ProvableCode 𝒩 (formula 𝒩 extended (transportFrom toNames template positive left right)) := by
    cases toNames <;> simpa only [transportFrom, Bool.false_eq_true, if_false, if_true, extended,
      predicate_terms_code, predicate_names_code] using! hp
  have h := values_modus_ponens (values := extended) h𝒩 (transportFrom toNames template positive left right) _ he hPremise
    (values_modus_ponens (values := extended) h𝒩 (atomicRight right) _ he (hR.symm ▸ hr.2 second hs hSecond)
      (values_modus_ponens (values := extended) h𝒩 (atomicLeft left) _ he (hL.symm ▸ hl.2 first hf hFirst)
        (specialize_values h𝒩 _ (predicate_transport_derives toNames template positive left right) he)))
  cases toNames <;> simpa only [transportTo, transportFrom, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    if_false, if_true, extended, predicate_terms_code, predicate_names_code] using! h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
