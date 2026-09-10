import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalQuotationEvaluation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralOrderReflection

/-! # 复合自然数项上等式与成员判断的双向反射

对子项选择合法数码，以已完成的等式／严格序反射判定数值，再特化源同余定理。
正负方向共用同一构造，参数和中间值允许是模型内部的非标准自然数。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxHeartbeats 100000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def FormulaReflects {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set)
    (body : SetOpenFormula free) : Prop :=
  (body.satisfies env → ProvableCode 𝒩 (formula 𝒩 values body)) ∧
  (¬ body.satisfies env → ProvableCode 𝒩 (formula 𝒩 values (.neg body)))

def polarity {bound free : SetContext} (positive : Bool) (body : SetFormula bound free) : SetFormula bound free :=
  if positive then body else .neg body

def atomicBody {bound free : SetContext} (membership : Bool) (left right : SetTerm bound free) : SetFormula bound free :=
  if membership then left ∈ₘ right else left ≐ₘ right

def liftTwo {free : SetContext} (input : SetOpenTerm free) : SetOpenTerm (.set :: .set :: free) :=
  (input.weakenFree SetSort.set).weakenFree SetSort.set

theorem liftTwo_code {free : SetContext} (values : Nat → 𝒩.Carrier .set)
    (first second : 𝒩.Carrier .set) (input : SetOpenTerm free) :
    term 𝒩 (ObjectCodeInstantiation.prepend second (ObjectCodeInstantiation.prepend first values)) (liftTwo input) =
      term 𝒩 values input := by
  simp only [liftTwo, term, ObjectCodeInstantiation.term_weakenFree]

def atomicLeft {free : SetContext} (left : SetOpenTerm free) : SetOpenFormula (.set :: .set :: free) :=
  liftTwo left ≐ₘ (.fvar (.there .here))
def atomicRight {free : SetContext} (right : SetOpenTerm free) : SetOpenFormula (.set :: .set :: free) :=
  liftTwo right ≐ₘ (.fvar .here)
def atomicPremise {free : SetContext} (membership positive : Bool) : SetOpenFormula (.set :: .set :: free) :=
  polarity positive (atomicBody membership (.fvar (.there .here)) (.fvar .here))
def atomicResult {free : SetContext} (membership positive : Bool) (left right : SetOpenTerm free) : SetOpenFormula (.set :: .set :: free) :=
  polarity positive (atomicBody membership (liftTwo left) (liftTwo right))

theorem atomic_transport_derives {free : SetContext} (membership positive : Bool) (left right : SetOpenTerm free) :
    Derives intrinsic_zfc_theory [] (.imp (atomicLeft left) (.imp (atomicRight right)
      (.imp (atomicPremise membership positive) (atomicResult membership positive left right)))) := by
  apply source_complete
  intro 𝒩 _ env
  cases membership <;> cases positive <;>
    simp only [atomicLeft, atomicRight, atomicPremise, atomicResult, atomicBody, polarity, Bool.false_eq_true, if_false, if_true, Formula.satisfies, Arguments.eval]
  all_goals intro hl hr h; simpa only [hl, hr] using h

theorem atomic_code {free : SetContext} (values : Nat → 𝒩.Carrier .set)
    (membership positive : Bool) (left right : SetOpenTerm free) :
    formula 𝒩 values (polarity positive (atomicBody membership left right)) =
      (if positive then id else fun code => node 𝒩 4 [code])
        (if membership then node 𝒩 2 [(node 𝒩 RelationSymbol.membership.ctorIdx []), term 𝒩 values left, term 𝒩 values right]
          else node 𝒩 3 [term 𝒩 values left, term 𝒩 values right]) := by
  cases membership <;> cases positive <;> rfl

theorem atomic_transport (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (membership positive : Bool) (left right : SetOpenTerm free)
    (hl : TermEvaluates env values left) (hr : TermEvaluates env values right)
    {first second : 𝒩.Carrier .set} (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 (left.eval env) first)
    (hSecond : PureSourceNumeralSyntax.Graph 𝒩 (right.eval env) second)
    (hp : ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second))
      (polarity positive (atomicBody membership (.fvar .here) (.fvar (.there .here)) : SetOpenFormula [.set,.set])))) :
    ProvableCode 𝒩 (formula 𝒩 values (polarity positive (atomicBody membership left right))) := by
  let extended := ObjectCodeInstantiation.prepend second (ObjectCodeInstantiation.prepend first values)
  have he := numeralValues_prepend (numeralValues_prepend hv hl.1 hf hFirst) hr.1 hs hSecond
  have hL : formula 𝒩 extended (atomicLeft left) = termEqualityCode 𝒩 values left first := by
    change node 𝒩 3 [term 𝒩 extended (liftTwo left), first] = _
    rw [liftTwo_code]; rfl
  have hR : formula 𝒩 extended (atomicRight right) = termEqualityCode 𝒩 values right second := by
    change node 𝒩 3 [term 𝒩 extended (liftTwo right), second] = _
    rw [liftTwo_code]; rfl
  have hP : formula 𝒩 extended (atomicPremise (free := free) membership positive) =
      formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second))
        (polarity positive (atomicBody membership (.fvar .here) (.fvar (.there .here)) : SetOpenFormula [.set,.set])) := by
    simp only [atomicPremise, atomic_code]; rfl
  have hC : formula 𝒩 extended (atomicResult membership positive left right) =
      formula 𝒩 values (polarity positive (atomicBody membership left right)) := by
    simp only [atomicResult, atomic_code, extended, liftTwo_code]
  have h := values_modus_ponens (values := extended) h𝒩 (atomicPremise membership positive) _ he (hP.symm ▸ hp)
    (values_modus_ponens (values := extended) h𝒩 (atomicRight right) _ he (hR.symm ▸ hr.2 second hs hSecond)
      (values_modus_ponens (values := extended) h𝒩 (atomicLeft left) _ he (hL.symm ▸ hl.2 first hf hFirst)
        (specialize_values h𝒩 _ (atomic_transport_derives membership positive left right) he)))
  rwa [hC] at h

/-- 等式与成员原子共享子项求值和同余传输，包含各自的否定方向。 -/
theorem atomic_reflection (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (membership : Bool) {left right : SetOpenTerm free}
    (hl : TermEvaluates env values left) (hr : TermEvaluates env values right) :
    FormulaReflects env values (atomicBody membership left right) := by
  obtain ⟨first, hf, hFirst⟩ := PureSourceNumeralSyntax.total h𝒩 hl.1
  obtain ⟨second, hs, hSecond⟩ := PureSourceNumeralSyntax.total h𝒩 hr.1
  have transfer := atomic_transport h𝒩 env values hv membership
  cases membership with
  | false =>
    constructor
    · intro h
      exact transfer true left right hl hr hf hs hFirst hSecond (equal h𝒩 hl.1 hf hs hFirst hSecond h)
    · intro h
      exact transfer false left right hl hr hf hs hFirst hSecond (unequal h𝒩 hl.1 hr.1 hf hs hFirst hSecond h)
  | true =>
    have hOrder := order h𝒩 hl.1 hr.1 hf hs hFirst hSecond
    exact ⟨fun h => transfer true left right hl hr hf hs hFirst hSecond (hOrder.1 h),
      fun h => transfer false left right hl hr hf hs hFirst hSecond (hOrder.2 h)⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
