import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralTraceReflection

/-! # 数码图的负反射与复合项接口

负方向用原图的内部总性和唯一性：构造正确输出的图证明，再用不等式排除候选。
不需要枚举被拒绝的轨迹，也不假定内部数码在外部有限。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
open ObjectNumeralTraceReflection (template)
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxHeartbeats 300000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def traceInput : SetOpenTerm [.set,.set,.set] := .fvar .here
def traceCandidate : SetOpenTerm [.set,.set,.set] := .fvar (.there .here)
def traceOutput : SetOpenTerm [.set,.set,.set] := .fvar (.there (.there .here))
def traceKnown : SetOpenFormula [.set,.set,.set] := template traceInput traceOutput
def traceRejected : SetOpenFormula [.set,.set,.set] := .neg (template traceInput traceCandidate)
def traceDifferent : SetOpenFormula [.set,.set,.set] := .neg (traceCandidate ≐ₘ traceOutput)

theorem numeral_trace_reject_derives : Derives intrinsic_zfc_theory []
    (.imp (traceInput ∈ₘ ωₘ) (.imp (traceCandidate ∈ₘ ωₘ) (.imp (traceOutput ∈ₘ ωₘ)
      (.imp traceKnown (.imp traceDifferent traceRejected))))) := by
  apply source_complete
  intro 𝒩 h𝒩 env
  change mem 𝒩 (traceInput.eval env) (w 𝒩) → mem 𝒩 (traceCandidate.eval env) (w 𝒩) →
    mem 𝒩 (traceOutput.eval env) (w 𝒩) → _
  intro hi hc ho hg hn hx
  have hg := (PureSourceNumeralSyntax.satisfies env traceInput traceOutput).mp
    ((ObjectNumeralTraceReflection.template_apply traceInput traceOutput) ▸ hg)
  have hx := (PureSourceNumeralSyntax.satisfies env traceInput traceCandidate).mp
    ((ObjectNumeralTraceReflection.template_apply traceInput traceCandidate) ▸ hx)
  exact hn (PureSourceNumeralSyntax.functional h𝒩 hi hc ho hx hg)

theorem numeral_trace_negative (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input output first second : 𝒩.Carrier .set}
    (hi : mem 𝒩 input (w 𝒩)) (ho : mem 𝒩 output (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 input first) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 output second)
    (hg : ¬ PureSourceNumeralSyntax.Graph 𝒩 input output) :
    ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) (.neg template.body)) := by
  obtain ⟨actual, ha, hActual⟩ := PureSourceNumeralSyntax.total h𝒩 hi
  obtain ⟨third, ht, hThird⟩ := PureSourceNumeralSyntax.total h𝒩 ha
  have hne : output ≠ actual := fun he => hg (he.symm ▸ hActual)
  let values := ObjectCodeInstantiation.prepend first (ObjectCodeInstantiation.prepend second (fun _ => third))
  have hv : NumeralValues 𝒩 values := numeralValues_prepend
    (numeralValues_prepend (fun _ => ⟨ht, actual, ha, hThird⟩) ho hs hSecond) hi hf hFirst
  have hk : formula 𝒩 values traceKnown =
      formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => third)) template.body :=
    ObjectCodeInstantiation.binary_template (node 𝒩) values template traceInput traceOutput
  have hKnown := hk.symm ▸ numeral_trace_positive h𝒩 hi ha hf ht hFirst hThird hActual
  have hDifferent : ProvableCode 𝒩 (formula 𝒩 values traceDifferent) :=
    unequal h𝒩 ho ha hs ht hSecond hThird hne
  have h := values_modus_ponens (values := values) h𝒩 traceDifferent traceRejected hv hDifferent
    (values_modus_ponens (values := values) h𝒩 traceKnown _ hv hKnown
      (values_modus_ponens (values := values) h𝒩 (traceOutput ∈ₘ ωₘ) _ hv (natural h𝒩 ha ht hThird)
        (values_modus_ponens (values := values) h𝒩 (traceCandidate ∈ₘ ωₘ) _ hv (natural h𝒩 ho hs hSecond)
          (values_modus_ponens (values := values) h𝒩 (traceInput ∈ₘ ωₘ) _ hv (natural h𝒩 hi hf hFirst)
            (specialize_values h𝒩 _ numeral_trace_reject_derives hv)))))
  have hc : formula 𝒩 values traceRejected =
      formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) (.neg template.body) := by
    change node 𝒩 4 [formula 𝒩 values (template traceInput traceCandidate)] = _
    rw [formula, ObjectCodeInstantiation.binary_template]
    rfl
  exact hc ▸ h

/-- 已求值的任意自然数项可直接进入原数码图，正负判断均生成内部证明。 -/
theorem numeral_trace_reflection (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {input output : SetOpenTerm free} (hi : TermEvaluates env values input) (ho : TermEvaluates env values output) :
    FormulaReflects env values (ObjectNumeralSyntax.condition input output) := by
  obtain ⟨first, hf, hFirst⟩ := PureSourceNumeralSyntax.total h𝒩 hi.1
  obtain ⟨second, hs, hSecond⟩ := PureSourceNumeralSyntax.total h𝒩 ho.1
  have transfer := predicate_transport h𝒩 env values hv false template
  rw [← ObjectNumeralTraceReflection.template_apply]
  constructor
  · intro hg
    have hg := (PureSourceNumeralSyntax.satisfies env input output).mp
      ((ObjectNumeralTraceReflection.template_apply input output) ▸ hg)
    exact transfer true input output hi ho hf hs hFirst hSecond
      (numeral_trace_positive h𝒩 hi.1 ho.1 hf hs hFirst hSecond hg)
  · intro hg
    have hg : ¬ PureSourceNumeralSyntax.Graph 𝒩 (input.eval env) (output.eval env) := by
      intro h
      apply hg
      rw [ObjectNumeralTraceReflection.template_apply]
      exact (PureSourceNumeralSyntax.satisfies env input output).mpr h
    exact transfer false input output hi ho hf hs hFirst hSecond
      (numeral_trace_negative h𝒩 hi.1 ho.1 hf hs hFirst hSecond hg)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
