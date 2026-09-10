import YesMetaZFC.Automation.ObjectNumeralTraceReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalPredicateTransport

/-! # 数码递归图的内部零规则与后继规则

源规则由任意内部轨迹的合并与插入证明，再特化为模型内部数码实例。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity
open ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation RelationalTranslation
open ObjectNumeralTraceReflection (template nextTerm)
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem nextTerm_eval {bound free : SetContext} (env : Env 𝒩 bound free) (output : SetTerm bound free) :
    (nextTerm output).eval env = PureSourceNumeralSyntax.next 𝒩 (output.eval env) := by
  simp only [nextTerm, node_eval, List.map_cons, List.map_nil, numeral_eval]
  rfl

theorem nextTerm_evaluation (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {output : SetOpenTerm free} (ho : TermEvaluates env values output) : TermEvaluates env values (nextTerm output) := by
  apply node_term_evaluation h𝒩 env values hv 2
  intro field hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact numeral_term_evaluation h𝒩 env values hv _
  · obtain rfl := List.mem_singleton.mp hf
    exact ho

theorem numeral_trace_zero_derives : Derives intrinsic_zfc_theory []
    (template ∅ₘ (numₘ(ObjectNumeralSyntax.zeroCode)) : SetSentence) := by
  apply source_complete
  intro 𝒩 h𝒩 env
  rw [ObjectNumeralTraceReflection.template_apply, PureSourceNumeralSyntax.satisfies, numeral_eval]
  exact PureSourceNumeralSyntax.zero h𝒩

def numeralTraceStep : SetOpenFormula [.set,.set] :=
  template (Sₘ(.fvar .here)) (nextTerm (.fvar (.there .here)))

theorem numeral_trace_step_derives : Derives intrinsic_zfc_theory []
    (.imp ((naturalBody : SetOpenFormula [.set]).weakenFree SetSort.set)
      (.imp (firstNaturalBody : SetOpenFormula [.set,.set]) (.imp template.body numeralTraceStep))) := by
  apply source_complete
  intro 𝒩 h𝒩 env
  change mem 𝒩 (env.freeVal (.there .here)) (w 𝒩) → mem 𝒩 (env.freeVal .here) (w 𝒩) → _
  intro ho hi hg
  have hg := (PureSourceNumeralSyntax.satisfies env (.fvar .here) (.fvar (.there .here))).mp hg
  rw [numeralTraceStep, ObjectNumeralTraceReflection.template_apply, PureSourceNumeralSyntax.satisfies, nextTerm_eval]
  exact PureSourceNumeralSyntax.successor h𝒩 hi ho hg

theorem numeral_trace_zero (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {first second : 𝒩.Carrier .set} (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 (z 𝒩) first)
    (hSecond : PureSourceNumeralSyntax.Graph 𝒩 (numeral 𝒩 ObjectNumeralSyntax.zeroCode) second) :
    ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) template.body) := by
  let values : Nat → 𝒩.Carrier .set := fun _ => first
  have hv : NumeralValues 𝒩 values := fun _ => ⟨hf, z 𝒩, (omega_closed h𝒩).1, hFirst⟩
  have hSecond' : PureSourceNumeralSyntax.Graph 𝒩
      ((numₘ(ObjectNumeralSyntax.zeroCode) : SetOpenTerm []).eval (Env.empty : Env 𝒩 [] [])) second := by
    rw [numeral_eval]
    exact hSecond
  exact predicate_transport h𝒩 Env.empty values hv true template true ∅ₘ (numₘ(ObjectNumeralSyntax.zeroCode))
    (zero_evaluation h𝒩 Env.empty values hv) (numeral_term_evaluation h𝒩 Env.empty values hv _)
    hf hs hFirst hSecond' (specialize_values h𝒩 _ numeral_trace_zero_derives hv)

theorem numeral_trace_step (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input output first second result named : 𝒩.Carrier .set}
    (hi : mem 𝒩 input (w 𝒩)) (ho : mem 𝒩 output (w 𝒩))
    (hf : mem 𝒩 first (w 𝒩)) (hs : mem 𝒩 second (w 𝒩))
    (hFirst : PureSourceNumeralSyntax.Graph 𝒩 input first) (hSecond : PureSourceNumeralSyntax.Graph 𝒩 output second)
    (hr : mem 𝒩 result (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hResult : PureSourceNumeralSyntax.Graph 𝒩 (suc 𝒩 input) result)
    (hNamed : PureSourceNumeralSyntax.Graph 𝒩 (PureSourceNumeralSyntax.next 𝒩 output) named)
    (hp : ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend first (fun _ => second)) template.body)) :
    ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend result (fun _ => named)) template.body) := by
  let values := ObjectCodeInstantiation.prepend first (fun _ => second)
  let env : Env 𝒩 [] [.set,.set] := templateEnv (.cons input (.cons output .nil))
  have hv : NumeralValues 𝒩 values := numeralValues_prepend
    (fun _ => ⟨hs, output, ho, hSecond⟩) hi hf hFirst
  have hLeft := variable_evaluation h𝒩 env values hv .here hi hFirst
  have hRight := variable_evaluation h𝒩 env values hv (.there .here) ho hSecond
  have hNatural : ProvableCode 𝒩 (formula 𝒩 values ((naturalBody : SetOpenFormula [.set]).weakenFree SetSort.set)) := by
    rw [PureSourceInstantiation.formula, ObjectCodeInstantiation.formula_weakenFree]
    exact natural h𝒩 ho hs hSecond
  have hStep := values_modus_ponens (values := values) h𝒩 template.body numeralTraceStep hv hp
    (values_modus_ponens (values := values) h𝒩 firstNaturalBody _ hv (natural h𝒩 hi hf hFirst)
      (values_modus_ponens (values := values) h𝒩 _ _ hv hNatural
        (specialize_values h𝒩 _ numeral_trace_step_derives hv)))
  apply predicate_transport h𝒩 env values hv true template true _ _
    (successor_term_evaluation h𝒩 env values hv hLeft) (nextTerm_evaluation h𝒩 env values hv hRight)
    hr hn hResult ?_ hStep
  rwa [nextTerm_eval]

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
