import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalPositiveFormula
import YesMetaZFC.Automation.ObjectPositiveBinder

/-! # 任意有限有界见证块的内部正反射

实际存在量词依次以内部数码见证引入，不使用图的否定反射。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalPositiveFormula
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity
open ReducedProofCodeSemantics InternalNumeralProof InternalNumeralReflection
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {bound free : SetContext}

theorem weaken_evaluation {env : Env 𝒩 [] free} {values : Nat → 𝒩.Carrier SetSort.set}
    {input : SetOpenTerm free} (he : TermEvaluates env values input) (value named : 𝒩.Carrier SetSort.set) :
    TermEvaluates (env.pushFree value) (ObjectCodeInstantiation.prepend named values) (input.weakenFree SetSort.set) := by
  simpa only [TermEvaluates, Term.eval_weakenFree, termEqualityCode, term, ObjectCodeInstantiation.term_weakenFree] using he

theorem embedBoundClosed (target : SetContext) {input : SetOpenTerm free} (hi : Evaluates 𝒩 input) :
    Evaluates 𝒩 (input.embedBoundClosed target) := by
  intro ctx env values hv bs fs _ hf
  rw [Term.embedBoundClosed_substituteMapped]
  exact hi env values hv VariableSubstitution.empty fs (fun entry => nomatch entry) hf

/-- 量词前后的正文通过规范打开等式连接，不复制不同元数的 binder 展开。 -/
theorem boundedExists (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {limit : SetTerm bound free} {body : SetFormula (SetSort.set :: bound) free}
    (hl : Evaluates 𝒩 limit) (hb : Positive 𝒩 body) :
    Positive 𝒩 (Formula.LevyBound.boundedExists set_levy_bound limit body) := by
  intro target env values hv bs fs hbs hfs ht
  let inner : SetFormula [SetSort.set] target := body.substituteMapped (VariableSubstitution.liftBound SetSort.set bs) (VariableSubstitution.weakenBound SetSort.set fs)
  let boundTerm := limit.substituteMapped bs fs
  have he := hl env values hv bs fs hbs hfs
  simp only [Formula.LevyBound.boundedExists, Formula.substituteMapped,
    Formula.LevyBound.membership_substituteMapped, Term.substituteMapped_weakenBound] at ht ⊢
  simp only [Formula.satisfies, Formula.LevyBound.satisfies_membership, Term.eval_weakenBound] at ht
  change ∃ input, mem 𝒩 input (boundTerm.eval env) ∧ inner.satisfies (env.pushBound input) at ht
  obtain ⟨input, hi, ht⟩ := ht
  have hn := member_natural h𝒩 he.1 hi
  obtain ⟨named, hNamed, hGraph⟩ := PureSourceNumeralSyntax.total h𝒩 hn
  have hExt := numeralValues_prepend hv hn hNamed hGraph
  have hVar := variable_evaluation h𝒩 (env.pushFree input) _ hExt .here hn hGraph
  have hLimit := weaken_evaluation he input named
  have hBody : ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend named values) (Formula.openBoundTop (σ := signature) SetSort.set inner)) := by
    have hTruth : (Formula.openBoundTop (σ := signature) SetSort.set inner).satisfies (env.pushFree input) := by
      have hs := Formula.satisfies_abstractFreeTop env input (Formula.openBoundTop (σ := signature) SetSort.set inner)
      rw [Formula.abstractFreeTop_openBoundTop] at hs
      exact hs.mp ht
    rw [show Formula.openBoundTop (σ := signature) SetSort.set inner = _ from ObjectPositiveBinder.open_substitute body bs fs] at hTruth ⊢
    apply hb (env.pushFree input) _ hExt _ _ ?_ ?_ hTruth
    · intro entry
      cases entry with
      | here => exact hVar
      | there entry => exact weaken_evaluation (hbs entry) input named
    · intro entry
      exact weaken_evaluation (hfs entry) input named
  let opened : SetOpenFormula (SetSort.set :: target) := (.fvar .here ∈ₘ boundTerm.weakenFree SetSort.set) ∧ₘ Formula.openBoundTop (σ := signature) SetSort.set inner
  have hGuard : ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend named values)
      (.fvar .here ∈ₘ boundTerm.weakenFree SetSort.set)) :=
    (atomic_reflection h𝒩 (env.pushFree input) _ hExt true hVar hLimit).1 (by
      change mem 𝒩 input ((boundTerm.weakenFree SetSort.set).eval (env.pushFree input))
      simpa only [Term.eval_weakenFree] using hi)
  have hp : ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend named values) opened) :=
    values_modus_ponens (values := ObjectCodeInstantiation.prepend named values) h𝒩 _ _ hExt hBody
      (reflection_rule h𝒩 _ hExt (boolean_rule_derives .conj true true _ _) hGuard)
  have hExists := exists_values h𝒩 opened values hv hn hNamed hGraph hp
  have hOpened : opened = Formula.openBoundTop (σ := signature) SetSort.set ((.bvar .here ∈ₘ boundTerm.weakenBound SetSort.set) ∧ₘ inner) := by
    change (.fvar .here ∈ₘ boundTerm.weakenFree SetSort.set) ∧ₘ Formula.openBoundTop (σ := signature) SetSort.set inner =
      (.fvar .here ∈ₘ Term.openBoundTop (σ := signature) SetSort.set (boundTerm.weakenBound SetSort.set)) ∧ₘ Formula.openBoundTop (σ := signature) SetSort.set inner
    rw [Term.openBoundTop_weakenBound]
  rw [hOpened, Formula.existsFreeTop_openBoundTop] at hExists
  exact hExists

theorem quantify (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (count : Nat) {limit : SetOpenTerm free}
    {body : SetFormula (QuineEncoding.project_bound_context count) free}
    (hl : Evaluates 𝒩 limit) (hb : Positive 𝒩 body) : Positive 𝒩 (ObjectHorn.quantify count limit body) := by
  induction count with
  | zero => exact hb
  | succ count ih => exact ih (boundedExists h𝒩 (embedBoundClosed _ hl) hb)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalPositiveFormula
