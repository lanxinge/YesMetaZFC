import YesMetaZFC.Automation.ObjectCheckedReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalPositiveQueries
import YesMetaZFC.Model.ZFC.Pure.PureSourceCheckedConstruction

/-! # 已检查规则的内部证明装配

实际局部查询的真值由正反射变成证明，前提轨迹按原规则合并。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity
open PureSourceTraceComposition ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation RelationalTranslation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxHeartbeats 400000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
attribute [local irreducible] InternalPositiveFormula.Positive InternalPositiveFormula.Evaluates
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {free : SetContext}

def CheckedProv (𝒩 : Structure.{0,0,0,x} signature) (rules : List ObjectHorn.Rule)
    (localCondition : FormulaTemplate.Unary) (root : 𝒩.Carrier .set) : Prop :=
  ∀ named, mem 𝒩 named (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 root named →
    ProvableCode 𝒩 (formula 𝒩 (fun _ => named) (ObjectCheckedReflection.template rules localCondition).body)

theorem checked_satisfies {bound : SetContext} (env : Env 𝒩 bound free) (rules : List ObjectHorn.Rule)
    (localCondition : FormulaTemplate.Unary) (root : SetTerm bound free) :
    (ObjectCheckedTrace.condition rules localCondition root).satisfies env ↔ Witness (ObjectCheckedTrace.step rules localCondition) (root.eval env) := by
  rw [ObjectCheckedTrace.condition, ObjectTrace.condition_satisfies]
  rfl

theorem checkedAt_satisfies {bound : SetContext} (env : Env 𝒩 bound free) (rules : List ObjectHorn.Rule)
    (localCondition : FormulaTemplate.Unary) (root : SetTerm bound free) :
    (ObjectCheckedReflection.atRow ReducedProofPresentation.presentation.graph rules localCondition root).satisfies env ↔
      CheckedProv 𝒩 rules localCondition (root.eval env) := by
  simp only [ObjectCheckedReflection.atRow, forallNumeral_satisfies, provableCode_satisfies, formula_eval]
  rfl

theorem checked_term_transfer (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (rules : List ObjectHorn.Rule)
    (localCondition : FormulaTemplate.Unary) (root : SetOpenTerm free) (hr : TermEvaluates env values root) :
    ProvableCode 𝒩 (formula 𝒩 values (ObjectCheckedTrace.condition rules localCondition root)) ↔
      CheckedProv 𝒩 rules localCondition (root.eval env) := by
  have hc (named : 𝒩.Carrier .set) : ObjectCodeInstantiation.prepend named (fun _ => named) = (fun _ => named) := by
    funext i; cases i <;> rfl
  constructor
  · intro hp named hn hg
    have h := predicate_transport h𝒩 env values hv true (ObjectCheckedReflection.template rules localCondition) true root root hr hr hn hn hg hg
      (by simpa only [polarity, if_true, ObjectCheckedReflection.template_apply] using! hp)
    simpa only [polarity, if_true, hc] using! h
  · intro hp
    obtain ⟨named, hn, hg⟩ := PureSourceNumeralSyntax.total h𝒩 hr.1
    have h := predicate_transport h𝒩 env values hv false (ObjectCheckedReflection.template rules localCondition) true root root hr hr hn hn hg hg
      (by simpa only [polarity, if_true, hc] using! hp named hn hg)
    simpa only [polarity, if_true, ObjectCheckedReflection.template_apply] using! h

theorem checked_rule_bounded_derives (rules : List ObjectHorn.Rule) (localCondition : FormulaTemplate.Unary)
    (rule : ObjectHorn.Rule) (hRule : rule ∈ rules)
    (inputs : Fin rule.arity → SetOpenTerm free) :
    Derives intrinsic_zfc_theory []
      (ObjectHornReflection.naturals inputs ⟶ₘ ObjectHornReflection.bounds rule inputs ⟶ₘ
        ObjectHornReflection.guards rule inputs ⟶ₘ localCondition (rule.head.term inputs) ⟶ₘ
        ObjectCheckedReflection.premises rules localCondition rule inputs ⟶ₘ
        ObjectCheckedTrace.condition rules localCondition (rule.head.term inputs)) := by
  apply source_complete
  intro 𝒩 h𝒩 env hNatural hBound hGuard hLocal hPremise
  have hNat := (ObjectHornSemantics.allOf_satisfies _ _).mp hNatural
  have hBounds := (ObjectHornSemantics.allOf_satisfies _ _).mp hBound
  have hGuards := (ObjectHornSemantics.allOf_satisfies _ _).mp hGuard
  have hPremises := (ObjectHornSemantics.allOf_satisfies _ _).mp hPremise
  rw [checked_satisfies, ObjectHornSemantics.expr_eval]
  apply PureSourceCheckedConstruction.rule_intro_bounds h𝒩 rules localCondition rule hRule (fun i => (inputs i).eval env)
    (fun i => hNat _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
    (fun i => by
      have h := hBounds _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
      change mem 𝒩 ((inputs i).eval env) (suc 𝒩 ((rule.head.term inputs).eval env)) at h
      rwa [ObjectHornSemantics.expr_eval] at h)
  · intro guard hg
    have h := hGuards _ (List.mem_map.mpr ⟨guard, hg, rfl⟩)
    simpa only [membership_satisfies, ObjectHornSemantics.expr_eval] using! h
  · simpa only [NaturalRosserSemantics.unary_satisfies, ObjectHornSemantics.expr_eval] using! hLocal
  · intro premise hp
    have h := hPremises _ (List.mem_map.mpr ⟨premise, hp, rfl⟩)
    simpa only [checked_satisfies, ObjectHornSemantics.expr_eval] using! h

theorem checked_rule_bounded_terms (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (rules : List ObjectHorn.Rule) (localCondition : FormulaTemplate.Unary)
    (hPositive : InternalPositiveFormula.Positive 𝒩 localCondition.body)
    (rule : ObjectHorn.Rule) (hRule : rule ∈ rules)
    (inputs : Fin rule.arity → SetOpenTerm free)
    (hInputs : ∀ i, TermEvaluates env values (inputs i))
    (hBounds : ∀ i, mem 𝒩 ((inputs i).eval env) (suc 𝒩 ((rule.head.term inputs).eval env)))
    (hGuards : ∀ guard ∈ rule.guards, mem 𝒩 ((guard.1.term inputs).eval env) ((guard.2.term inputs).eval env))
    (hLocal : (localCondition (rule.head.term inputs)).satisfies env)
    (hPremises : ∀ premise ∈ rule.premises, CheckedProv 𝒩 rules localCondition ((premise.term inputs).eval env)) :
    CheckedProv 𝒩 rules localCondition ((rule.head.term inputs).eval env) := by
  have hNatural := allOf_values h𝒩 values hv (List.ofFn (fun i => inputs i ∈ₘ ωₘ)) (by
    intro body hb; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact natural_term_proof h𝒩 env values hv (hInputs i))
  have hBound := allOf_values h𝒩 values hv (List.ofFn (fun i => inputs i ∈ₘ Sₘ(rule.head.term inputs))) (by
    intro body hb; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact (atomic_reflection h𝒩 env values hv true (hInputs i)
      (successor_term_evaluation h𝒩 env values hv
        (horn_expr_evaluation h𝒩 env values hv inputs hInputs rule.head))).1 (hBounds i))
  have hGuard := allOf_values h𝒩 values hv (rule.guards.map (fun g => g.1.term inputs ∈ₘ g.2.term inputs)) (by
    intro body hb; obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
    exact (atomic_reflection h𝒩 env values hv true
      (horn_expr_evaluation h𝒩 env values hv inputs hInputs g.1)
      (horn_expr_evaluation h𝒩 env values hv inputs hInputs g.2)).1 (hGuards g hg))
  have hQuery := InternalPositiveFormula.unary_terms localCondition hPositive env values hv
    (horn_expr_evaluation h𝒩 env values hv inputs hInputs rule.head) hLocal
  have hPremise := allOf_values h𝒩 values hv (rule.premises.map (fun p => ObjectCheckedTrace.condition rules localCondition (p.term inputs))) (by
    intro body hb; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact (checked_term_transfer h𝒩 env values hv rules localCondition _
      (horn_expr_evaluation h𝒩 env values hv inputs hInputs p)).mpr (hPremises p hp))
  have h := specialize_values h𝒩 _ (checked_rule_bounded_derives rules localCondition rule hRule inputs) hv
  have h := values_modus_ponens (values := values) h𝒩 _ _ hv hNatural h
  have h := values_modus_ponens (values := values) h𝒩 _ _ hv hBound h
  have h := values_modus_ponens (values := values) h𝒩 _ _ hv hGuard h
  have h := values_modus_ponens (values := values) h𝒩 _ _ hv hQuery h
  exact (checked_term_transfer h𝒩 env values hv rules localCondition _
    (horn_expr_evaluation h𝒩 env values hv inputs hInputs rule.head)).mp
      (values_modus_ponens (values := values) h𝒩 _ _ hv hPremise h)

/-- 固定规则的全部参数由公共数码总性命名，局部条件和前提在同一环境中装配。 -/

theorem checked_rule_bounded_values (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) (localCondition : FormulaTemplate.Unary)
    (hPositive : InternalPositiveFormula.Positive 𝒩 localCondition.body)
    (rule : ObjectHorn.Rule) (hRule : rule ∈ rules)
    (values : Fin rule.arity → 𝒩.Carrier .set)
    (hv : ∀ i, mem 𝒩 (values i) (w 𝒩))
    (hBounds : ∀ i, mem 𝒩 (values i) (suc 𝒩 (ObjectHornSemantics.exprValue 𝒩 values rule.head)))
    (hg : ∀ guard ∈ rule.guards, mem 𝒩 (ObjectHornSemantics.exprValue 𝒩 values guard.1)
      (ObjectHornSemantics.exprValue 𝒩 values guard.2))
    (hLocal : localCondition.body.satisfies (templateEnv (.cons (ObjectHornSemantics.exprValue 𝒩 values rule.head) .nil)))
    (hp : ∀ premise ∈ rule.premises, CheckedProv 𝒩 rules localCondition (ObjectHornSemantics.exprValue 𝒩 values premise)) :
    CheckedProv 𝒩 rules localCondition (ObjectHornSemantics.exprValue 𝒩 values rule.head) := by
  classical
  let actual (i : Nat) := if h : i < rule.arity then values ⟨i, h⟩ else z 𝒩
  have ha i : mem 𝒩 (actual i) (w 𝒩) := by
    dsimp only [actual]
    split
    · exact hv _
    · exact (omega_closed h𝒩).1
  let names i := Classical.choose (PureSourceNumeralSyntax.total h𝒩 (ha i))
  have hn i := Classical.choose_spec (PureSourceNumeralSyntax.total h𝒩 (ha i))
  have hNames : NumeralValues 𝒩 names := fun i => ⟨(hn i).1, actual i, ha i, (hn i).2⟩
  let env : Env 𝒩 [] (QuineEncoding.project_bound_context rule.arity) :=
    ⟨(fun {_} entry => nomatch entry), (fun {_} entry => actual entry.index)⟩
  let inputs (i : Fin rule.arity) : SetOpenTerm (QuineEncoding.project_bound_context rule.arity) :=
    .fvar (QuineEncoding.project_bound_variable i)
  have he i : (inputs i).eval env = values i := by
    change actual (QuineEncoding.project_bound_variable i).index = values i
    rw [KernelQuotation.bound_index]
    exact dif_pos i.isLt
  have hInputs i : TermEvaluates env names (inputs i) :=
    variable_evaluation h𝒩 env names hNames (QuineEncoding.project_bound_variable i)
      (ha _) (hn _).2
  have hExpr (expr : ObjectHorn.Expr rule.arity) :
      (expr.term inputs).eval env = ObjectHornSemantics.exprValue 𝒩 values expr := by
    rw [ObjectHornSemantics.expr_eval]
    exact congrArg (fun v => ObjectHornSemantics.exprValue 𝒩 v expr) (funext he)
  have h := checked_rule_bounded_terms h𝒩 env names hNames rules localCondition hPositive rule hRule inputs hInputs
    (fun i => by rw [he, hExpr]; exact hBounds i)
    (fun guard hGuard => by rw [hExpr, hExpr]; exact hg guard hGuard)
    (by rw [NaturalRosserSemantics.unary_satisfies, hExpr]; exact hLocal)
    (fun premise hPremise => by rw [hExpr]; exact hp premise hPremise)
  rwa [hExpr] at h

theorem checkedProv_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) (localCondition : FormulaTemplate.Unary)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩)) :
    CheckedProv 𝒩 rules localCondition root ↔ CheckedProv (PureSourceNumerals.canonical h𝒩) rules localCondition root := by
  unfold CheckedProv
  apply forall_congr'; intro named
  change (mem 𝒩 named (w 𝒩) → _) ↔ (mem 𝒩 named (w (PureSourceNumerals.canonical h𝒩)) → _)
  rw [← omega_agrees h𝒩]
  apply imp_congr_right; intro hn
  apply imp_congr (PureSourceNumeralSyntax.agrees h𝒩 hr hn)
  exact instance_provability_agrees h𝒩 (fun _ => hn) rfl _

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
