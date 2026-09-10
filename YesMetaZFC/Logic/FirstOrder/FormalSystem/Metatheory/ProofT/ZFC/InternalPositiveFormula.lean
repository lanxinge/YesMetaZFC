import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalHornReflection
import YesMetaZFC.Automation.ObjectArithmeticTerm

/-! # 保持实际模板替换的正反射组合

只消费正向图反射；自然数见证可为非标准值。任意槽位替换由公共 AST API 处理。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalPositiveFormula
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity
open ReducedProofCodeSemantics InternalNumeralProof InternalNumeralReflection PureSourceTraceComposition
open _root_.YesMetaZFC.Automation ObjectHornSemantics
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}
variable {bound free : SetContext}

def Evaluates (𝒩 : Structure.{0,0,0,x} signature) (input : SetTerm bound free) : Prop :=
  ∀ {target : SetContext} (env : Env 𝒩 [] target) (values : Nat → 𝒩.Carrier .set), NumeralValues 𝒩 values →
    ∀ (bs : VariableSubstitution signature bound [] target) (fs : VariableSubstitution signature free [] target),
      (∀ entry : Variable bound .set, TermEvaluates env values (bs entry)) →
      (∀ entry : Variable free .set, TermEvaluates env values (fs entry)) →
      TermEvaluates env values (input.substituteMapped bs fs)

def Positive (𝒩 : Structure.{0,0,0,x} signature) (body : SetFormula bound free) : Prop :=
  ∀ {target : SetContext} (env : Env 𝒩 [] target) (values : Nat → 𝒩.Carrier .set), NumeralValues 𝒩 values →
    ∀ (bs : VariableSubstitution signature bound [] target) (fs : VariableSubstitution signature free [] target),
      (∀ entry : Variable bound .set, TermEvaluates env values (bs entry)) →
      (∀ entry : Variable free .set, TermEvaluates env values (fs entry)) →
      (body.substituteMapped bs fs).satisfies env → ProvableCode 𝒩 (formula 𝒩 values (body.substituteMapped bs fs))

theorem bvar (entry : Variable bound .set) : Evaluates 𝒩 (.bvar entry : SetTerm bound free) :=
  fun _ _ _ _ _ hb _ => hb entry

theorem fvar (entry : Variable free .set) : Evaluates 𝒩 (.fvar entry : SetTerm bound free) :=
  fun _ _ _ _ _ _ hf => hf entry

variable (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
include h𝒩

theorem numeral (number : Nat) : Evaluates 𝒩 (numₘ(number) : SetTerm bound free) := by
  intro target env values hv bs fs _ _
  simpa only [finite_numeral_term_substituteMapped] using numeral_term_evaluation h𝒩 env values hv number

theorem successor {input : SetTerm bound free} (hi : Evaluates 𝒩 input) : Evaluates 𝒩 Sₘ(input) := by
  intro target env values hv bs fs hb hf
  exact successor_term_evaluation h𝒩 env values hv (hi env values hv bs fs hb hf)

theorem pairing {left right : SetTerm bound free} (hl : Evaluates 𝒩 left) (hr : Evaluates 𝒩 right) :
    Evaluates 𝒩 (godel_pairₘ(left, right)) := by
  intro target env values hv bs fs hb hf
  exact pairing_term_evaluation h𝒩 env values hv (hl env values hv bs fs hb hf) (hr env values hv bs fs hb hf)

theorem exponentiation {left right : SetTerm bound free} (hl : Evaluates 𝒩 left) (hr : Evaluates 𝒩 right) :
    Evaluates 𝒩 (left ^ₘ right) := by
  intro target env values hv bs fs hb hf
  exact arithmetic_term_evaluation h𝒩 env values hv .exponentiation (hl env values hv bs fs hb hf) (hr env values hv bs fs hb hf)

theorem shift (count : Nat) {input : SetTerm bound free} (hi : Evaluates 𝒩 input) :
    Evaluates 𝒩 (ObjectArithmeticTerm.shift count input) := by
  induction count with
  | zero => exact hi
  | succ count ih => exact successor h𝒩 ih

theorem tableBound {input : SetTerm bound free} (hi : Evaluates 𝒩 input) :
    Evaluates 𝒩 (ObjectArithmeticTerm.tableBound input) :=
  exponentiation h𝒩 (shift h𝒩 8 hi) (exponentiation h𝒩 (numeral h𝒩 16) (shift h𝒩 2 hi))

theorem expression {n : Nat} (expr : ObjectHorn.Expr n) (inputs : Fin n → SetTerm bound free)
    (hi : ∀ i, Evaluates 𝒩 (inputs i)) : Evaluates 𝒩 (expr.term inputs) := by
  intro target env values hv bs fs hb hf
  rw [ObjectHorn.Expr.term_substituteMapped]
  exact horn_expr_evaluation h𝒩 env values hv _ (fun i => hi i env values hv bs fs hb hf) expr

theorem fields {terms : List (SetTerm bound free)} (ht : ∀ t ∈ terms, Evaluates 𝒩 t) :
    Evaluates 𝒩 (structural_list_code_term terms) := by
  induction terms with
  | nil => exact successor h𝒩 (pairing h𝒩 (numeral h𝒩 0) (numeral h𝒩 0))
  | cons head tail ih =>
    exact successor h𝒩 (pairing h𝒩 (numeral h𝒩 1)
      (pairing h𝒩 (ht head List.mem_cons_self) (ih (fun t h => ht t (List.mem_cons_of_mem head h)))))

theorem node (tag : Nat) {terms : List (SetTerm bound free)} (ht : ∀ t ∈ terms, Evaluates 𝒩 t) :
    Evaluates 𝒩 (IntrinsicQuotation.node tag terms) :=
  successor h𝒩 (pairing h𝒩 (numeral h𝒩 tag) (fields h𝒩 ht))

theorem equal {left right : SetTerm bound free} (hl : Evaluates 𝒩 left) (hr : Evaluates 𝒩 right) :
    Positive 𝒩 (left ≐ₘ right) := by
  intro target env values hv bs fs hb hf
  exact (atomic_reflection h𝒩 env values hv false (hl env values hv bs fs hb hf) (hr env values hv bs fs hb hf)).1

theorem conj {left right : SetFormula bound free} (hl : Positive 𝒩 left) (hr : Positive 𝒩 right) :
    Positive 𝒩 (left ∧ₘ right) := by
  intro target env values hv bs fs hb hf ht
  exact values_modus_ponens (values := values) h𝒩 _ _ hv (hr env values hv bs fs hb hf ht.2)
    (reflection_rule h𝒩 values hv (boolean_rule_derives .conj true true _ _) (hl env values hv bs fs hb hf ht.1))

theorem disj {left right : SetFormula bound free} (hl : Positive 𝒩 left) (hr : Positive 𝒩 right) :
    Positive 𝒩 (left ∨ₘ right) := by
  intro target env values hv bs fs hb hf ht
  rcases ht with ht | ht
  · exact reflection_rule h𝒩 values hv
      (source_complete (.imp (left.substituteMapped bs fs) (.disj (left.substituteMapped bs fs) (right.substituteMapped bs fs)))
        (fun _ _ _ h => Or.inl h)) (hl env values hv bs fs hb hf ht)
  · exact reflection_rule h𝒩 values hv
      (source_complete (.imp (right.substituteMapped bs fs) (.disj (left.substituteMapped bs fs) (right.substituteMapped bs fs)))
        (fun _ _ _ h => Or.inr h)) (hr env values hv bs fs hb hf ht)

theorem allOf {formulas : List (SetFormula bound free)} (h : ∀ f ∈ formulas, Positive 𝒩 f) :
    Positive 𝒩 (ObjectHorn.allOf formulas) := by
  induction formulas with
  | nil => exact fun env values hv _ _ _ _ _ => (truth_reflection h𝒩 env values hv).1 True.intro
  | cons head tail ih => exact conj h𝒩 (h head List.mem_cons_self) (ih (fun f hf => h f (List.mem_cons_of_mem head hf)))

theorem anyOf {formulas : List (SetFormula bound free)} (h : ∀ f ∈ formulas, Positive 𝒩 f) :
    Positive 𝒩 (ObjectHorn.anyOf formulas) := by
  induction formulas with
  | nil => exact fun _ _ _ _ _ _ _ h => False.elim h
  | cons head tail ih => exact disj h𝒩 (h head List.mem_cons_self) (ih (fun f hf => h f (List.mem_cons_of_mem head hf)))

theorem horn (rules : List ObjectHorn.Rule)
    (hRules : ∀ root, mem 𝒩 root (w 𝒩) → Witness (ObjectHorn.step rules) root → HornProv 𝒩 rules root)
    {root : SetTerm bound free} (hr : Evaluates 𝒩 root) : Positive 𝒩 (ObjectHorn.condition rules root) := by
  intro target env values hv bs fs hb hf ht
  rw [ObjectHorn.condition_substituteMapped] at ht ⊢
  have he := hr env values hv bs fs hb hf
  exact (horn_term_transfer h𝒩 env values hv rules _ he).mpr
    (hRules _ he.1 ((horn_satisfies _ _ _).mp ht))

omit h𝒩 in
theorem instantiate {params : SetContext} (template : FormulaTemplate params)
    (h : Positive 𝒩 template.body) (sub : VariableSubstitution signature params bound free)
    (hSub : ∀ entry : Variable params .set, Evaluates 𝒩 (sub entry)) : Positive 𝒩 (template.instantiate sub) := by
  intro target env values hv bs fs hb hf
  change (template.body.substituteMapped VariableSubstitution.empty sub |>.substituteMapped bs fs).satisfies env → _
  simp only [FormulaTemplate.instantiate, Formula.substituteMapped_comp]
  exact h env values hv _ _ (fun entry => nomatch entry) (fun entry => hSub entry env values hv bs fs hb hf)

omit h𝒩 in
theorem evaluates_empty : ∀ entry : Variable [] SetSort.set,
    Evaluates 𝒩 ((VariableSubstitution.empty : VariableSubstitution signature [] bound free) entry) := fun entry => nomatch entry

omit h𝒩 in
theorem evaluates_cons {params : SetContext} {head : SetTerm bound free}
    {tail : VariableSubstitution signature params bound free}
    (hh : Evaluates 𝒩 head) (ht : ∀ entry : Variable params .set, Evaluates 𝒩 (tail entry)) :
    ∀ entry : Variable (.set :: params) .set, Evaluates 𝒩 (VariableSubstitution.cons head tail entry) := by
  intro entry
  cases entry with
  | here => exact hh
  | there entry => exact ht entry

omit h𝒩 in
theorem unary (template : FormulaTemplate.Unary) (h : Positive 𝒩 template.body)
    {input : SetTerm bound free} (hi : Evaluates 𝒩 input) : Positive 𝒩 (template input) :=
  instantiate template h _ (evaluates_cons hi evaluates_empty)

omit h𝒩 in
theorem binary (template : FormulaTemplate.Binary) (h : Positive 𝒩 template.body)
    {left right : SetTerm bound free} (hl : Evaluates 𝒩 left) (hr : Evaluates 𝒩 right) :
    Positive 𝒩 (template left right) :=
  instantiate template h _ (evaluates_cons hl (evaluates_cons hr evaluates_empty))

omit h𝒩 in
theorem ternary (template : FormulaTemplate.Ternary) (h : Positive 𝒩 template.body)
    {a b c : SetTerm bound free} (ha : Evaluates 𝒩 a) (hb : Evaluates 𝒩 b) (hc : Evaluates 𝒩 c) :
    Positive 𝒩 (template a b c) :=
  instantiate template h _ (evaluates_cons ha (evaluates_cons hb (evaluates_cons hc evaluates_empty)))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalPositiveFormula
