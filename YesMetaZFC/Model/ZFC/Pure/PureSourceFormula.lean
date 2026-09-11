import YesMetaZFC.Model.ZFC.Pure.PureSourceHorn
import YesMetaZFC.Automation.ObjectArithmeticTerm

/-! # 自然数参数公式的组合对应

环境参数及有界见证只要求属于模型内部 ω。模板替换保持这项条件，
而整个 Horn 轨迹由同一集合上的成员关系比较。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceFormula
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct _root_.YesMetaZFC.SetTheory.signature
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)

def Envs {bound free : SetContext} (env : Env 𝒩 bound free)
    (other : Env (canonical h𝒩) bound free) : Prop :=
  (∀ entry : Variable bound .set, mem 𝒩 (env.boundVal entry) (w 𝒩) ∧ env.boundVal entry = other.boundVal entry) ∧
  (∀ entry : Variable free .set, mem 𝒩 (env.freeVal entry) (w 𝒩) ∧ env.freeVal entry = other.freeVal entry)

def Natural {bound free : SetContext} (term : SetTerm bound free) : Prop :=
  ∀ env other, Envs h𝒩 env other → mem 𝒩 (term.eval env) (w 𝒩) ∧ term.eval env = term.eval other

def Stable {bound free : SetContext} (formula : SetFormula bound free) : Prop :=
  ∀ env other, Envs h𝒩 env other → (formula.satisfies env ↔ formula.satisfies other)

variable {h𝒩} {bound free : SetContext}

theorem bvar (entry : Variable bound .set) : Natural h𝒩 (.bvar entry : SetTerm bound free) :=
  fun _ _ h => h.1 entry

theorem fvar (entry : Variable free .set) : Natural h𝒩 (.fvar entry : SetTerm bound free) :=
  fun _ _ h => h.2 entry

theorem numeral (number : Nat) : Natural h𝒩 (numₘ(number) : SetTerm bound free) := by
  intro env other _
  rw [PureSourceCoding.numeral_eval, PureSourceCoding.numeral_eval]
  exact ⟨PureSourceCoding.numeral_natural h𝒩 number, numeral_agrees h𝒩 number⟩

theorem successor {term : SetTerm bound free} (h : Natural h𝒩 term) : Natural h𝒩 (Sₘ(term)) := by
  intro env other hEnv
  obtain ⟨hNat, hEq⟩ := h env other hEnv
  exact ⟨(omega_closed h𝒩).2 _ hNat, (successor_agrees h𝒩 _).trans (congrArg (suc (canonical h𝒩)) hEq)⟩

theorem pairing {left right : SetTerm bound free} (hLeft : Natural h𝒩 left) (hRight : Natural h𝒩 right) :
    Natural h𝒩 (godel_pairₘ(left, right)) := by
  intro env other hEnv
  obtain ⟨hl, el⟩ := hLeft env other hEnv
  obtain ⟨hr, er⟩ := hRight env other hEnv
  refine ⟨(PureSourceCoding.pairing_spec h𝒩 hl hr).1, ?_⟩
  change pair 𝒩 _ _ = pair (canonical h𝒩) _ _
  rw [PureSourceCoding.pairing_agrees h𝒩 hl hr, el, er]

theorem exponentiation {left right : SetTerm bound free} (hLeft : Natural h𝒩 left) (hRight : Natural h𝒩 right) :
    Natural h𝒩 (left ^ₘ right) := by
  intro env other hEnv
  obtain ⟨hl, el⟩ := hLeft env other hEnv
  obtain ⟨hr, er⟩ := hRight env other hEnv
  refine ⟨(PureSourceArithmetic.specification h𝒩 .exponentiation hl hr).1, ?_⟩
  change power 𝒩 _ _ = power (canonical h𝒩) _ _
  rw [PureSourceArithmetic.exponentiation_agrees h𝒩 hl hr, el, er]

theorem shift (count : Nat) {term : SetTerm bound free} (h : Natural h𝒩 term) :
    Natural h𝒩 (ObjectArithmeticTerm.shift count term) := by
  induction count with
  | zero => exact h
  | succ count ih => exact successor ih

theorem tableBound {term : SetTerm bound free} (h : Natural h𝒩 term) :
    Natural h𝒩 (ObjectArithmeticTerm.tableBound term) :=
  exponentiation (shift 8 h) (exponentiation (numeral 16) (shift 2 h))

theorem expression {n : Nat} (expr : ObjectHorn.Expr n) (inputs : Fin n → SetTerm bound free)
    (hInputs : ∀ i, Natural h𝒩 (inputs i)) : Natural h𝒩 (expr.term inputs) := by
  intro env other hEnv
  rw [expr_eval, expr_eval]
  have hNat i := (hInputs i env other hEnv).1
  refine ⟨PureSourceHorn.expr_natural h𝒩 hNat expr, ?_⟩
  rw [PureSourceHorn.expr_agrees h𝒩 hNat expr]
  exact congrArg (fun values => exprValue (canonical h𝒩) values expr)
    (funext (fun i => (hInputs i env other hEnv).2))

theorem fields {terms : List (SetTerm bound free)} (h : ∀ term ∈ terms, Natural h𝒩 term) :
    Natural h𝒩 (structural_list_code_term terms) := by
  induction terms with
  | nil => exact successor (pairing (numeral 0) (numeral 0))
  | cons head tail ih => exact successor (pairing (numeral 1)
      (pairing (h head List.mem_cons_self) (ih (fun term ht => h term (List.mem_cons_of_mem head ht)))))

theorem node (tag : Nat) {terms : List (SetTerm bound free)} (h : ∀ term ∈ terms, Natural h𝒩 term) :
    Natural h𝒩 (IntrinsicQuotation.node tag terms) :=
  successor (pairing (numeral tag) (fields h))

theorem equal {left right : SetTerm bound free} (hl : Natural h𝒩 left) (hr : Natural h𝒩 right) :
    Stable h𝒩 (left ≐ₘ right) := by
  intro env other hEnv
  change left.eval env = right.eval env ↔ left.eval other = right.eval other
  rw [(hl env other hEnv).2, (hr env other hEnv).2]

theorem conj {left right : SetFormula bound free} (hl : Stable h𝒩 left) (hr : Stable h𝒩 right) :
    Stable h𝒩 (left ∧ₘ right) := fun env other h => and_congr (hl env other h) (hr env other h)

theorem disj {left right : SetFormula bound free} (hl : Stable h𝒩 left) (hr : Stable h𝒩 right) :
    Stable h𝒩 (left ∨ₘ right) := fun env other h => or_congr (hl env other h) (hr env other h)

theorem allOf {formulas : List (SetFormula bound free)} (h : ∀ f ∈ formulas, Stable h𝒩 f) :
    Stable h𝒩 (ObjectHorn.allOf formulas) := by
  intro env other hEnv
  rw [allOf_satisfies, allOf_satisfies]
  exact forall_congr' (fun f => imp_congr_right (fun hf => h f hf env other hEnv))

theorem anyOf {formulas : List (SetFormula bound free)} (h : ∀ f ∈ formulas, Stable h𝒩 f) :
    Stable h𝒩 (ObjectHorn.anyOf formulas) := by
  intro env other hEnv
  rw [anyOf_satisfies, anyOf_satisfies]
  exact exists_congr (fun f => and_congr_right (fun hf => h f hf env other hEnv))

theorem horn (rules : List ObjectHorn.Rule) {root : SetTerm bound free} (h : Natural h𝒩 root) :
    Stable h𝒩 (ObjectHorn.condition rules root) :=
  fun env other hEnv => PureSourceHorn.condition_agrees h𝒩 rules env other root (h env other hEnv).2

theorem instantiate {params : SetContext} (template : FormulaTemplate params)
    (h : Stable h𝒩 template.body) (substitution : VariableSubstitution signature params bound free)
    (hSub : ∀ entry : Variable params .set, Natural h𝒩 (substitution entry)) :
    Stable h𝒩 (template.instantiate substitution) := by
  intro env other hEnv
  change (template.body.substitute (.map VariableSubstitution.empty substitution)).satisfies env ↔
    (template.body.substitute (.map VariableSubstitution.empty substitution)).satisfies other
  rw [Formula.satisfies_substitute, Formula.satisfies_substitute]
  exact h _ _ ⟨(fun entry => nomatch entry), fun entry => hSub entry env other hEnv⟩

theorem boundEnvs {env : Env 𝒩 [] free} {other : Env (canonical h𝒩) [] free}
    (h : Envs h𝒩 env other) {count : Nat} (values : Fin count → 𝒩.Carrier .set)
    (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩)) :
    Envs h𝒩 (boundEnv env count values) (boundEnv other count values) := by
  constructor
  · induction count with
    | zero => exact h.1
    | succ count ih =>
      intro entry
      cases entry with
      | here => exact ⟨hValues 0, rfl⟩
      | there entry => exact ih (fun i => values i.succ) (fun i => hValues i.succ) entry
  · intro entry
    simpa only [boundEnv_free] using h.2 entry

theorem quantify (count : Nat) {limit : SetOpenTerm free}
    {body : SetFormula (QuineEncoding.project_bound_context count) free}
    (hLimit : Natural h𝒩 limit) (hBody : Stable h𝒩 body) :
    Stable h𝒩 (ObjectHorn.quantify count limit body) := by
  intro env other hEnv
  rw [quantify_satisfies, quantify_satisfies]
  apply exists_congr
  intro values
  change ((∀ i, mem 𝒩 (values i) (limit.eval env)) ∧ _) ↔
    ((∀ i, mem 𝒩 (values i) (limit.eval other)) ∧ _)
  rw [← (hLimit env other hEnv).2]
  apply and_congr_right
  intro hBound
  exact hBody _ _ (boundEnvs hEnv values
    (fun i => member_natural h𝒩 (hLimit env other hEnv).1 (hBound i)))

theorem natural_empty : ∀ entry : Variable [] SetSort.set,
    Natural h𝒩 ((VariableSubstitution.empty : VariableSubstitution signature [] bound free) entry) :=
  fun entry => nomatch entry

theorem natural_cons {params : SetContext} {head : SetTerm bound free}
    {tail : VariableSubstitution signature params bound free}
    (hHead : Natural h𝒩 head) (hTail : ∀ entry : Variable params .set, Natural h𝒩 (tail entry)) :
    ∀ entry : Variable (.set :: params) .set, Natural h𝒩 (VariableSubstitution.cons head tail entry) := by
  intro entry
  cases entry with
  | here => exact hHead
  | there entry => exact hTail entry

theorem unary (template : FormulaTemplate.Unary) (h : Stable h𝒩 template.body)
    {input : SetTerm bound free} (hInput : Natural h𝒩 input) : Stable h𝒩 (template input) :=
  instantiate template h _ (natural_cons hInput natural_empty)

theorem binary (template : FormulaTemplate.Binary) (h : Stable h𝒩 template.body)
    {left right : SetTerm bound free} (hl : Natural h𝒩 left) (hr : Natural h𝒩 right) :
    Stable h𝒩 (template left right) := instantiate template h _ (natural_cons hl (natural_cons hr natural_empty))

theorem ternary (template : FormulaTemplate.Ternary) (h : Stable h𝒩 template.body)
    {a b c : SetTerm bound free} (ha : Natural h𝒩 a) (hb : Natural h𝒩 b) (hc : Natural h𝒩 c) :
    Stable h𝒩 (template a b c) :=
  instantiate template h _ (natural_cons ha (natural_cons hb (natural_cons hc natural_empty)))

theorem unaryAgreement (template : FormulaTemplate.Unary) (h : Stable h𝒩 template.body) :
    PureSourceHorn.UnaryAgreement h𝒩 template := by
  intro row hRow
  apply h
  constructor
  · intro entry; cases entry
  · intro entry
    cases entry with
    | here => exact ⟨hRow, rfl⟩
    | there entry => cases entry

theorem binaryTest {T : SetTheory} (C : CertificateCore T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (test : ObjectBinaryTest.Test T) (h : Stable h𝒩 test.condition.body) :
    PureSourceHorn.UnaryAgreement h𝒩 (ObjectBinaryTest.localTest C hSuccessor test).condition := by
  apply unaryAgreement
  apply quantify 2 (successor (fvar _))
  apply conj (equal (fvar _) (node 0 ?_)) (binary test.condition h (bvar _) (bvar _))
  intro term ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> exact bvar _

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceFormula
