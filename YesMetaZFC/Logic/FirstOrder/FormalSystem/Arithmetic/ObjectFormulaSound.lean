import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectFormulaAccept
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuotationDecode

/-! # 完整公式识别图的类型可靠性

有限图接受的任意自然数都重构为当前 AST 的类型正确语法。
这排除了“仅在已知良构输入上正确”的弱规格。
-/
namespace YesMetaZFC.Automation.ObjectFormulaSyntax
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT NatPacket IntrinsicQuotation ObjectHorn
open ObjectTermSyntax
set_option autoImplicit false

private theorem contexts_equal {left right : SetContext} (h : left.length = right.length) : left = right := by
  induction left generalizing right with
  | nil => exact (List.length_eq_zero_iff.mp h.symm).symm
  | cons sort tail ih =>
    cases right with
    | nil => cases h
    | cons other rest =>
      cases sort
      cases other
      exact congrArg (List.cons SetSort.set) (ih (Nat.succ.inj h))

inductive Meaning : Nat → Prop where
  | term (bound free : SetContext) (input : SetTerm bound free) :
      Meaning (termRow bound.length free.length (SyntaxEncode.term input))
  | arguments (bound free sorts : SetContext) (input : Arguments signature bound free sorts) :
      Meaning (argumentRow bound.length free.length sorts.length (SyntaxEncode.argumentsList input))
  | formula (bound free : SetContext) (input : SetFormula bound free) :
      Meaning (formulaRow bound.length free.length (SyntaxEncode.formula input))

private theorem extract_term {row : Nat} (h : Meaning row) (bound free : SetContext) (input : Nat)
    (hRow : row = nodeValue 0 [bound.length, free.length, input]) :
    ∃ term : SetTerm bound free, treeValue (SyntaxEncode.term term) = input := by
  cases h with
  | term sourceBound sourceFree term =>
    have h := (nodeValue_eq_iff _ _ _ _).mp hRow
    simp only [List.cons.injEq, and_true] at h
    obtain rfl := contexts_equal h.2.1
    obtain rfl := contexts_equal h.2.2.1
    exact ⟨term, h.2.2.2⟩
  | arguments sourceBound sourceFree sorts args =>
    have h := (nodeValue_eq_iff _ _ _ _).mp hRow
    cases h.1
  | formula sourceBound sourceFree formula =>
    have h := (nodeValue_eq_iff _ _ _ _).mp hRow
    cases h.1

private theorem extract_arguments {row : Nat} (h : Meaning row) (bound free sorts : SetContext) (input : Nat)
    (hRow : row = nodeValue 1 [bound.length, free.length, sorts.length, input]) :
    ∃ args : Arguments signature bound free sorts,
      listValue ((SyntaxEncode.argumentsList args).map treeValue) = input := by
  cases h with
  | term sourceBound sourceFree term =>
    have h := (nodeValue_eq_iff _ _ _ _).mp hRow
    cases h.1
  | arguments sourceBound sourceFree sourceSorts args =>
    have h := (nodeValue_eq_iff _ _ _ _).mp hRow
    simp only [List.cons.injEq, and_true] at h
    obtain rfl := contexts_equal h.2.1
    obtain rfl := contexts_equal h.2.2.1
    obtain rfl := contexts_equal h.2.2.2.1
    exact ⟨args, h.2.2.2.2⟩
  | formula sourceBound sourceFree formula =>
    have h := (nodeValue_eq_iff _ _ _ _).mp hRow
    cases h.1

private theorem extract_formula {row : Nat} (h : Meaning row) (bound free : SetContext) (input : Nat)
    (hRow : row = nodeValue 4 [bound.length, free.length, input]) :
    ∃ formula : SetFormula bound free, treeValue (SyntaxEncode.formula formula) = input := by
  cases h with
  | term sourceBound sourceFree term =>
    have h := (nodeValue_eq_iff _ _ _ _).mp hRow
    cases h.1
  | arguments sourceBound sourceFree sorts args =>
    have h := (nodeValue_eq_iff _ _ _ _).mp hRow
    cases h.1
  | formula sourceBound sourceFree formula =>
    have h := (nodeValue_eq_iff _ _ _ _).mp hRow
    simp only [List.cons.injEq, and_true] at h
    obtain rfl := contexts_equal h.2.1
    obtain rfl := contexts_equal h.2.2.1
    exact ⟨formula, h.2.2.2⟩

private abbrev ctx (n : Nat) : SetContext := List.replicate n SetSort.set

private theorem variable_sound (isFree : Bool) (values : Fin 3 → Nat)
    (hGuard : values 2 < values (if isFree then 1 else 0)) :
    Meaning ((variableRule isFree).head.eval values) := by
  cases isFree with
  | false =>
    obtain ⟨entry, hEntry⟩ := SyntaxDecode.variable_exists (ctx (values 0)) (values 2) (by simpa using hGuard)
    have h := Meaning.term (ctx (values 0)) (ctx (values 1)) (.bvar entry)
    simpa [termRow, variableRule, variableRule.rawNodeVar, ObjectTermSyntax.node, Expr.eval,
      SyntaxDecode.variable_index hEntry, ctx, leaf] using h
  | true =>
    obtain ⟨entry, hEntry⟩ := SyntaxDecode.variable_exists (ctx (values 1)) (values 2) (by simpa using hGuard)
    have h := Meaning.term (ctx (values 0)) (ctx (values 1)) (.fvar entry)
    simpa [termRow, variableRule, variableRule.rawNodeVar, ObjectTermSyntax.node, Expr.eval,
      SyntaxDecode.variable_index hEntry, ctx, leaf] using h

private theorem application_sound (symbol : FunctionSymbol) (values : Fin 3 → Nat)
    (hArgs : Meaning (nodeValue 1 [values 0, values 1, (signature.funcDomain symbol).length, values 2])) :
    Meaning ((applicationRule symbol).head.eval values) := by
  obtain ⟨args, hArgs⟩ := extract_arguments hArgs (ctx (values 0)) (ctx (values 1))
    (signature.funcDomain symbol) (values 2) (by simp)
  have h := Meaning.term _ _ (SyntaxDecode.application symbol args)
  simpa [termRow, applicationRule, ObjectTermSyntax.node, rawNode, cons, Expr.eval,
    leaf, treeValue_node, nodeValue, listValue, ctx, hArgs] using h

private theorem nil_sound (values : Fin 2 → Nat) : Meaning (nilRule.head.eval values) := by
  simpa [argumentRow, nilRule, ObjectTermSyntax.node, Expr.eval, ctx, SyntaxEncode.argumentsList]
    using Meaning.arguments (ctx (values 0)) (ctx (values 1)) [] .nil

private theorem cons_sound (values : Fin 5 → Nat)
    (hHead : Meaning (nodeValue 0 [values 0, values 1, values 3]))
    (hTail : Meaning (nodeValue 1 [values 0, values 1, values 2, values 4])) :
    Meaning (consRule.head.eval values) := by
  obtain ⟨head, hHead⟩ := extract_term hHead (ctx (values 0)) (ctx (values 1)) (values 3) (by simp)
  obtain ⟨tail, hTail⟩ := extract_arguments hTail (ctx (values 0)) (ctx (values 1))
    (ctx (values 2)) (values 4) (by simp)
  have h := Meaning.arguments _ _ _ (.cons head tail)
  simpa [argumentRow, consRule, ObjectTermSyntax.node, cons, Expr.eval,
    SyntaxEncode.argumentsList, ctx, listValue, hHead, hTail] using h

private theorem constant_sound (tag : Nat) (hTag : tag = 0 ∨ tag = 1) (values : Fin 2 → Nat) :
    Meaning ((constantRule tag).head.eval values) := by
  rcases hTag with rfl | rfl
  · simpa [formulaRow, SyntaxEncode.formula, leaf, constantRule, ObjectTermSyntax.node, Expr.eval, ctx]
      using Meaning.formula (ctx (values 0)) (ctx (values 1)) .falsum
  · simpa [formulaRow, SyntaxEncode.formula, leaf, constantRule, ObjectTermSyntax.node, Expr.eval, ctx]
      using Meaning.formula (ctx (values 0)) (ctx (values 1)) .truth

private theorem relation_sound (symbol : RelationSymbol) (values : Fin 3 → Nat)
    (hArgs : Meaning (nodeValue 1 [values 0, values 1, (signature.relDomain symbol).length, values 2])) :
    Meaning ((relationRule symbol).head.eval values) := by
  obtain ⟨args, hArgs⟩ := extract_arguments hArgs (ctx (values 0)) (ctx (values 1))
    (signature.relDomain symbol) (values 2) (by simp)
  have h := Meaning.formula _ _ (.rel symbol args)
  simpa [formulaRow, SyntaxEncode.formula, relationRule, ObjectTermSyntax.node, rawNode, cons, Expr.eval,
    leaf, treeValue_node, nodeValue, listValue, ctx, hArgs] using h

private theorem equality_sound (values : Fin 4 → Nat)
    (hLeft : Meaning (nodeValue 0 [values 0, values 1, values 2]))
    (hRight : Meaning (nodeValue 0 [values 0, values 1, values 3])) :
    Meaning (equalityRule.head.eval values) := by
  obtain ⟨left, hLeft⟩ := extract_term hLeft (ctx (values 0)) (ctx (values 1)) (values 2) (by simp)
  obtain ⟨right, hRight⟩ := extract_term hRight (ctx (values 0)) (ctx (values 1)) (values 3) (by simp)
  have h := Meaning.formula _ _ (.equal left right)
  simpa [formulaRow, SyntaxEncode.formula, equalityRule, ObjectTermSyntax.node, Expr.eval, ctx, hLeft, hRight] using h

private theorem binary_sound (tag : Nat) (hTag : tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8)
    (values : Fin 4 → Nat)
    (hLeft : Meaning (nodeValue 4 [values 0, values 1, values 2]))
    (hRight : Meaning (nodeValue 4 [values 0, values 1, values 3])) :
    Meaning ((binaryRule tag).head.eval values) := by
  obtain ⟨left, hLeft⟩ := extract_formula hLeft (ctx (values 0)) (ctx (values 1)) (values 2) (by simp)
  obtain ⟨right, hRight⟩ := extract_formula hRight (ctx (values 0)) (ctx (values 1)) (values 3) (by simp)
  rcases hTag with rfl | rfl | rfl | rfl
  · simpa [formulaRow, SyntaxEncode.formula, binaryRule, ObjectTermSyntax.node, Expr.eval, ctx, hLeft, hRight]
      using Meaning.formula _ _ (.conj left right)
  · simpa [formulaRow, SyntaxEncode.formula, binaryRule, ObjectTermSyntax.node, Expr.eval, ctx, hLeft, hRight]
      using Meaning.formula _ _ (.disj left right)
  · simpa [formulaRow, SyntaxEncode.formula, binaryRule, ObjectTermSyntax.node, Expr.eval, ctx, hLeft, hRight]
      using Meaning.formula _ _ (.imp left right)
  · simpa [formulaRow, SyntaxEncode.formula, binaryRule, ObjectTermSyntax.node, Expr.eval, ctx, hLeft, hRight]
      using Meaning.formula _ _ (.iff left right)

private theorem negation_sound (values : Fin 3 → Nat)
    (hBody : Meaning (nodeValue 4 [values 0, values 1, values 2])) :
    Meaning ((unaryRule 4 false).head.eval values) := by
  obtain ⟨body, hBody⟩ := extract_formula hBody (ctx (values 0)) (ctx (values 1)) (values 2) (by simp)
  simpa [formulaRow, SyntaxEncode.formula, unaryRule, ObjectTermSyntax.node, Expr.eval, ctx, hBody]
    using Meaning.formula _ _ (.neg body)

private theorem quantifier_sound (tag : Nat) (hTag : tag = 9 ∨ tag = 10) (values : Fin 3 → Nat)
    (hBody : Meaning (nodeValue 4 [values 0 + 1, values 1, values 2])) :
    Meaning ((unaryRule tag true).head.eval values) := by
  obtain ⟨body, hBody⟩ := extract_formula hBody (.set :: ctx (values 0)) (ctx (values 1)) (values 2) (by simp)
  rcases hTag with rfl | rfl
  · simpa [formulaRow, SyntaxEncode.formula, unaryRule, ObjectTermSyntax.node, Expr.eval, ctx, hBody]
      using Meaning.formula _ _ (.forallE .set body)
  · simpa [formulaRow, SyntaxEncode.formula, unaryRule, ObjectTermSyntax.node, Expr.eval, ctx, hBody]
      using Meaning.formula _ _ (.existsE .set body)

private theorem rule_sound (rule : Rule) (hRule : rule ∈ rules) (values : Fin rule.arity → Nat)
    (hGuards : ∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values)
    (hPremises : ∀ premise, premise ∈ rule.premises → Meaning (premise.eval values)) :
    Meaning (rule.head.eval values) := by
  simp only [rules, termRules, argumentRules, formulaRules, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with (((rfl | rfl) | hRule) | rfl | rfl) |
    ((rfl | rfl) | hRule) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact variable_sound false values (hGuards _ List.mem_cons_self)
  · exact variable_sound true values (hGuards _ List.mem_cons_self)
  · obtain ⟨symbol, _, rfl⟩ := List.mem_map.mp hRule
    exact application_sound symbol values (hPremises _ List.mem_cons_self)
  · exact nil_sound values
  · exact cons_sound values (hPremises _ List.mem_cons_self)
      (hPremises _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact constant_sound 0 (Or.inl rfl) values
  · exact constant_sound 1 (Or.inr rfl) values
  · obtain ⟨symbol, _, rfl⟩ := List.mem_map.mp hRule
    exact relation_sound symbol values (hPremises _ List.mem_cons_self)
  · exact equality_sound values (hPremises _ List.mem_cons_self)
      (hPremises _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact negation_sound values (hPremises _ List.mem_cons_self)
  · exact binary_sound 5 (by simp) values (hPremises _ List.mem_cons_self)
      (hPremises _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact binary_sound 6 (by simp) values (hPremises _ List.mem_cons_self)
      (hPremises _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact binary_sound 7 (by simp) values (hPremises _ List.mem_cons_self)
      (hPremises _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact binary_sound 8 (by simp) values (hPremises _ List.mem_cons_self)
      (hPremises _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact quantifier_sound 9 (Or.inl rfl) values (hPremises _ List.mem_cons_self)
  · exact quantifier_sound 10 (Or.inr rfl) values (hPremises _ List.mem_cons_self)

/-- 接受任意自然数即保证当前 AST 的良构性，包括排序和两个变量上下文。 -/
theorem checked_sound (bound free : SetContext) (input : Nat)
    (h : checked bound.length free.length input = true) :
    ∃ formula : SetFormula bound free, treeValue (SyntaxEncode.formula formula) = input := by
  have hMeaning := check_sound rules rank descending Meaning
    (fun rule hRule values _ hGuards hPremises => rule_sound rule hRule values hGuards hPremises) _ h
  exact extract_formula hMeaning bound free input rfl

/-- 检查器的全自然数精确规格；不存在宿主预先假定良构的前提。 -/
theorem checked_iff (bound free : SetContext) (input : Nat) :
    checked bound.length free.length input = true ↔
      ∃ formula : SetFormula bound free, treeValue (SyntaxEncode.formula formula) = input := by
  constructor
  · exact checked_sound bound free input
  · rintro ⟨formula, rfl⟩
    exact checked_encode formula

/-- 固定识别图与实际自然数 quotation 解码、当前 AST 解码完全一致。 -/
theorem checked_decode (bound free : SetContext) (input : Nat) :
    checked bound.length free.length input = true ↔
      ∃ formula : SetFormula bound free,
        ((IntrinsicQuotation.decodeTree input).bind (SyntaxDecode.formula bound free)) = some formula := by
  rw [checked_iff]
  constructor
  · rintro ⟨formula, rfl⟩
    exact ⟨formula, by simp⟩
  · rintro ⟨formula, h⟩
    obtain ⟨tree, hTree, hFormula⟩ := Option.bind_eq_some_iff.mp h
    refine ⟨formula, ?_⟩
    rw [SyntaxDecode.formula_encode_of_decode bound free tree formula hFormula]
    exact treeValue_of_decode hTree


/-- 同一个完整语法图的项入口也提供全自然数的类型重构。 -/
theorem checked_term_iff (bound free : SetContext) (input : Nat) :
    check rules rank (nodeValue 0 [bound.length, free.length, input]) = true ↔
      ∃ term : SetTerm bound free, treeValue (SyntaxEncode.term term) = input := by
  constructor
  · intro h
    have hMeaning := check_sound rules rank descending Meaning
      (fun rule hRule values _ hGuards hPremises => rule_sound rule hRule values hGuards hPremises) _ h
    exact extract_term hMeaning bound free input rfl
  · rintro ⟨term, rfl⟩
    exact acceptance_check rules rank descending _ (term_accept term)

/-- 项列入口保留排序表及其长度，可直接识别自由代入表。 -/
theorem checked_arguments_iff (bound free sorts : SetContext) (input : Nat) :
    check rules rank (nodeValue 1 [bound.length, free.length, sorts.length, input]) = true ↔
      ∃ args : Arguments signature bound free sorts,
        listValue ((SyntaxEncode.argumentsList args).map treeValue) = input := by
  constructor
  · intro h
    have hMeaning := check_sound rules rank descending Meaning
      (fun rule hRule values _ hGuards hPremises => rule_sound rule hRule values hGuards hPremises) _ h
    exact extract_arguments hMeaning bound free sorts input rfl
  · rintro ⟨args, rfl⟩
    exact acceptance_check rules rank descending _ (arguments_accept args)

end YesMetaZFC.Automation.ObjectFormulaSyntax
