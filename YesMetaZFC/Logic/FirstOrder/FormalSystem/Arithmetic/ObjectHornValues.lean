import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornCertificate

/-! # 行码表达式的结构求值与单射 -/
namespace YesMetaZFC.Automation.ObjectHorn
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding ProofCode
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def listValue : List Nat → Nat
  | [] => godel_pair_value 0 0 + 1
  | head :: tail => godel_pair_value 1 (godel_pair_value head (listValue tail)) + 1

def nodeValue (tag : Nat) (fields : List Nat) : Nat := godel_pair_value tag (listValue fields) + 1

@[simp] theorem Expr.list_term {n : Nat} {bound free : SetContext}
    (fields : List (Expr n)) (env : Fin n → SetTerm bound free) :
    (Expr.list fields).term env = structural_list_code_term (fields.map (Expr.term env)) := by
  induction fields <;> simp_all [Expr.list, Expr.term, structural_list_code_term,
    structural_raw_node_code_term, structural_code_tag, finite_numeral_term]

@[simp] theorem Expr.node_term {n : Nat} {bound free : SetContext}
    (tag : Nat) (fields : List (Expr n)) (env : Fin n → SetTerm bound free) :
    (Expr.node (.literal tag) fields).term env =
      IntrinsicQuotation.node tag (fields.map (Expr.term env)) := by
  simp [Expr.node, Expr.term, IntrinsicQuotation.node]

@[simp] theorem Expr.list_eval {n : Nat} (fields : List (Expr n)) (env : Fin n → Nat) :
    (Expr.list fields).eval env = listValue (fields.map (Expr.eval env)) := by
  induction fields <;> simp_all [Expr.list, Expr.eval, listValue]

@[simp] theorem Expr.node_eval {n : Nat} (tag : Expr n) (fields : List (Expr n)) (env : Fin n → Nat) :
    (Expr.node tag fields).eval env = nodeValue (tag.eval env) (fields.map (Expr.eval env)) := by
  simp [Expr.node, Expr.eval, nodeValue]

theorem node_evaluate {T : SetTheory} (C : CertificateCore T) (tag : Nat) (fields : List Nat) :
    Derives T [] (IntrinsicQuotation.node tag (fields.map (fun n => (numₘ(n) : Code))) ≐ₘ numₘ(nodeValue tag fields)) := by
  have h := (Expr.node (.literal tag) (fields.map (Expr.literal (arity := 0)))).evaluate C Fin.elim0
  simpa [Expr.term, Expr.eval, Function.comp_def] using h

theorem numeral_list_evaluate {T : SetTheory} (C : CertificateCore T) (fields : List Nat) :
    Derives T [] (structural_list_code_term (fields.map (fun n => (numₘ(n) : Code))) ≐ₘ numₘ(listValue fields)) := by
  have h := (Expr.list (fields.map (Expr.literal (arity := 0)))).evaluate C Fin.elim0
  simpa [Expr.term, Expr.eval, Function.comp_def] using h

inductive FieldEqualities (T : SetTheory) {free : SetContext} (Γ : Context signature free) :
    List (SetOpenTerm free) → List (SetOpenTerm free) → Prop where
  | nil : FieldEqualities T Γ [] []
  | cons {left right : SetOpenTerm free} {lefts rights : List (SetOpenTerm free)}
      (head : Derives T Γ (left ≐ₘ right)) (tail : FieldEqualities T Γ lefts rights) :
      FieldEqualities T Γ (left :: lefts) (right :: rights)

theorem list_congr {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    {left right : List (SetOpenTerm free)}
    (h : FieldEqualities T Γ left right) :
    Derives T Γ (structural_list_code_term left ≐ₘ structural_list_code_term right) := by
  induction h with
  | nil => exact Metatheory.Derives.equality_refl _
  | cons hHead _ ih =>
    exact successor_term_congr_of_equality _ _ (IntrinsicPairing.pair_congr_of_equalities _ _ _ _
      (Metatheory.Derives.equality_refl _)
      (IntrinsicPairing.pair_congr_of_equalities _ _ _ _ hHead ih))

theorem node_congr {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (tag : Nat) {left right : List (SetOpenTerm free)}
    (h : FieldEqualities T Γ left right) :
    Derives T Γ (IntrinsicQuotation.node tag left ≐ₘ IntrinsicQuotation.node tag right) :=
  successor_term_congr_of_equality _ _ (IntrinsicPairing.pair_congr_of_equalities _ _ _ _
    (Metatheory.Derives.equality_refl _) (list_congr h))

@[simp] theorem condition_instantiateTop (rules : List Rule) {free : SetContext} (point : SetOpenTerm free) :
    (condition rules (.bvar .here : SetTerm [SetSort.set] free)).instantiateTop point =
      condition rules point := by
  simp [condition, Formula.instantiateTop, Formula.substitute, Substitution.instantiateTop,
    Term.substituteMapped, Arguments.substituteMapped, VariableSubstitution.instantiateTop]

theorem transport {T : SetTheory} (rules : List Rule) {free : SetContext} {Γ : Context signature free}
    {left right : SetOpenTerm free} (hEq : Derives T Γ (left ≐ₘ right))
    (h : Derives T Γ (condition rules left)) : Derives T Γ (condition rules right) := by
  have h := FirstOrder.Derives.eq_subst (body := condition rules (.bvar .here)) hEq
    (by rw [condition_instantiateTop]; exact h)
  rwa [condition_instantiateTop] at h

theorem transport_negative {T : SetTheory} (rules : List Rule) {free : SetContext} {Γ : Context signature free}
    {left right : SetOpenTerm free} (hEq : Derives T Γ (left ≐ₘ right))
    (h : Derives T Γ (¬ₘ condition rules left)) : Derives T Γ (¬ₘ condition rules right) := by
  have h := FirstOrder.Derives.eq_subst (body := .neg (condition rules (.bvar .here))) hEq
    (by rw [Formula.instantiateTop_neg, condition_instantiateTop]; exact h)
  rwa [Formula.instantiateTop_neg, condition_instantiateTop] at h

@[simp] theorem listValue_eq_iff (left right : List Nat) :
    listValue left = listValue right ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [listValue, godel_pair_value_eq_iff]
  | cons head tail ih =>
    cases right <;> simp [listValue, godel_pair_value_eq_iff, ih]

@[simp] theorem nodeValue_eq_iff (leftTag rightTag : Nat) (left right : List Nat) :
    nodeValue leftTag left = nodeValue rightTag right ↔ leftTag = rightTag ∧ left = right := by
  simp [nodeValue, godel_pair_value_eq_iff]

theorem listValue_cons {input : List Nat} {head tail : Nat}
    (h : listValue input = godel_pair_value 1 (godel_pair_value head tail) + 1) :
    ∃ rest, input = head :: rest ∧ listValue rest = tail := by
  cases input with
  | nil =>
    have hTag := (godel_pair_value_eq_iff.mp (Nat.add_right_cancel h)).1
    exact False.elim (Nat.zero_ne_one hTag)
  | cons actual rest =>
    have hFields := godel_pair_value_eq_iff.mp
      (godel_pair_value_eq_iff.mp (Nat.add_right_cancel h)).2
    exact ⟨rest, congrArg (fun h => h :: rest) hFields.1, hFields.2⟩

@[simp] theorem treeValue_node (tag : Nat) (children : List NatPacket.Tree) :
    IntrinsicQuotation.treeValue (.node tag children) =
      nodeValue tag (children.map IntrinsicQuotation.treeValue) := by
  have hForest : IntrinsicQuotation.forestValue children =
      listValue (children.map IntrinsicQuotation.treeValue) := by
    induction children <;> simp_all [IntrinsicQuotation.forestValue, listValue]
  exact congrArg (fun payload => godel_pair_value tag payload + 1) hForest

theorem tree_node_zero (input : NatPacket.Tree) (tag : Nat)
    (h : IntrinsicQuotation.treeValue input = nodeValue tag []) : input = .node tag [] := by
  apply IntrinsicQuotation.treeValue_injective
  simpa using h

theorem tree_node_one (input : NatPacket.Tree) (tag value : Nat)
    (h : IntrinsicQuotation.treeValue input = nodeValue tag [value]) :
    ∃ body, input = .node tag [body] ∧ IntrinsicQuotation.treeValue body = value := by
  cases input with
  | node inputTag children =>
    simp only [treeValue_node, nodeValue_eq_iff] at h
    rcases h with ⟨rfl, h⟩
    cases children with
    | nil => simp at h
    | cons body tail =>
      cases tail with
      | nil => exact ⟨body, rfl, (List.cons.inj h).1⟩
      | cons _ _ => simp at h

theorem tree_node_two (input : NatPacket.Tree) (tag leftValue rightValue : Nat)
    (h : IntrinsicQuotation.treeValue input = nodeValue tag [leftValue, rightValue]) :
    ∃ left right, input = .node tag [left, right] ∧
      IntrinsicQuotation.treeValue left = leftValue ∧ IntrinsicQuotation.treeValue right = rightValue := by
  cases input with
  | node inputTag children =>
    simp only [treeValue_node, nodeValue_eq_iff] at h
    rcases h with ⟨rfl, h⟩
    cases children with
    | nil => simp at h
    | cons left tail =>
      cases tail with
      | nil => simp at h
      | cons right tail =>
        cases tail with
        | nil => exact ⟨left, right, rfl, (List.cons.inj h).1, (List.cons.inj (List.cons.inj h).2).1⟩
        | cons _ _ => simp at h

theorem treeValue_node_zero {input : NatPacket.Tree} {tag : Nat}
    (h : IntrinsicQuotation.treeValue input = nodeValue tag []) : input = .node tag [] := by
  apply IntrinsicQuotation.treeValue_injective
  simpa using h

theorem treeValue_node_one {input : NatPacket.Tree} {tag value : Nat}
    (h : IntrinsicQuotation.treeValue input = nodeValue tag [value]) :
    ∃ body, input = .node tag [body] ∧ IntrinsicQuotation.treeValue body = value := by
  cases input with
  | node actual fields =>
    have h := nodeValue_eq_iff _ _ _ _ |>.mp ((treeValue_node _ _).symm.trans h)
    rcases h with ⟨rfl, hFields⟩
    cases fields with
    | nil => simp at hFields
    | cons head tail =>
      cases tail with
      | nil => exact ⟨head, rfl, (List.cons.inj hFields).1⟩
      | cons _ _ => simp at hFields

theorem treeValue_node_two {input : NatPacket.Tree} {tag left right : Nat}
    (h : IntrinsicQuotation.treeValue input = nodeValue tag [left, right]) :
    ∃ a b, input = .node tag [a, b] ∧ IntrinsicQuotation.treeValue a = left ∧
      IntrinsicQuotation.treeValue b = right := by
  cases input with
  | node actual fields =>
    have h := nodeValue_eq_iff _ _ _ _ |>.mp ((treeValue_node _ _).symm.trans h)
    rcases h with ⟨rfl, hFields⟩
    cases fields with
    | nil => simp at hFields
    | cons a tail =>
      cases tail with
      | nil => simp at hFields
      | cons b rest =>
        cases rest with
        | nil => exact ⟨a, b, rfl, (List.cons.inj hFields).1, (List.cons.inj (List.cons.inj hFields).2).1⟩
        | cons _ _ => simp at hFields

def Expr.tag? {n : Nat} : Expr n → Option Nat
  | .succ (.pair (.literal tag) _) => some tag
  | _ => none

theorem Expr.tag_of_eval {n : Nat} (expr : Expr n) (env : Fin n → Nat)
    (tag : Nat) (fields : List Nat) (hTagged : expr.tag?.isSome)
    (hEq : nodeValue tag fields = expr.eval env) : expr.tag? = some tag := by
  cases expr with
  | literal _ | var _ | pair _ _ => cases hTagged
  | succ body =>
    cases body with
    | literal _ | var _ | succ _ => cases hTagged
    | pair left right =>
      cases left with
      | var _ | succ _ | pair _ _ => cases hTagged
      | literal actual =>
        have hTag := (godel_pair_value_eq_iff.mp (Nat.add_right_cancel hEq)).1
        exact congrArg some hTag.symm

def rulesFor (rules : List Rule) (tag : Nat) : List Rule :=
  rules.filter (fun rule => rule.head.tag? == some tag)

theorem matching_rule {rules : List Rule} (hTagged : ∀ rule, rule ∈ rules → rule.head.tag?.isSome)
    {rule : Rule} (hRule : rule ∈ rules) (values : Fin rule.arity → Nat) (tag : Nat) (fields : List Nat)
    (hHead : nodeValue tag fields = rule.head.eval values) : rule ∈ rulesFor rules tag := by
  exact List.mem_filter.mpr ⟨hRule, by simp [rule.head.tag_of_eval values tag fields (hTagged rule hRule) hHead]⟩

theorem Rejection.of_tagged {rules : List Rule}
    (hTagged : ∀ rule, rule ∈ rules → rule.head.tag?.isSome) (tag : Nat) (fields : List Nat)
    (reject : ∀ rule, rule ∈ rulesFor rules tag → ∀ values : Fin rule.arity → Nat,
      (∀ i, values i ≤ nodeValue tag fields) → nodeValue tag fields = rule.head.eval values →
      (∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values) →
      ∃ premise, premise ∈ rule.premises ∧ Rejection rules (premise.eval values)) :
    Rejection rules (nodeValue tag fields) := by
  apply Rejection.of_rule
  intro rule hRule values hBound hHead hGuards
  exact reject rule (matching_rule hTagged hRule values tag fields hHead) values hBound hHead hGuards

end YesMetaZFC.Automation.ObjectHorn
