import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectSyntaxTransform
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuotationDecode

/-! # 共用语法变换图的数值可靠性

接受任意数值行时，输入必须重构为真实语法树，输出等于独立递归程序的结果。
参数表的合法性由使用此图的类型识别接口另行约束。
-/
namespace YesMetaZFC.Automation.ObjectSyntaxTransform
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT NatPacket IntrinsicQuotation
open ObjectHorn ObjectCodeProjection
set_option autoImplicit false

private def termMeaning (mode depth parameter input output : Nat) : Prop :=
  ∃ tree, treeValue tree = input ∧ SyntaxTransform.term mode depth parameter tree = some output
private def argumentsMeaning (mode depth parameter input output : Nat) : Prop :=
  ∃ trees, listValue (trees.map treeValue) = input ∧ SyntaxTransform.arguments mode depth parameter trees = some output
private def formulaMeaning (mode depth parameter input output : Nat) : Prop :=
  ∃ tree, treeValue tree = input ∧ SyntaxTransform.formula mode depth parameter tree = some output
private def Meaning (code : Nat) : Prop :=
  match tag code with
  | 0 => SyntaxTransform.lookup (field code 0) (field code 1) = some (field code 2)
  | 1 => termMeaning (field code 0) (field code 1) (field code 2) (field code 3) (field code 4)
  | 2 => argumentsMeaning (field code 0) (field code 1) (field code 2) (field code 3) (field code 4)
  | 3 => formulaMeaning (field code 0) (field code 1) (field code 2) (field code 3) (field code 4)
  | _ => False

private theorem bvar_sound (mode depth parameter index output : Nat)
    (h : SyntaxTransform.boundValue mode depth parameter index = some output) :
    termMeaning mode depth parameter (nodeValue 0 [nodeValue index []]) output :=
  ⟨.node 0 [.node index []] , by simp, h⟩
private theorem fvar_sound (mode depth parameter index output : Nat)
    (h : SyntaxTransform.freeValue mode depth parameter index = some output) :
    termMeaning mode depth parameter (nodeValue 1 [nodeValue index []]) output :=
  ⟨.node 1 [.node index []] , by simp, h⟩

private theorem application_sound (kind mode depth parameter symbol input output : Nat)
    (hKind : kind = 1 ∨ kind = 3) (h : argumentsMeaning mode depth parameter input output) :
    Meaning (nodeValue kind [mode, depth, parameter,
      ProofCode.godel_pair_value 2 (ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value (nodeValue symbol []) input) + 1) + 1,
      ProofCode.godel_pair_value 2 (ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value (nodeValue symbol []) output) + 1) + 1]) := by
  obtain ⟨trees, rfl, h⟩ := h
  rcases hKind with rfl | rfl
  all_goals simp only [Meaning, tag_node, field_node, get_zero, get_succ]
  all_goals refine ⟨.node 2 (.node symbol [] :: trees), by simp [nodeValue, listValue] , ?_⟩
  · simp [SyntaxTransform.term, h]
  · simp [SyntaxTransform.formula, h]

private theorem cons_sound (mode depth parameter first rest firstOut restOut : Nat)
    (hFirst : termMeaning mode depth parameter first firstOut)
    (hRest : argumentsMeaning mode depth parameter rest restOut) :
    argumentsMeaning mode depth parameter
      (ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value first rest) + 1)
      (ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value firstOut restOut) + 1) := by
  obtain ⟨firstTree, rfl, hFirst⟩ := hFirst
  obtain ⟨restTrees, rfl, hRest⟩ := hRest
  exact ⟨firstTree :: restTrees, by simp [listValue] , by simp [SyntaxTransform.arguments, hFirst, hRest]⟩

private theorem binary_sound (tag mode depth parameter left right leftOut rightOut : Nat)
    (hTag : tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8)
    (hLeft : formulaMeaning mode depth parameter left leftOut)
    (hRight : formulaMeaning mode depth parameter right rightOut) :
    formulaMeaning mode depth parameter (nodeValue tag [left, right]) (nodeValue tag [leftOut, rightOut]) := by
  obtain ⟨leftTree, rfl, hLeft⟩ := hLeft
  obtain ⟨rightTree, rfl, hRight⟩ := hRight
  refine ⟨.node tag [leftTree, rightTree] , by simp, ?_⟩
  rcases hTag with rfl | rfl | rfl | rfl
  all_goals simp [SyntaxTransform.formula, hLeft, hRight]

private theorem unary_sound (tag : Nat) (binder : Bool) (mode depth parameter input output : Nat)
    (hTag : (tag = 4 ∧ binder = false) ∨ (tag = 9 ∧ binder = true) ∨ (tag = 10 ∧ binder = true))
    (h : formulaMeaning mode (if binder then depth + 1 else depth) parameter input output) :
    formulaMeaning mode depth parameter (nodeValue tag [input]) (nodeValue tag [output]) := by
  obtain ⟨tree, rfl, h⟩ := h
  refine ⟨.node tag [tree] , by simp, ?_⟩
  rcases hTag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp_all [SyntaxTransform.formula]

set_option maxHeartbeats 1000000 in
private theorem rule_sound (rule : Rule) (hRule : rule ∈ rules) (values : Fin rule.arity → Nat)
    (_hBound : ∀ i, values i ≤ rule.head.eval values)
    (hGuards : ∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values)
    (hPremises : ∀ premise, premise ∈ rule.premises → Meaning (premise.eval values)) :
    Meaning (rule.head.eval values) := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [lookupHead, lookupTail, boundIdentity, boundAbstract,
    boundPoint, boundPredecessor, freeWeaken, freeAbstractHead, freeAbstractTail,
    freeIdentity, freeReplace, application, nilArguments, consArguments,
    constant, binary, unary] at values hGuards hPremises ⊢
  all_goals simp [Expr.eval, Meaning] at hGuards hPremises ⊢
  · simpa using hPremises
  · exact bvar_sound _ _ _ _ _ rfl
  · exact bvar_sound _ _ _ _ _ rfl
  · apply bvar_sound
    simp [SyntaxTransform.boundValue, hGuards, SyntaxSubstitution.bvar, leaf]
  · apply bvar_sound
    have hNot : ¬ values 2 < values 0 := by omega
    simp [SyntaxTransform.boundValue, hNot, SyntaxSubstitution.bvar, leaf]
  · apply bvar_sound
    simp [SyntaxTransform.boundValue, hGuards, SyntaxSubstitution.bvar, leaf]
  · apply bvar_sound
    simp [SyntaxTransform.boundValue]
  · apply bvar_sound
    have hNot : ¬ values 2 + 1 < values 0 := by omega
    have hNe : values 2 + 1 ≠ values 0 := by omega
    simp [SyntaxTransform.boundValue, hNot, hNe, SyntaxSubstitution.bvar, leaf]
  · exact fvar_sound _ _ _ _ _ rfl
  · exact fvar_sound _ _ _ _ _ rfl
  · exact fvar_sound _ _ _ _ _ rfl
  · exact fvar_sound _ _ _ _ _ rfl
  · exact fvar_sound _ _ _ _ _ hPremises
  · simpa [Meaning] using application_sound 1 _ _ _ _ _ _ (Or.inl rfl) hPremises
  · exact ⟨[] , rfl, by simpa [SyntaxTransform.arguments] using hGuards⟩
  · exact cons_sound _ _ _ _ _ _ _ hPremises.1 hPremises.2
  · exact ⟨.node 0 [] , by simp, by simp [SyntaxTransform.formula, hGuards]⟩
  · exact ⟨.node 1 [] , by simp, by simp [SyntaxTransform.formula, hGuards]⟩
  · simpa [Meaning] using application_sound 3 _ _ _ _ _ _ (Or.inr rfl) hPremises
  · obtain ⟨left, hLeft, hLeftRun⟩ := hPremises.1
    obtain ⟨right, hRight, hRightRun⟩ := hPremises.2
    exact ⟨.node 3 [left, right] , by simp [hLeft, hRight] , by simp [SyntaxTransform.formula, hLeftRun, hRightRun]⟩
  · exact unary_sound 4 false _ _ _ _ _ (Or.inl ⟨rfl, rfl⟩) hPremises
  · exact binary_sound 5 _ _ _ _ _ _ _ (by simp) hPremises.1 hPremises.2
  · exact binary_sound 6 _ _ _ _ _ _ _ (by simp) hPremises.1 hPremises.2
  · exact binary_sound 7 _ _ _ _ _ _ _ (by simp) hPremises.1 hPremises.2
  · exact binary_sound 8 _ _ _ _ _ _ _ (by simp) hPremises.1 hPremises.2
  · exact unary_sound 9 true _ _ _ _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩)) hPremises
  · exact unary_sound 10 true _ _ _ _ _ (Or.inr (Or.inr ⟨rfl, rfl⟩)) hPremises

/-- 对任意自然数成立，而非仅限预先知道良构的输入。 -/
theorem checked_sound (mode depth parameter input output : Nat)
    (h : checked mode depth parameter input output = true) :
    ∃ tree, treeValue tree = input ∧ SyntaxTransform.formula mode depth parameter tree = some output := by
  have h := check_sound rules rank descending Meaning rule_sound _ h
  simpa [Meaning, formulaMeaning] using h

end YesMetaZFC.Automation.ObjectSyntaxTransform
