import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornValues
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaObjectGraph

/-! # 正文检查器到统一对象图的证书 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Body
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def row (tag depth : Nat) (input : Tree) : Nat := nodeValue tag [depth, treeValue input]

@[simp] theorem termRule_head (values : Fin 2 → Nat) : termRule.head.eval values =
    nodeValue 0 [values 0, nodeValue 0 [nodeValue (values 1) []]] := rfl

@[simp] theorem constantRule_head (tag : Nat) (values : Fin 1 → Nat) :
    (constantRule tag).head.eval values = nodeValue 1 [values 0, nodeValue tag []] := rfl

@[simp] theorem atomRule_head (tag : Nat) (values : Fin 3 → Nat) :
    (atomRule tag).head.eval values = nodeValue 1 [values 0, nodeValue tag [values 1, values 2]] := rfl

@[simp] theorem unaryRule_head (tag : Nat) (binder : Bool) (values : Fin 2 → Nat) :
    (unaryRule tag binder).head.eval values = nodeValue 1 [values 0, nodeValue tag [values 1]] := rfl

@[simp] theorem binaryRule_head (tag : Nat) (values : Fin 3 → Nat) :
    (binaryRule tag).head.eval values = nodeValue 1 [values 0, nodeValue tag [values 1, values 2]] := rfl

theorem head_variables (rule : Rule) (hRule : rule ∈ rules) :
    ∀ index, index ∈ rule.head.variables := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem accept_rule (rule : Rule) (hRule : rule ∈ rules) (values : Fin rule.arity → Nat)
    (hGuards : ∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values)
    (hPremises : ∀ premise, premise ∈ rule.premises → Acceptance rules (premise.eval values)) :
    Acceptance rules (rule.head.eval values) :=
  Acceptance.of_rule rule hRule values
    (fun index => rule.head.variable_le values (head_variables rule hRule index)) hGuards hPremises

theorem term_accept (depth : Nat) (input : Tree) (h : SchemaTerm.check depth input = true) :
    Acceptance rules (row 0 depth input) := by
  obtain ⟨index, hIndex, rfl⟩ := (SchemaTerm.check_eq_true_iff depth input).mp h
  have hRule := accept_rule termRule (by simp [rules])
    (fun i => if i.val = 0 then depth else index)
    (by
      intro guard hGuard
      have hGuard := List.mem_singleton.mp hGuard
      subst guard
      exact hIndex) (by intro premise hPremise; exact False.elim (List.not_mem_nil hPremise))
  simpa [termRule, row, SchemaObjectGraph.node, boundVar, Expr.eval, leaf] using hRule

theorem constant_accept (tag depth : Nat) (hTag : tag = 0 ∨ tag = 1) :
    Acceptance rules (row 1 depth (.node tag [])) := by
  have hRule : constantRule tag ∈ rules := by rcases hTag with rfl | rfl <;> simp [rules]
  have h := accept_rule (constantRule tag) hRule (fun _ => depth)
    (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry)) (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry))
  simpa [constantRule, row, SchemaObjectGraph.node, Expr.eval] using h

theorem atom_accept (tag depth : Nat) (left right : Tree) (hTag : tag = 2 ∨ tag = 3 ∨ tag = 11)
    (hLeft : SchemaTerm.check depth left = true) (hRight : SchemaTerm.check depth right = true) :
    Acceptance rules (row 1 depth (.node tag [left, right])) := by
  have hRule : atomRule tag ∈ rules := by rcases hTag with rfl | rfl | rfl <;> simp [rules]
  have h := accept_rule (atomRule tag) hRule
    (fun i => if i.val = 0 then depth else if i.val = 1 then treeValue left else treeValue right)
    (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry)) (by
      intro premise hPremise
      dsimp only [atomRule] at hPremise
      rcases List.mem_cons.mp hPremise with hPremise | hPremise
      · subst premise
        exact term_accept depth left hLeft
      · have hPremise := List.mem_singleton.mp hPremise
        subst premise
        exact term_accept depth right hRight)
  simpa [atomRule, row, SchemaObjectGraph.node, Expr.eval] using h

theorem unary_accept (tag depth : Nat) (binder : Bool) (body : Tree)
    (hRule : unaryRule tag binder ∈ rules)
    (hBody : Acceptance rules (row 1 (if binder then depth + 1 else depth) body)) :
    Acceptance rules (row 1 depth (.node tag [body])) := by
  have h := accept_rule (unaryRule tag binder) hRule
    (fun i => if i.val = 0 then depth else treeValue body)
    (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry)) (by
      intro premise hPremise
      have hPremise := List.mem_singleton.mp hPremise
      subst premise
      cases binder <;> exact hBody)
  simpa [unaryRule, row, SchemaObjectGraph.node, Expr.eval] using h

theorem binary_accept (tag depth : Nat) (left right : Tree) (hRule : binaryRule tag ∈ rules)
    (hLeft : Acceptance rules (row 1 depth left)) (hRight : Acceptance rules (row 1 depth right)) :
    Acceptance rules (row 1 depth (.node tag [left, right])) := by
  have h := accept_rule (binaryRule tag) hRule
    (fun i => if i.val = 0 then depth else if i.val = 1 then treeValue left else treeValue right)
    (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry)) (by
      intro premise hPremise
      dsimp only [binaryRule] at hPremise
      rcases List.mem_cons.mp hPremise with hPremise | hPremise
      · subst premise
        exact hLeft
      · have hPremise := List.mem_singleton.mp hPremise
        subst premise
        exact hRight)
  simpa [binaryRule, row, SchemaObjectGraph.node, Expr.eval] using h

/-- 实际递归解码成功时，逐构造子生成固定规则表的有限接受轨迹。 -/
theorem decode_accept (depth : Nat) (input : Tree) :
    ∀ result, ProjectDecode.formula depth input = some result → Acceptance rules (row 1 depth input) := by
  fun_induction ProjectDecode.formula depth input
  case case1 => intro _ _; exact constant_accept 0 _ (Or.inl rfl)
  case case2 => intro _ _; exact constant_accept 1 _ (Or.inr rfl)
  case case3 | case4 | case12 =>
    intro _ h
    obtain ⟨left, hLeft, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨right, hRight, _⟩ := Option.bind_eq_some_iff.mp hRest
    apply atom_accept
    · simp
    · simp only [SchemaTerm.check, hLeft, Option.isSome_some]
    · simp only [SchemaTerm.check, hRight, Option.isSome_some]
  case case5 depth body ih =>
    intro _ h
    obtain ⟨decoded, hBody, _⟩ := Option.bind_eq_some_iff.mp h
    exact unary_accept 4 depth false body (by simp [rules]) (ih decoded hBody)
  case case10 depth body ih =>
    intro _ h
    obtain ⟨decoded, hBody, _⟩ := Option.bind_eq_some_iff.mp h
    exact unary_accept 9 depth true body (by simp [rules]) (ih decoded hBody)
  case case11 depth body ih =>
    intro _ h
    obtain ⟨decoded, hBody, _⟩ := Option.bind_eq_some_iff.mp h
    exact unary_accept 10 depth true body (by simp [rules]) (ih decoded hBody)
  case case6 depth left right ihLeft ihRight
     | case7 depth left right ihLeft ihRight
     | case8 depth left right ihLeft ihRight
     | case9 depth left right ihLeft ihRight =>
    intro _ h
    obtain ⟨decodedLeft, hLeft, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨decodedRight, hRight, _⟩ := Option.bind_eq_some_iff.mp hRest
    exact binary_accept _ depth left right (by simp [rules])
      (ihLeft decodedLeft hLeft) (ihRight decodedRight hRight)
  case case13 => intro _ h; cases h

theorem check_accept (depth : Nat) (input : Tree) (h : SchemaBody.check depth input = true) :
    Acceptance rules (row 1 depth input) := by
  obtain ⟨result, hResult⟩ := Option.isSome_iff_exists.mp h
  exact decode_accept depth input result hResult

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Body
