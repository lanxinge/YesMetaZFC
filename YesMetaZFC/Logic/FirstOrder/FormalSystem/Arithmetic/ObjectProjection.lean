import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornLocal
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCodeProjection

/-! # 任意自然数的标签和字段投影表示

投影保留原局部检查器对非规范外壳的实际行为。零码单列处理，
其余自然数由配数的双向逆性质分解；不预先假定输入是树或列表。
-/
namespace YesMetaZFC.Automation.ObjectProjection
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding ProofCode
open ObjectHorn ObjectCodeProjection
set_option autoImplicit false

abbrev node {n : Nat} (tag : Nat) (fields : List (Expr n)) : Expr n := .node (.literal tag) fields
abbrev raw {n : Nat} (tag payload : Expr n) : Expr n := .succ (.pair tag payload)
abbrev tagZero : Rule where
  arity := 0
  head := node 0 [.literal 0, .literal 0]
abbrev tagPositive : Rule where
  arity := 2
  head := node 0 [raw (.var 0) (.var 1), .var 0]
abbrev getZero : Rule where
  arity := 1
  head := node 1 [.literal 0, .var 0, .literal 0]
abbrev getHead : Rule where
  arity := 3
  head := node 1 [raw (.var 0) (.pair (.var 1) (.var 2)), .literal 0, .var 1]
abbrev getTail : Rule where
  arity := 5
  head := node 1 [raw (.var 0) (.pair (.var 1) (.var 2)), .succ (.var 3), .var 4]
  premises := [node 1 [.var 2, .var 3, .var 4]]
abbrev fieldZero : Rule where
  arity := 1
  head := node 2 [.literal 0, .var 0, .literal 0]
abbrev fieldPositive : Rule where
  arity := 4
  head := node 2 [raw (.var 0) (.var 1), .var 2, .var 3]
  premises := [node 1 [.var 1, .var 2, .var 3]]

def rules : List Rule := [tagZero, tagPositive, getZero, getHead, getTail, fieldZero, fieldPositive]
def rank (row : Nat) : Nat := if tag row = 0 then 0 else field row 0 + field row 1 + (if tag row = 2 then 1 else 0)

private theorem tail_lt (tag first rest : Nat) : rest < godel_pair_value tag (godel_pair_value first rest) + 1 :=
  Nat.lt_succ_of_le (Nat.le_trans (right_le_godel_pair_value _ _) (right_le_godel_pair_value _ _))

theorem descending : Descending rules rank := by
  intro rule hRule values _ _ premise hPremise
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [tagZero, tagPositive, getZero, getHead, getTail, fieldZero, fieldPositive] at values premise hPremise ⊢
  all_goals first
    | exact False.elim (List.not_mem_nil hPremise)
    | obtain rfl := List.mem_singleton.mp hPremise
  all_goals simp only [node, raw, Expr.node_eval, Expr.eval, List.map_cons, List.map_nil, rank,
    tag_node, field_node, get_zero, get_succ, Nat.reduceEqDiff, if_false, if_true, Nat.add_zero]
  · have h := tail_lt (values 0) (values 1) (values 2)
    omega
  · have h := right_le_godel_pair_value (values 0) (values 1)
    omega

private def Meaning (row : Nat) : Prop :=
  match tag row with
  | 0 => tag (field row 0) = field row 1
  | 1 => ObjectCodeProjection.get (field row 0) (field row 1) = field row 2
  | 2 => field (field row 0) (field row 1) = field row 2
  | _ => False

@[simp] theorem get_zero_input (index : Nat) : ObjectCodeProjection.get 0 index = 0 := by
  induction index with
  | zero => rfl
  | succ index ih => exact ih

private theorem rule_sound (rule : Rule) (hRule : rule ∈ rules) (values : Fin rule.arity → Nat)
    (hPremises : ∀ premise, premise ∈ rule.premises → Meaning (premise.eval values)) :
    Meaning (rule.head.eval values) := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [tagZero, tagPositive, getZero, getHead, getTail, fieldZero, fieldPositive] at values hPremises ⊢
  all_goals simp [Meaning, Expr.eval] at hPremises ⊢
  all_goals first | rfl | exact get_zero_input _ | skip
  · simp [tag, godel_unpair_value_pair]
  · simp [ObjectCodeProjection.get, ObjectCodeProjection.head, payload, godel_unpair_value_pair]
  · simpa [ObjectCodeProjection.get, ObjectCodeProjection.tail, payload, godel_unpair_value_pair] using hPremises
  · simpa [field, payload, godel_unpair_value_pair] using hPremises

theorem head_variables (rule : Rule) (hRule : rule ∈ rules) : ∀ i, i ∈ rule.head.variables := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem accept_rule (rule : Rule) (hRule : rule ∈ rules) (values : Fin rule.arity → Nat)
    (hPremises : ∀ premise, premise ∈ rule.premises → Acceptance rules (premise.eval values)) :
    Acceptance rules (rule.head.eval values) := by
  apply Acceptance.of_rule rule hRule values
    (fun i => rule.head.variable_le values (head_variables rule hRule i))
  · intro guard hGuard
    simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
    rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases hGuard
  · exact hPremises

private theorem tag_accept (input : Nat) : Acceptance rules (nodeValue 0 [input, tag input]) := by
  cases input with
  | zero => exact accept_rule tagZero (by simp [rules]) Fin.elim0 (by intro p h; cases h)
  | succ n =>
    have h := accept_rule tagPositive (by simp [rules])
      (fun i : Fin 2 => [(godel_unpair_value n).1, (godel_unpair_value n).2][i]) (by intro p h; cases h)
    change Acceptance rules (nodeValue 0 [godel_pair_value (godel_unpair_value n).1 (godel_unpair_value n).2 + 1, (godel_unpair_value n).1]) at h
    simpa [tag, godel_unpair_value_spec] using h

private theorem get_accept (input index : Nat) : Acceptance rules (nodeValue 1 [input, index, ObjectCodeProjection.get input index]) := by
  induction index generalizing input with
  | zero =>
    cases input with
    | zero => exact accept_rule getZero (by simp [rules]) (fun _ => 0) (by intro p h; cases h)
    | succ n =>
      have h := accept_rule getHead (by simp [rules])
        (fun i : Fin 3 => [(godel_unpair_value n).1, (godel_unpair_value (godel_unpair_value n).2).1, (godel_unpair_value (godel_unpair_value n).2).2][i])
        (by intro p h; cases h)
      simpa [getHead, node, raw, Expr.eval, godel_unpair_value_spec, ObjectCodeProjection.get, ObjectCodeProjection.head, payload] using h
  | succ index ih =>
    cases input with
    | zero =>
      rw [get_zero_input]
      exact accept_rule getZero (by simp [rules]) (fun _ => index + 1) (by intro p h; cases h)
    | succ n =>
      let rest := (godel_unpair_value (godel_unpair_value n).2).2
      have h := accept_rule getTail (by simp [rules])
        (fun i : Fin 5 => [(godel_unpair_value n).1, (godel_unpair_value (godel_unpair_value n).2).1, rest, index, ObjectCodeProjection.get rest index][i])
        (by intro p h; obtain rfl := List.mem_singleton.mp h; exact ih rest)
      change Acceptance rules (nodeValue 1 [godel_pair_value (godel_unpair_value n).1
        (godel_pair_value (godel_unpair_value (godel_unpair_value n).2).1 rest) + 1,
        index + 1, ObjectCodeProjection.get rest index]) at h
      simpa [godel_unpair_value_spec, ObjectCodeProjection.get, ObjectCodeProjection.tail, payload, rest] using h

private theorem field_accept (input index : Nat) : Acceptance rules (nodeValue 2 [input, index, field input index]) := by
  cases input with
  | zero =>
    have h : field 0 index = 0 := get_zero_input index
    rw [h]
    exact accept_rule fieldZero (by simp [rules]) (fun _ => index) (by intro p h; cases h)
  | succ n =>
    have h := accept_rule fieldPositive (by simp [rules])
      (fun i : Fin 4 => [(godel_unpair_value n).1, (godel_unpair_value n).2, index, ObjectCodeProjection.get (godel_unpair_value n).2 index][i])
      (by intro p h; obtain rfl := List.mem_singleton.mp h; exact get_accept _ _)
    change Acceptance rules (nodeValue 2 [godel_pair_value (godel_unpair_value n).1 (godel_unpair_value n).2 + 1,
      index, ObjectCodeProjection.get (godel_unpair_value n).2 index]) at h
    simpa [godel_unpair_value_spec, field, payload] using h

theorem checked_tag_iff (input output : Nat) :
    check rules rank (nodeValue 0 [input, output]) = true ↔ tag input = output := by
  constructor
  · intro h
    have h := check_sound rules rank descending Meaning (fun rule hr values _ _ hp => rule_sound rule hr values hp) _ h
    simpa [Meaning] using h
  · intro h
    rw [← h]
    exact acceptance_check rules rank descending _ (tag_accept input)

theorem checked_field_iff (input index output : Nat) :
    check rules rank (nodeValue 2 [input, index, output]) = true ↔ field input index = output := by
  constructor
  · intro h
    have h := check_sound rules rank descending Meaning (fun rule hr values _ _ hp => rule_sound rule hr values hp) _ h
    simpa [Meaning] using h
  · intro h
    rw [← h]
    exact acceptance_check rules rank descending _ (field_accept input index)

/-- 字段见证不超过原数码，可使用节点本身作为有限模式的存在界。 -/
theorem field_le (input index : Nat) : field input index ≤ input := by
  have hGet : ∀ input index, ObjectCodeProjection.get input index ≤ input := by
    intro input index
    induction index generalizing input with
    | zero =>
      exact Nat.le_trans (godel_unpair_value_left_le _) (Nat.le_trans (godel_unpair_value_right_le _) (Nat.sub_le _ _))
    | succ index ih =>
      exact Nat.le_trans (ih (ObjectCodeProjection.tail input)) (Nat.le_trans (godel_unpair_value_right_le _)
        (Nat.le_trans (godel_unpair_value_right_le _) (Nat.sub_le _ _)))
  exact Nat.le_trans (hGet (payload input) index) (Nat.le_trans (godel_unpair_value_right_le _) (Nat.sub_le _ _))

def localTest {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ) : ObjectCheckedTrace.LocalTest T :=
  ObjectHorn.localTest C S hPower hInfinity rules rank descending

end YesMetaZFC.Automation.ObjectProjection
