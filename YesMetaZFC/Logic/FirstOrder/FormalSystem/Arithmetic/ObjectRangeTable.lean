import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornValues

/-! # 带固定前缀的连续自然数表：统一对象图 -/
namespace YesMetaZFC.Automation.ObjectRangeTable
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding IntrinsicQuotation
open ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def range (start : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => start :: range (start + 1) n

theorem range_ofFn (start n : Nat) : range start n = List.ofFn (fun i : Fin n => i.val + start) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [range, List.ofFn_succ, ih, Nat.add_comm, Nat.add_left_comm]

def cons {n : Nat} (head tail : Expr n) : Expr n := .succ (.pair (.literal 1) (.pair head tail))
def prepend {n : Nat} (heads : List Nat) (tail : Expr n) : Expr n :=
  heads.foldr (fun head rest => cons (.literal head) rest) tail

def prefixValue (heads : List Nat) (tail : Nat) : Nat :=
  heads.foldr (fun head rest => ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value head rest) + 1) tail

@[simp] theorem prefix_eval {n : Nat} (heads : List Nat) (tail : Expr n) (env : Fin n → Nat) :
    (prepend heads tail).eval env = prefixValue heads (tail.eval env) := by
  induction heads <;> simp_all [prepend, prefixValue, cons, Expr.eval]

theorem prefix_listValue (heads tail : List Nat) :
    prefixValue heads (listValue tail) = listValue (heads ++ tail) := by
  induction heads <;> simp_all [prefixValue, listValue]

theorem prefix_injective (heads : List Nat) : Function.Injective (prefixValue heads) := by
  intro a b h
  induction heads with
  | nil => exact h
  | cons head rest ih =>
    apply ih
    exact (ProofCode.godel_pair_value_eq_iff.mp
      (ProofCode.godel_pair_value_eq_iff.mp (Nat.add_right_cancel h)).2).2

@[simp] theorem prefix_variables {n : Nat} (heads : List Nat) (tail : Expr n) :
    (prepend heads tail).variables = tail.variables := by
  induction heads <;> simp_all [prepend, cons, Expr.variables]

structure Entry where
  tag : Nat
  start : Nat
  heads : List Nat

def base : Rule where
  arity := 1
  head := .node (.literal 0) [.var 0, .literal 0, .list []]

def step : Rule where
  arity := 3
  head := .node (.literal 0) [.var 0, .succ (.var 1), cons (.var 0) (.var 2)]
  premises := [.node (.literal 0) [.succ (.var 0), .var 1, .var 2]]

def Entry.rule (entry : Entry) : Rule where
  arity := 2
  head := .node (.literal 1) [.literal entry.tag, .var 0, prepend entry.heads (.var 1)]
  premises := [.node (.literal 0) [.literal entry.start, .var 0, .var 1]]

def rules (program : List Entry) : List Rule := base :: step :: program.map Entry.rule

theorem heads_tagged (program : List Entry) (rule : Rule) (h : rule ∈ rules program) : rule.head.tag?.isSome := by
  rcases List.mem_cons.mp h with rfl | h
  · rfl
  rcases List.mem_cons.mp h with rfl | h
  · rfl
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp h
  rfl

@[simp] theorem rulesFor_range (program : List Entry) : rulesFor (rules program) 0 = [base, step] := by
  induction program <;> simp_all [rules, rulesFor, Entry.rule, base, step, Expr.node, Expr.tag?]

@[simp] theorem rulesFor_table (program : List Entry) : rulesFor (rules program) 1 = program.map Entry.rule := by
  induction program <;> simp_all [rules, rulesFor, Entry.rule, base, step, Expr.node, Expr.tag?]

theorem range_accept (program : List Entry) (start n : Nat) :
    Acceptance (rules program) (nodeValue 0 [start, n, listValue (range start n)]) := by
  induction n generalizing start with
  | zero =>
    exact Acceptance.of_rule base (by simp [rules]) (fun _ => start)
      (fun i => base.head.variable_le (fun _ => start) ((by decide : ∀ i, i ∈ base.head.variables) i))
      (by intro g h; cases h) (by intro p h; cases h)
  | succ n ih =>
    exact Acceptance.of_rule step (by simp [rules])
      (fun i => if i.val = 0 then start else if i.val = 1 then n else listValue (range (start + 1) n))
      (fun i => step.head.variable_le (fun i => if i.val = 0 then start else if i.val = 1 then n else listValue (range (start + 1) n)) ((by decide : ∀ i, i ∈ step.head.variables) i))
      (by intro g h; cases h) (by
        intro p hp
        have hp := List.mem_singleton.mp hp
        subst p
        exact ih (start + 1))

theorem range_reject (program : List Entry) (start n output : Nat)
    (hBad : listValue (range start n) ≠ output) :
    Rejection (rules program) (nodeValue 0 [start, n, output]) := by
  induction n using Nat.strongRecOn generalizing start output with
  | ind n ih =>
    apply Rejection.of_tagged (heads_tagged program) 0 [start, n, output]
    intro rule hRule env _ hHead _
    rw [rulesFor_range] at hRule
    rcases List.mem_cons.mp hRule with rfl | hRule
    · dsimp only [base] at env hHead ⊢
      have h := (nodeValue_eq_iff 0 0 [start, n, output] [env 0, 0, listValue []]).mp hHead |>.2
      simp only [List.cons.injEq, and_true] at h
      exact False.elim (hBad (by rw [h.2.1, h.2.2]; rfl))
    · have hRule := List.mem_singleton.mp hRule
      subst rule
      dsimp only [step] at env hHead ⊢
      have h := (nodeValue_eq_iff 0 0 [start, n, output]
        [env 0, env 1 + 1, ProofCode.godel_pair_value 1 (ProofCode.godel_pair_value (env 0) (env 2)) + 1]).mp hHead |>.2
      simp only [List.cons.injEq, and_true] at h
      refine ⟨Expr.node (.literal 0) [.succ (.var 0), .var 1, .var 2] , List.mem_cons_self, ?_⟩
      change Rejection (rules program) (nodeValue 0 [env 0 + 1, env 1, env 2])
      apply ih (env 1) (by omega)
      intro hGood
      apply hBad
      rw [h.1, h.2.1, range, listValue, hGood, h.2.2]

theorem table_accept (program : List Entry) (entry : Entry) (hEntry : entry ∈ program) (n : Nat) :
    Acceptance (rules program) (nodeValue 1 [entry.tag, n, listValue (entry.heads ++ range entry.start n)]) := by
  have h := Acceptance.of_rule (rules := rules program) entry.rule
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry, hEntry, rfl⟩)))
    (fun i : Fin 2 => if i.val = 0 then n else listValue (range entry.start n))
    (fun i => entry.rule.head.variable_le
      (fun i : Fin 2 => if i.val = 0 then n else listValue (range entry.start n)) (by
        dsimp only [Entry.rule] at i ⊢
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl <;> simp only [Expr.node, Expr.list, Expr.variables, prefix_variables, List.nil_append, List.append_nil]
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self))
    (by intro g hg; cases hg) (by
      intro p hp
      have hp := List.mem_singleton.mp hp
      subst p
      exact range_accept program entry.start n)
  simpa [Entry.rule, Expr.eval, prefix_listValue] using h

/-- 未知标签、错误表码和非列表数码均由同一接口排除。 -/
theorem table_reject (program : List Entry) (tag n output : Nat)
    (hBad : ∀ entry, entry ∈ program → entry.tag = tag →
      listValue (entry.heads ++ range entry.start n) ≠ output) :
    Rejection (rules program) (nodeValue 1 [tag, n, output]) := by
  apply Rejection.of_tagged (heads_tagged program) 1 [tag, n, output]
  intro rule hRule env _ hHead _
  rw [rulesFor_table] at hRule
  obtain ⟨entry, hEntry, rfl⟩ := List.mem_map.mp hRule
  dsimp only [Entry.rule] at env hHead ⊢
  have hHead' : nodeValue 1 [tag, n, output] = nodeValue 1 [entry.tag, env 0, prefixValue entry.heads (env 1)] := by
    simpa [Expr.eval] using hHead
  have h := (nodeValue_eq_iff 1 1 _ _).mp hHead' |>.2
  simp only [List.cons.injEq, and_true] at h
  refine ⟨Expr.node (.literal 0) [.literal entry.start, .var 0, .var 1] , List.mem_cons_self, ?_⟩
  change Rejection (rules program) (nodeValue 0 [entry.start, env 0, env 1])
  apply range_reject
  intro hGood
  apply hBad entry hEntry h.1.symm
  rw [← prefix_listValue, h.2.1, hGood, h.2.2]

def condition (program : List Entry) {bound free : SetContext} (tag n output : SetTerm bound free) : SetFormula bound free :=
  ObjectHorn.condition (rules program) (IntrinsicQuotation.node 1 [tag, n, output])

theorem condition_delta0 (program : List Entry) {bound free : SetContext} (tag n output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition program tag n output) := ObjectHorn.condition_delta0 _ _

end YesMetaZFC.Automation.ObjectRangeTable
