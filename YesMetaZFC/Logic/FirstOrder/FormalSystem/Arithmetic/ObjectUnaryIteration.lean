import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornValues

/-! # 固定一元树构造的任意次迭代及对象证书 -/
namespace YesMetaZFC.Automation.ObjectUnaryIteration
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT QuineEncoding NatPacket IntrinsicQuotation
open ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def value (tag : Nat) : Nat → Nat → Nat
  | 0, input => input
  | count + 1, input => nodeValue tag [value tag count input]

def tree (tag : Nat) : Nat → Tree → Tree
  | 0, input => input
  | count + 1, input => .node tag [tree tag count input]

theorem tree_value (tag count : Nat) (input : Tree) :
    treeValue (tree tag count input) = value tag count (treeValue input) := by
  induction count <;> simp_all [tree, value]

theorem tree_succ_right (tag count : Nat) (input : Tree) :
    tree tag count (.node tag [input]) = tree tag (count + 1) input := by
  induction count <;> simp_all [tree]

def base : Rule where
  arity := 2
  head := .node (.literal 0) [.var 0, .literal 0, .var 1, .var 1]
  guards := []
  premises := []

def step : Rule where
  arity := 4
  head := .node (.literal 0) [.var 0, .succ (.var 1), .var 2, .node (.var 0) [.var 3]]
  guards := []
  premises := [.node (.literal 0) [.var 0, .var 1, .var 2, .var 3]]

def rules : List Rule := [base, step]
def row (tag count input output : Nat) : Nat := nodeValue 0 [tag, count, input, output]

private theorem head_variables (rule : Rule) (h : rule ∈ rules) :
    ∀ i, i ∈ rule.head.variables := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

private theorem accept_rule (rule : Rule) (hRule : rule ∈ rules) (values : Fin rule.arity → Nat)
    (hPremises : ∀ premise, premise ∈ rule.premises → Acceptance rules (premise.eval values)) :
    Acceptance rules (rule.head.eval values) := by
  apply Acceptance.of_rule rule hRule values
    (fun i => rule.head.variable_le values (head_variables rule hRule i))
  · rcases (show rule = base ∨ rule = step by simpa [rules] using hRule) with rfl | rfl
    all_goals intro guard h; exact False.elim (List.not_mem_nil h)
  · exact hPremises

theorem accept (tag count input : Nat) : Acceptance rules (row tag count input (value tag count input)) := by
  induction count with
  | zero =>
    have h := accept_rule base (by simp [rules]) (fun i => if i.val = 0 then tag else input)
      (by intro premise h; exact False.elim (List.not_mem_nil h))
    simpa [base, row, value, Expr.eval] using h
  | succ count ih =>
    have h := accept_rule step (by simp [rules])
      (fun i => if i.val = 0 then tag else if i.val = 1 then count
        else if i.val = 2 then input else value tag count input) (by
          intro premise h
          have h := List.mem_singleton.mp h
          subst premise
          exact ih)
    exact h

/-- 输出数值完全任意；匹配后继头时才产生严格较小层数的拒绝前提。 -/
theorem reject (tag count input output : Nat) (hBad : value tag count input ≠ output) :
    Rejection rules (row tag count input output) := by
  induction count using Nat.strongRecOn generalizing tag input output with
  | ind count ih =>
    apply Rejection.of_rule
    intro rule hRule values _ hHead _
    simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
    rcases hRule with rfl | rfl
    · dsimp only [base] at values hHead ⊢
      have h := ((nodeValue_eq_iff 0 0 [tag, count, input, output]
        [values 0, 0, values 1, values 1]).mp hHead).2
      simp only [List.cons.injEq, and_true] at h
      exact False.elim (hBad (by rw [h.2.1]; exact h.2.2.1.trans h.2.2.2.symm))
    · dsimp only [step] at values hHead ⊢
      have h := ((nodeValue_eq_iff 0 0 [tag, count, input, output]
        [values 0, values 1 + 1, values 2, nodeValue (values 0) [values 3]]).mp hHead).2
      simp only [List.cons.injEq, and_true] at h
      refine ⟨Expr.node (.literal 0) [.var 0, .var 1, .var 2, .var 3] , List.mem_cons_self, ?_⟩
      change Rejection rules (row (values 0) (values 1) (values 2) (values 3))
      apply ih (values 1) (by omega)
      intro hGood
      apply hBad
      rw [h.1, h.2.1, h.2.2.1, h.2.2.2, value, hGood]

def condition {bound free : SetContext} (tag count input output : SetTerm bound free) : SetFormula bound free :=
  ObjectHorn.condition rules (IntrinsicQuotation.node 0 [tag, count, input, output])

theorem condition_delta0 {bound free : SetContext} (tag count input output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition tag count input output) := ObjectHorn.condition_delta0 _ _

theorem positive {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (tag count input output : Nat) (h : value tag count input = output) :
    Derives T [] (condition (numₘ(tag)) (numₘ(count)) (numₘ(input)) (numₘ(output) : Code)) := by
  obtain ⟨rows, hRoot, hRows⟩ := h ▸ accept tag count input
  exact ObjectHorn.transport rules (FirstOrder.Derives.eq_symm
    (node_evaluate C 0 [tag, count, input, output]))
    (ObjectHorn.positive C S hPower hInfinity rules _ rows hRoot hRows)

theorem negative {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (tag count input output : Nat) (h : value tag count input ≠ output) :
    Derives T [] (¬ₘ condition (numₘ(tag)) (numₘ(count)) (numₘ(input)) (numₘ(output) : Code)) :=
  ObjectHorn.transport_negative rules (FirstOrder.Derives.eq_symm
    (node_evaluate C 0 [tag, count, input, output])) (ObjectHorn.negative C A (reject tag count input output h))

private theorem tree_arguments {T : SetTheory} (C : CertificateCore T) (tag count : Nat)
    (input output : Tree) : Derives T []
    (IntrinsicQuotation.node 0 [numₘ(tag), numₘ(count), numₘ(treeValue input), numₘ(treeValue output)] ≐ₘ
      IntrinsicQuotation.node 0 [numₘ(tag), numₘ(count), IntrinsicQuotation.tree input, IntrinsicQuotation.tree output]) :=
  node_congr 0 (.cons (Metatheory.Derives.equality_refl _) (.cons (Metatheory.Derives.equality_refl _)
    (.cons (FirstOrder.Derives.eq_symm (tree_evaluate C input))
      (.cons (FirstOrder.Derives.eq_symm (tree_evaluate C output)) .nil))))

theorem positive_at_tree {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (tag count : Nat) (input output : Tree) (h : tree tag count input = output) :
    Derives T [] (condition (numₘ(tag)) (numₘ(count)) (IntrinsicQuotation.tree input) (IntrinsicQuotation.tree output)) :=
  ObjectHorn.transport rules (tree_arguments C tag count input output)
    (positive C S hPower hInfinity tag count _ _ ((tree_value tag count input).symm.trans (congrArg treeValue h)))

theorem negative_at_tree {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (tag count : Nat) (input output : Tree) (h : tree tag count input ≠ output) :
    Derives T [] (¬ₘ condition (numₘ(tag)) (numₘ(count)) (IntrinsicQuotation.tree input) (IntrinsicQuotation.tree output)) :=
  ObjectHorn.transport_negative rules (tree_arguments C tag count input output)
    (negative C A tag count _ _ (fun hValue => h (treeValue_injective ((tree_value tag count input).trans hValue))))

end YesMetaZFC.Automation.ObjectUnaryIteration
