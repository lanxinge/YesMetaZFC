import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProjection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectLocalDecision
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectProofTree

/-! # 节点局部表示到递归检查行的封装

根行不调用节点检查。该封装对全部自然数精确实现 rowCheck，
包括零码及非规范外壳，不对图外输入额外作假设。
-/
namespace YesMetaZFC.Automation.ObjectProofRow
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT ProofCode ObjectHorn ObjectCodeProjection
set_option autoImplicit false

abbrev raw {n : Nat} (tag payload : Expr n) : Expr n := .succ (.pair tag payload)
abbrev zeroRule {T : SetTheory} (test : ObjectCheckedTrace.LocalTest T) : ObjectLocalDecision.Rule T where
  arity := 0
  head := .literal 0
  queries := [(test, .literal 0)]
abbrev zeroTagRule {T : SetTheory} (projection test : ObjectCheckedTrace.LocalTest T) : ObjectLocalDecision.Rule T where
  arity := 2
  head := raw (.literal 0) (.var 0)
  queries := [(projection, .node (.literal 2) [raw (.literal 0) (.var 0), .literal 0, .var 1]), (test, .var 1)]
abbrev otherTagRule (T : SetTheory) : ObjectLocalDecision.Rule T where
  arity := 2
  head := raw (.succ (.var 0)) (.var 1)
  queries := []
def rules {T : SetTheory} (projection test : ObjectCheckedTrace.LocalTest T) : List (ObjectLocalDecision.Rule T) :=
  [zeroRule test, zeroTagRule projection test, otherTagRule T]

theorem checked_iff {T : SetTheory} (projection test : ObjectCheckedTrace.LocalTest T)
    (hProjection : ∀ input output, projection.checked (nodeValue 2 [input, 0, output]) = true ↔ field input 0 = output)
    (root : Nat) : ObjectLocalDecision.checked (rules projection test) root = true ↔
      ObjectProofTree.rowCheck test.checked root = true := by
  constructor
  · intro h
    obtain ⟨rule, hRule, h⟩ := List.any_eq_true.mp h
    obtain ⟨values, _, rfl, hQueries⟩ := (rule.checked_iff root).mp h
    simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
    rcases hRule with rfl | rfl | rfl
    · simpa [zeroRule, Expr.eval, ObjectProofTree.rowCheck, tag, field, payload, ObjectCodeProjection.get, ObjectCodeProjection.head, godel_unpair_value] using hQueries
    · dsimp only [zeroTagRule] at values hQueries ⊢
      have hPair : field (godel_pair_value 0 (values 0) + 1) 0 = values 1 ∧ test.checked (values 1) = true := by
        simpa [Expr.eval, hProjection] using hQueries
      simpa [raw, Expr.eval, ObjectProofTree.rowCheck, tag, godel_unpair_value_pair, hPair.1] using hPair.2
    · simp [Expr.eval, ObjectProofTree.rowCheck, tag, godel_unpair_value_pair]
  · intro h
    have accept (rule : ObjectLocalDecision.Rule T) (hRule : rule ∈ rules projection test)
        (values : Fin rule.arity → Nat) (hBound : ∀ i, values i ≤ root)
        (hHead : root = rule.head.eval values)
        (hQueries : ∀ query, query ∈ rule.queries → query.1.checked (query.2.eval values) = true) :
        ObjectLocalDecision.checked (rules projection test) root = true :=
      List.any_eq_true.mpr ⟨rule, hRule, (rule.checked_iff root).mpr ⟨values, hBound, hHead, hQueries⟩⟩
    cases root with
    | zero =>
      apply accept (zeroRule test) (by simp [rules]) Fin.elim0 (fun i => Fin.elim0 i) rfl
      simpa [zeroRule, Expr.eval, ObjectProofTree.rowCheck, tag, field, payload, ObjectCodeProjection.get, ObjectCodeProjection.head, godel_unpair_value] using h
    | succ n =>
      obtain ⟨a, b, hParts⟩ : ∃ a b, godel_unpair_value n = (a, b) := ⟨_, _, rfl⟩
      have hn : n = godel_pair_value a b := by simpa [hParts] using (godel_unpair_value_spec n).symm
      subst n
      cases a with
      | zero =>
        apply accept (zeroTagRule projection test) (by simp [rules])
          (fun i : Fin 2 => [b, field (godel_pair_value 0 b + 1) 0][i])
        · intro i
          cases i using Fin.cases with
          | zero => exact Nat.le_succ_of_le (right_le_godel_pair_value _ _)
          | succ i =>
            have hi : i = 0 := Fin.ext (by omega)
            subst i
            exact ObjectProjection.field_le _ _
        · rfl
        · simpa [zeroTagRule, Expr.eval, hProjection, ObjectProofTree.rowCheck, tag, godel_unpair_value_pair] using h
      | succ a =>
        apply accept (otherTagRule T) (by simp [rules]) (fun i : Fin 2 => [a, b][i])
        · intro i
          exact (otherTagRule T).head.variable_le _ (by cases i using Fin.cases <;> simp [otherTagRule, Expr.variables])
        · rfl
        · intro query hQuery
          cases hQuery

def localTest {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (test : ObjectCheckedTrace.LocalTest T) : ObjectCheckedTrace.LocalTest T :=
  ObjectLocalDecision.localTest C hSuccessor (rules (ObjectProjection.localTest C S hPower hInfinity) test)

theorem localTest_checked {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hSuccessor : ∀ {φ}, successor_operator_theory φ → T φ)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ)
    (test : ObjectCheckedTrace.LocalTest T) :
    (localTest C S hSuccessor hPower hInfinity test).checked = ObjectProofTree.rowCheck test.checked := by
  funext root
  have h := checked_iff (ObjectProjection.localTest C S hPower hInfinity) test (fun input output => ObjectProjection.checked_field_iff input 0 output) root
  change ObjectLocalDecision.checked (rules (ObjectProjection.localTest C S hPower hInfinity) test) root = _
  cases hLeft : ObjectLocalDecision.checked (rules (ObjectProjection.localTest C S hPower hInfinity) test) root <;>
    cases hRight : ObjectProofTree.rowCheck test.checked root <;> simp_all

end YesMetaZFC.Automation.ObjectProofRow
