import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectPacketGraph

/-! # 有界数字与固定进位基数的接受和拒绝证书 -/
namespace YesMetaZFC.Automation.ObjectPacket
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem ProofT NatPacket IntrinsicQuotation
open ObjectHorn
set_option autoImplicit false

def radix (wide : Bool) : Nat := if wide then 256 else 128
def relation (wide : Bool) : Nat := if wide then 1 else 0

theorem radix_pos (wide : Bool) : 0 < radix wide := by cases wide <;> decide

theorem affine_rules (wide : Bool) : rulesFor rules (relation wide) =
    [affineBase (relation wide) (radix wide), affineStep (relation wide) (radix wide)] := by
  cases wide <;> rfl

theorem accept_head (rule : Rule) (hRule : rule ∈ rules) (values : Fin rule.arity → Nat)
    (hVariables : ∀ i, i ∈ rule.head.variables)
    (hGuards : ∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values)
    (hPremises : ∀ premise, premise ∈ rule.premises → Acceptance rules (premise.eval values)) :
    Acceptance rules (rule.head.eval values) :=
  Acceptance.of_rule rule hRule values (fun i => rule.head.variable_le values (hVariables i)) hGuards hPremises

theorem affine_accept (wide : Bool) (digit tail : Nat) (hDigit : digit < radix wide) :
    Acceptance rules (nodeValue (relation wide) [digit, tail, digit + radix wide * tail]) := by
  induction tail with
  | zero =>
    have h := accept_head (affineBase (relation wide) (radix wide))
      (by cases wide <;> simp [relation, radix, rules]) (fun _ => digit)
      (by cases wide <;> decide)
      (by intro guard h; have h := List.mem_singleton.mp h; subst guard; exact hDigit)
      (by intro premise h; exact False.elim (List.not_mem_nil h))
    exact h
  | succ tail ih =>
    have h := accept_head (affineStep (relation wide) (radix wide))
      (by cases wide <;> simp [relation, radix, rules])
      (fun i => if i.val = 0 then digit else if i.val = 1 then tail else digit + radix wide * tail)
      (by cases wide <;> decide)
      (by intro guard h; exact False.elim (List.not_mem_nil h))
      (by intro premise h; have h := List.mem_singleton.mp h; subst premise; exact ih)
    simp only [affineStep, node, Expr.node_eval, Expr.addConst_eval, Expr.eval, List.map_cons, List.map_nil] at h
    change Acceptance rules (nodeValue (relation wide) [digit, tail + 1, (digit + radix wide * tail) + radix wide]) at h
    simpa [Nat.mul_succ, Nat.add_assoc] using h

/-- 数字范围和数值结果均纳入拒绝，不接受超出基数的非规范数字。 -/
theorem affine_reject (wide : Bool) (digit tail output : Nat)
    (hBad : ¬ (digit < radix wide ∧ digit + radix wide * tail = output)) :
    Rejection rules (nodeValue (relation wide) [digit, tail, output]) := by
  induction tail using Nat.strongRecOn generalizing output with
  | ind tail ih =>
    apply Rejection.of_tagged heads_tagged (relation wide) [digit, tail, output]
    intro rule hRule values _ hHead hGuards
    rw [affine_rules] at hRule
    rcases List.mem_cons.mp hRule with rfl | hRule
    · dsimp only [affineBase] at values hHead hGuards ⊢
      have h := ((nodeValue_eq_iff _ _ [digit, tail, output] [values 0, 0, values 0]).mp hHead).2
      simp only [List.cons.injEq, and_true] at h
      have hGuard := hGuards (.var 0, .literal (radix wide)) List.mem_cons_self
      exact False.elim (hBad ⟨h.1.symm ▸ hGuard, by rw [h.2.1]; simpa using h.1.trans h.2.2.symm⟩)
    · have hRule := List.mem_singleton.mp hRule
      subst rule
      dsimp only [affineStep] at values hHead ⊢
      have hHead' : nodeValue (relation wide) [digit, tail, output] =
          nodeValue (relation wide) [values 0, values 1 + 1, values 2 + radix wide] := by
        simpa only [node, Expr.node_eval, List.map_cons, List.map_nil, Expr.eval, Expr.addConst_eval] using hHead
      have h := (nodeValue_eq_iff _ _ _ _).mp hHead' |>.2
      simp only [List.cons.injEq, and_true] at h
      refine ⟨node (n := 3) (relation wide) [.var 0, .var 1, .var 2] , List.mem_cons_self, ?_⟩
      change Rejection rules (nodeValue (relation wide) [values 0, values 1, values 2])
      rw [← h.1]
      apply ih (values 1) (by omega)
      intro hGood
      apply hBad
      refine ⟨hGood.1, ?_⟩
      rw [h.2.1, h.2.2, Nat.mul_succ, ← Nat.add_assoc, hGood.2]

end YesMetaZFC.Automation.ObjectPacket
