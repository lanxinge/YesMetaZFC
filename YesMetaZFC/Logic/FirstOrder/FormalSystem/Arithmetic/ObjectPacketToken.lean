import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectPacketArithmetic

/-! # 规范 varint 前缀的正负规则证书 -/
namespace YesMetaZFC.Automation.ObjectPacket
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem ProofT NatPacket IntrinsicQuotation
open ObjectHorn
set_option autoImplicit false

theorem list_bounds (values : List Nat) (upper : Nat) (h : ∀ v ∈ values, v ≤ upper) :
    ∀ i : Fin values.length, values[i] ≤ upper := fun i => h (values[i]) (List.mem_of_getElem rfl)

theorem token_small_accept (n tail : Nat) (hn : n < 128) :
    Acceptance rules (nodeValue 2 [n, tail, n + 256 * tail]) := by
  have h := accept_head tokenSmall (by simp [rules])
    (fun i : Fin 3 => [n, tail, n + 256 * tail][i])
    (by decide)
    (by intro guard h; have h := List.mem_singleton.mp h; subst guard; exact hn)
    (by intro premise h; have h := List.mem_singleton.mp h; subst premise
        exact affine_accept true n tail (by dsimp [radix]; omega))
  exact h

theorem token_large_accept (digit rest tail : Nat) (hDigit : digit < 128) (hRest : 0 < rest)
    (hRec : Acceptance rules (nodeValue 2 [rest, tail, token rest tail])) :
    Acceptance rules (nodeValue 2 [digit + 128 * rest, tail, digit + 128 + 256 * token rest tail]) := by
  let output := digit + 128 + 256 * token rest tail
  let root := nodeValue 2 [digit + 128 * rest, tail, output]
  have hN : digit + 128 * rest ≤ root := field_le 2 (by simp)
  have hTail : tail ≤ root := field_le 2 (by simp)
  have hOut : output ≤ root := field_le 2 (by simp)
  have hMid : token rest tail ≤ root := by dsimp [output] at hOut; omega
  have h := Acceptance.of_rule (rules := rules) tokenLarge (by simp [rules])
    (fun i : Fin 6 => [digit + 128 * rest, tail, output, digit, rest, token rest tail][i])
    (by
      change ∀ i : Fin 6, [digit + 128 * rest, tail, output, digit, rest, token rest tail][i] ≤ root
      apply list_bounds [digit + 128 * rest, tail, output, digit, rest, token rest tail] root
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    (by
      intro guard hGuard
      dsimp only [tokenLarge] at hGuard
      rcases List.mem_cons.mp hGuard with rfl | hGuard
      · exact hRest
      · have hGuard := List.mem_singleton.mp hGuard; subst guard; exact hDigit)
    (by
      intro premise hPremise
      dsimp only [tokenLarge] at hPremise
      rcases List.mem_cons.mp hPremise with rfl | hPremise
      · exact affine_accept false digit rest hDigit
      · rcases List.mem_cons.mp hPremise with rfl | hPremise
        · exact hRec
        · have hPremise := List.mem_singleton.mp hPremise
          subst premise
          exact affine_accept true (digit + 128) (token rest tail) (by dsimp [radix]; omega))
  exact h

theorem token_accept (n tail : Nat) : Acceptance rules (nodeValue 2 [n, tail, token n tail]) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 128
    · rw [token_small n tail h]; exact token_small_accept n tail h
    · have hRest : 0 < n / 128 := by omega
      have hSmall : n / 128 < n := Nat.div_lt_self (by omega) (by decide)
      have hDigit : n % 128 < 128 := Nat.mod_lt _ (by decide)
      have hAccept := token_large_accept (n % 128) (n / 128) tail hDigit hRest (ih _ hSmall)
      have hValue := token_large (n % 128) (n / 128) tail hDigit hRest
      rw [Nat.mod_add_div] at hValue hAccept
      rwa [hValue]

theorem token_reject (n tail output : Nat) (hBad : token n tail ≠ output) :
    Rejection rules (nodeValue 2 [n, tail, output]) := by
  induction n using Nat.strongRecOn generalizing tail output with
  | ind n ih =>
    apply Rejection.of_tagged heads_tagged 2 [n, tail, output]
    intro rule hRule values _ hHead hGuards
    rw [rulesFor_two] at hRule
    rcases List.mem_cons.mp hRule with rfl | hRule
    · dsimp only [tokenSmall] at values hHead hGuards ⊢
      have h := ((nodeValue_eq_iff 2 2 [n, tail, output] [values 0, values 1, values 2]).mp hHead).2
      simp only [List.cons.injEq, and_true] at h
      have hn := hGuards (.var 0, .literal 128) List.mem_cons_self
      change values 0 < 128 at hn
      refine ⟨node (n := 3) 1 [.var 0, .var 1, .var 2] , List.mem_cons_self, ?_⟩
      apply affine_reject true
      intro hGood
      apply hBad
      rw [h.1, h.2.1, h.2.2, token_small _ _ hn]
      exact hGood.2
    · have hRule := List.mem_singleton.mp hRule
      subst rule
      dsimp only [tokenLarge] at values hHead hGuards ⊢
      have h := ((nodeValue_eq_iff 2 2 [n, tail, output] [values 0, values 1, values 2]).mp hHead).2
      simp only [List.cons.injEq, and_true] at h
      have hRest := hGuards (.literal 0, .var 4) List.mem_cons_self
      have hDigit := hGuards (.var 3, .literal 128) (List.mem_cons_of_mem _ List.mem_cons_self)
      change 0 < values 4 at hRest
      change values 3 < 128 at hDigit
      by_cases hAffine : values 3 + 128 * values 4 = values 0
      · by_cases hToken : token (values 4) (values 1) = values 5
        · refine ⟨node (n := 6) 1 [Expr.addConst 128 (.var 3), .var 5, .var 2] ,
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
          change Rejection rules (nodeValue 1 [values 3 + 128, values 5, values 2])
          apply affine_reject true
          intro hGood
          apply hBad
          rw [h.1, h.2.1, h.2.2, ← hAffine, token_large _ _ _ hDigit hRest, hToken]
          exact hGood.2
        · refine ⟨node (n := 6) 2 [.var 4, .var 1, .var 5] ,
            List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
          exact ih (values 4) (by omega) (values 1) (values 5) hToken
      · refine ⟨node (n := 6) 0 [.var 3, .var 4, .var 0] , List.mem_cons_self, ?_⟩
        exact affine_reject false _ _ _ (fun hGood => hAffine hGood.2)

end YesMetaZFC.Automation.ObjectPacket
