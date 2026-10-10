import YesMetaZFC.SetTheory.InnerModel.Computation.Decision

/-! # 原 Δ₀ 公式到集合程序的可执行编译

解析器读取实际语法，拒绝自由项及无界量词。总性证书只排除解析失败分支，
不从 Prop 中选择程序。成员测试、联结和有界量词最终都降为集合运算。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u

def cp_term_l {n} : Term n → Option (Fin n)
  | .bound i => some i
  | .free _ => none

def cp_unlift_l {n} : Term (n + 1) → Option (Fin n)
  | .bound ⟨0, _⟩ => none
  | .bound ⟨i + 1, h⟩ => some ⟨i, Nat.lt_of_succ_lt_succ h⟩
  | .free _ => none

@[simp] theorem cp_unlift_bound_l {n} (i : Fin n) : cp_unlift_l (Term.bound i).weaken = some i := rfl

def cp_parse_l : {n : Nat} → Formula 1 n → Option (Cp_test n)
  | _, .falsum => some .falsum
  | _, .truth => some .truth
  | _, .mem s t => do return .mem (← cp_term_l s) (← cp_term_l t)
  | _, .atom k _ a => do
      let p ← cp_term_l (a.get 0)
      let q ← cp_term_l (a.get 1)
      return match k with | .extensionalEq => .eq p q | .subset => .subset p q
  | _, .neg φ => (cp_parse_l φ).map Cp_test.neg
  | _, .conj φ ψ => do return .conj (← cp_parse_l φ) (← cp_parse_l ψ)
  | _, .disj φ ψ => do return .disj (← cp_parse_l φ) (← cp_parse_l ψ)
  | _, .imp φ ψ => do return .imp (← cp_parse_l φ) (← cp_parse_l ψ)
  | _, .iff φ ψ => do return .iff (← cp_parse_l φ) (← cp_parse_l ψ)
  | _, .forallE (.imp (.mem (.bound ⟨0, _⟩) t) φ) => do
      let i ← cp_unlift_l t
      return .all i (← cp_parse_l φ)
  | _, .existsE (.conj (.mem (.bound ⟨0, _⟩) t) φ) => do
      let i ← cp_unlift_l t
      return .any i (← cp_parse_l φ)
  | _, .forallE _ | _, .existsE _ => none

theorem cp_term_correct_l {n} (t : Term n) (ht : t.freeSupport = []) :
    ∃ p, cp_term_l t = some p ∧ ∀ (M : Structure.{u}) (ρ : Env M n), Cp_eval_d (.var p) ρ (t.eval ρ) := by
  cases t with
  | bound i => exact ⟨i, rfl, fun _ _ => rfl⟩
  | free i => cases ht

theorem cp_parse_correct_l {n} {φ : Formula 1 n} (hd : φ.IsDelta0) (hc : φ.FreeClosed) :
    ∃ p, cp_parse_l φ = some p ∧ ∀ (M : Structure.{u}), M.Models KP → ∀ ρ : Env M n,
      Cp_decides_d (cp_test_code_l p) ρ (Formula.satisfies ρ φ) := by
  induction hd with
  | falsum => exact ⟨.falsum, rfl, fun _ _ ρ => (cp_zero_bit_l ρ).congr_l (Formula.satisfies_falsum_iff ρ).symm⟩
  | truth => exact ⟨.truth, rfl, fun _ hKP ρ => (cp_one_bit_l hKP ρ).congr_l (Formula.satisfies_truth_iff ρ).symm⟩
  | mem s t =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p, hp, hs⟩ := cp_term_correct_l s hc.1
    obtain ⟨q, hq, ht⟩ := cp_term_correct_l t hc.2
    exact ⟨.mem p q, by simp [cp_parse_l, hp, hq], fun M hKP ρ =>
      (cp_member_bit_l hKP (hs M ρ) (ht M ρ)).congr_l (Formula.satisfies_mem_iff ρ s t).symm⟩
  | atom k hk a =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p, hp, hs⟩ := cp_term_correct_l (a.get 0) (hc 0)
    obtain ⟨q, hq, ht⟩ := cp_term_correct_l (a.get 1) (hc 1)
    cases k with
    | subset =>
      exact ⟨.subset p q, by simp [cp_parse_l, hp, hq], fun M hKP ρ =>
        (cp_subset_bit_l hKP (hs M ρ) (ht M ρ)).congr_l (Formula.satisfies_atom_subset_iff ρ hk a).symm⟩
    | extensionalEq =>
      refine ⟨.eq p q, by simp [cp_parse_l, hp, hq], fun M hKP ρ => ?_⟩
      apply (cp_equal_bit_l hKP (hs M ρ) (ht M ρ)).congr_l
      rw [Formula.satisfies_atom_extensionalEq_iff]
      exact ⟨fun he => he ▸ (fun _ => Iff.rfl), hKP.1.eq_of_same_members _ _⟩
  | neg h ih =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p, hp, ht⟩ := ih hc
    exact ⟨.neg p, by simp [cp_parse_l, hp], fun M hKP ρ =>
      (cp_not_bit_l hKP (ht M hKP ρ)).congr_l (Formula.satisfies_neg_iff ρ _).symm⟩
  | conj h k ih jh =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p, hp, ht⟩ := ih hc.1
    obtain ⟨q, hq, hs⟩ := jh hc.2
    exact ⟨.conj p q, by simp [cp_parse_l, hp, hq], fun M hKP ρ =>
      (cp_and_bit_l hKP (ht M hKP ρ) (hs M hKP ρ)).congr_l (Formula.satisfies_conj_iff ρ _ _).symm⟩
  | disj h k ih jh =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p, hp, ht⟩ := ih hc.1
    obtain ⟨q, hq, hs⟩ := jh hc.2
    exact ⟨.disj p q, by simp [cp_parse_l, hp, hq], fun M hKP ρ =>
      (cp_or_bit_l hKP (ht M hKP ρ) (hs M hKP ρ)).congr_l (Formula.satisfies_disj_iff ρ _ _).symm⟩
  | imp h k ih jh =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p, hp, ht⟩ := ih hc.1
    obtain ⟨q, hq, hs⟩ := jh hc.2
    exact ⟨.imp p q, by simp [cp_parse_l, hp, hq], fun M hKP ρ =>
      (cp_imp_bit_l hKP (ht M hKP ρ) (hs M hKP ρ)).congr_l (Formula.satisfies_imp_iff ρ _ _).symm⟩
  | iff h k ih jh =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p, hp, ht⟩ := ih hc.1
    obtain ⟨q, hq, hs⟩ := jh hc.2
    exact ⟨.iff p q, by simp [cp_parse_l, hp, hq], fun M hKP ρ =>
      (cp_iff_bit_l hKP (ht M hKP ρ) (hs M hKP ρ)).congr_l (Formula.satisfies_iff_iff ρ _ _).symm⟩
  | forallMem t h ih =>
    have hc := Formula.forallMem_freeClosed t _ |>.mp hc
    obtain ⟨p, hp, ht⟩ := ih hc.2
    cases t with
    | free i => cases hc.1
    | bound i =>
      refine ⟨.all i p, by
        change (do let q ← cp_parse_l _; pure (Cp_test.all i q)) = _
        simp [hp], fun M hKP ρ => ?_⟩
      apply (cp_not_bit_l hKP (cp_bunion_bit_l hKP (q := cp_not_l (cp_test_code_l p)) (show Cp_eval_d (.var i) ρ (ρ.bound i) from rfl)
        (fun z _ => cp_not_bit_l hKP (ht M hKP (ρ.push z))))).congr_l
      rw [Formula.satisfies_forallMem_iff]
      exact ⟨fun hn z hz => Classical.byContradiction (fun h => hn ⟨z, hz, h⟩), fun h ⟨z, hz, hn⟩ => hn (h z hz)⟩
  | existsMem t h ih =>
    have hc := Formula.existsMem_freeClosed t _ |>.mp hc
    obtain ⟨p, hp, ht⟩ := ih hc.2
    cases t with
    | free i => cases hc.1
    | bound i =>
      exact ⟨.any i p, by
        change (do let q ← cp_parse_l _; pure (Cp_test.any i q)) = _
        simp [hp], fun M hKP ρ =>
        (cp_bunion_bit_l hKP (show Cp_eval_d (.var i) ρ (ρ.bound i) from rfl) (fun z _ => ht M hKP (ρ.push z))).congr_l
          (Formula.satisfies_existsMem_iff ρ (.bound i) _).symm⟩

/-- 判定指令经公式后端再解析，逐项恢复原指令。 -/
theorem cp_parse_test_l {n} (p : Cp_test n) : cp_parse_l (cp_test_formula_l p) = some p := by
  induction p with
  | falsum | truth | mem i j => rfl
  | eq i j | subset i j => rfl
  | neg p ih => simp [cp_test_formula_l, cp_parse_l, ih]
  | conj p q ih jh | disj p q ih jh | imp p q ih jh | iff p q ih jh =>
    simp [cp_test_formula_l, cp_parse_l, ih, jh]
  | all i p ih =>
    change (do let q ← cp_parse_l (cp_test_formula_l p); pure (Cp_test.all i q)) = _
    simp [ih]
  | any i p ih =>
    change (do let q ← cp_parse_l (cp_test_formula_l p); pure (Cp_test.any i q)) = _
    simp [ih]

/-- 解析总性只作语法归纳，不消费集合论公理或模型存在性。 -/
theorem cp_parse_some_l {n} {φ : Formula 1 n} (hd : φ.IsDelta0) (hc : φ.FreeClosed) : (cp_parse_l φ).isSome := by
  induction hd with
  | falsum | truth => rfl
  | mem s t =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p, hp, _⟩ := cp_term_correct_l.{0} s hc.1
    obtain ⟨q, hq, _⟩ := cp_term_correct_l.{0} t hc.2
    simp [cp_parse_l, hp, hq]
  | atom k hk a =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p, hp, _⟩ := cp_term_correct_l.{0} (a.get 0) (hc 0)
    obtain ⟨q, hq, _⟩ := cp_term_correct_l.{0} (a.get 1) (hc 1)
    simp [cp_parse_l, hp, hq]
  | neg h ih =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (ih hc)
    simp [cp_parse_l, hp]
  | conj h k ih jh | disj h k ih jh | imp h k ih jh | iff h k ih jh =>
    simp only [Definitional.Formula.FreeClosed] at hc
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (ih hc.1)
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (jh hc.2)
    simp [cp_parse_l, hp, hq]
  | forallMem t h ih =>
    have hc := Formula.forallMem_freeClosed t _ |>.mp hc
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (ih hc.2)
    cases t with
    | free i => cases hc.1
    | bound i =>
      change (do let q ← cp_parse_l _; pure (Cp_test.all i q)).isSome
      simp [hp]
  | existsMem t h ih =>
    have hc := Formula.existsMem_freeClosed t _ |>.mp hc
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (ih hc.2)
    cases t with
    | free i => cases hc.1
    | bound i =>
      change (do let q ← cp_parse_l _; pure (Cp_test.any i q)).isSome
      simp [hp]

def cp_delta_l {n} (φ : Delta0UnarySchema n) : Cp_code (n + 1) :=
  cp_test_code_l ((cp_parse_l φ.body).get (cp_parse_some_l φ.delta0 φ.freeClosed))

theorem cp_delta_correct_l {M : Structure.{u}} (hKP : M.Models KP) {n} (φ : Delta0UnarySchema n) (ρ : Env M n)
    (x y : M.Domain) : Cp_eval_d (cp_delta_l φ) (ρ.push x) y ↔ Cp_bit_d (φ.toUnarySchema.denote ρ x) y := by
  obtain ⟨p, hp, h⟩ := cp_parse_correct_l φ.delta0 φ.freeClosed
  have he : cp_delta_l φ = cp_test_code_l p := by simp [cp_delta_l, hp]
  rw [he]
  exact cp_decide_iff_l hKP (h M hKP (ρ.push x)) y

/-- Δ₀ 反向编译的往返性质是程序语法的相等，而不只是外延等价。 -/
theorem cp_delta_roundtrip_l {n} (p : Cp_test (n + 1)) : cp_delta_l (cp_test_schema_l p) = cp_test_code_l p := by
  simp only [cp_delta_l, cp_test_schema_l, cp_parse_test_l, Option.get_some]

theorem cp_test_sat_l {M : Structure.{u}} (hKP : M.Models KP) {n} (p : Cp_test (n + 1))
    (ρ : Env M n) (x y : M.Domain) :
    Cp_eval_d (cp_test_code_l p) (ρ.push x) y ↔ Cp_bit_d ((cp_test_schema_l p).toUnarySchema.denote ρ x) y := by
  rw [← cp_delta_roundtrip_l p]
  exact cp_delta_correct_l hKP (cp_test_schema_l p) ρ x y

end YesMetaZFC.SetTheory.InnerModel
