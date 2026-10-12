import YesMetaZFC.Model.SetTheory.Internal.TypeSource
import YesMetaZFC.Model.SetTheory.Internal.TypeGuard
import YesMetaZFC.Model.SetTheory.Internal.TypePoolBounded
import YesMetaZFC.Model.SetTheory.Internal.FiniteSyntax

/-! # 查询程序及原名字列的有限公式

字面编码只记录实际列图和坐标。自然数程序的全称正确性单独保存，
从而既能固定低程序，也能在共同秩段中读取含新常量的原名字列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tt_code0_m {d} (n U z p : Term d) : Formula 1 d := set[d] ⟪∃ N C b,
  ⌜tn_names0_m⌝ₚ(⌜n⌝ₛ, ⌜U⌝ₛ, N) ∧ ⌜num0_m 0⌝ₚ(b) ∧ ⌜fn0_m⌝ₚ(b, N, C) ∧ ⌜kpair0_m⌝ₚ(⌜p⌝ₛ, ⌜z⌝ₛ, C)⟫
derive_free_closed tt_code0_m

def tt_code2_m {d} (n U z p a b : Term d) : Formula 1 d := set[d] ⟪∃ N C l,
  ⌜tn_names0_m⌝ₚ(⌜n⌝ₛ, ⌜U⌝ₛ, N) ∧ ⌜num0_m 2⌝ₚ(l) ∧ ⌜fn0_m⌝ₚ(l, N, C) ∧ ⌜kpair0_m⌝ₚ(⌜p⌝ₛ, ⌜z⌝ₛ, C) ∧
  (∀ i ∈ l, ⌜num0_m 0⌝ₚ(i) → ⌜rd_entry0_m⌝ₚ(i, ⌜a⌝ₛ, C)) ∧
  (∀ i ∈ l, ⌜num0_m 1⌝ₚ(i) → ⌜rd_entry0_m⌝ₚ(i, ⌜b⌝ₛ, C))⟫
derive_free_closed tt_code2_m

def tg_guard_code_m {d} (n κ U l z p : Term d) : Formula 1 d := set[d] ⟪∃ b k C N,
  ⌜KP.succ0_m⌝ₚ(b, ⌜n⌝ₛ) ∧ ⌜KP.succ0_m⌝ₚ(⌜l⌝ₛ, b) ∧ ⌜tn_names0_m⌝ₚ(⌜n⌝ₛ, ⌜U⌝ₛ, N) ∧
  ⌜fn0_m⌝ₚ(⌜l⌝ₛ, N, C) ∧ ⌜kpair0_m⌝ₚ(k, ⌜κ⌝ₛ, ⌜κ⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(⌜p⌝ₛ, ⌜z⌝ₛ, C) ∧
  (∀ i ∈ b, ⌜rd_entry0_m⌝ₚ(i, i, C)) ∧ ⌜rd_entry0_m⌝ₚ(b, k, C)⟫
derive_free_closed tg_guard_code_m

def tg_guard_program0_m : Formula 1 3 :=
  let ω : Term 3 := .bound 0
  let l : Term 3 := .bound 1
  let z : Term 3 := .bound 2
  set[3] ⟪⌜l⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜z⌝ₛ ∈ ⌜ω⌝ₛ ∧
  (∀ ν μ X Y c R f, ⌜v_m kpair_convention_l⌝ₚ(ν, X) → ⌜v_m kpair_convention_l⌝ₚ(μ, Y) →
    ⌜Formula.isSuccessor⌝ₚ(μ, ν) → ⌜ω⌝ₛ ⊆ ν → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
    ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(f, ⌜ω⌝ₛ, Y) →
      (⌜sc_sat_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, c, ⌜z⌝ₛ, f) ↔
        ∀ i y, i ∈ ⌜l⌝ₛ → ⌜rd_entry0_m⌝ₚ(i, y, f) → y ∈ X))⟫
theorem tg_guard_program0_closed_l : tg_guard_program0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_guard_program0_m, Definitional.Formula.FreeClosed]

def tg_guard_program_m {d} (ω l z : Term d) : Formula 1 d :=
  tg_guard_program0_m.bind (Fin.cases ω (Fin.cases l (fun _ => z)))

@[simp] theorem tg_guard_program_closed_l {d} (ω l z : Term d)
    (hw : ω.freeSupport = []) (hl : l.freeSupport = []) (hz : z.freeSupport = []) :
    (tg_guard_program_m ω l z).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hw (Fin.cases hl (fun _ => hz))) _).mpr tg_guard_program0_closed_l

variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP
include hKP

theorem tt_code0_sat_l {d} (ρ : Env M d) (n U z p : Term d) :
    Formula.satisfies ρ (tt_code0_m n U z p) ↔
      Tt_code_d (n.eval ρ) (U.eval ρ) (z.eval ρ) (p.eval ρ) (Fin.elim0 : Fin 0 → M.Domain) := by
  simp only [tt_code0_m, Tt_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tn_names0_sat_l hKP, num0_sat_l hKP.1, fn0_sat_l hKP.1, kpair0_sat_l hKP.1,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨N, C, b, names, hb, fn, pair⟩ => ⟨N, C, b, names, hb, fn, pair, fun i => Fin.elim0 i⟩,
    fun ⟨N, C, b, names, hb, fn, pair, _⟩ => ⟨N, C, b, names, hb, fn, pair⟩⟩

theorem tt_code2_sat_l {d} (ρ : Env M d) (n U z p a b : Term d) :
    Formula.satisfies ρ (tt_code2_m n U z p a b) ↔
      Tt_code_d (n.eval ρ) (U.eval ρ) (z.eval ρ) (p.eval ρ)
        (Fin.cases (a.eval ρ) (fun _ => b.eval ρ) : Fin 2 → M.Domain) := by
  simp only [tt_code2_m, Tt_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, tn_names0_sat_l hKP,
    num0_sat_l hKP.1, fn0_sat_l hKP.1, kpair0_sat_l hKP.1, rd_entry0_sat_l hKP.1,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨N, C, l, names, hl, fn, pair, ha, hb⟩ =>
    ⟨N, C, l, names, hl, fn, pair,
      Fin.cases (fun x hx => ha x (num_lt_l hKP.1 hx hl (by decide)) hx)
        (Fin.cases (fun x hx => hb x (num_lt_l hKP.1 hx hl (by decide)) hx) (fun i => Fin.elim0 i))⟩,
    fun ⟨N, C, l, names, hl, fn, pair, params⟩ =>
      ⟨N, C, l, names, hl, fn, pair, fun x _ => params 0 x, fun x _ => params 1 x⟩⟩

theorem tg_guard_code_sat_l {d} (ρ : Env M d) (n κ U l z p : Term d) :
    Formula.satisfies ρ (tg_guard_code_m n κ U l z p) ↔
      Tg_guard_code_d (n.eval ρ) (κ.eval ρ) (U.eval ρ) (l.eval ρ) (z.eval ρ) (p.eval ρ) := by
  simp only [tg_guard_code_m, Tg_guard_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    KP.succ0_sat_l hKP.1, tn_names0_sat_l hKP, fn0_sat_l hKP.1, kpair0_sat_l hKP.1,
    Formula.satisfies_forallMem_iff, rd_entry0_sat_l hKP.1, Definitional.Term.eval_weaken]
  rfl

theorem tg_guard_program_sat_l {d} (ρ : Env M d) (ω l z : Term d) :
    Formula.satisfies ρ (tg_guard_program_m ω l z) ↔ Tg_guard_program_d I (ω.eval ρ) (l.eval ρ) (z.eval ρ) := by
  simp only [tg_guard_program_m, Formula.satisfies_bind, tg_guard_program0_m, Tg_guard_program_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, v_sat_l I hKP.1, Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_subset_iff, smem_sat_l I, Formula.satisfies_isFunctionFromTo_iff I hKP.1,
    Formula.satisfies_iff_iff, sc_sat_formula_l I hKP.1,
    rd_entry0_sat_l hKP.1, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal
