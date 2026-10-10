import YesMetaZFC.Model.Forcing.Internal.Forcing.Congruence
import YesMetaZFC.Model.Forcing.Internal.Check.Forcing

/-! # 有限地参数的 check 赋值及力迫规则

自由闭合正文只消费有限 bound 参数。默认自由值用一个实际空名称补齐，避免调用端
额外提供无限自由赋值的名称性；基条件交换由已有共同加强处的 check 等号给出。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem check_env_l (hZF : M.Models ZF) {n b} (hb : M.mem b B) (v : Fin n → M.Domain) :
    ∃ ρ : Env M n, (∀ i, Check_d M b (v i) (ρ.bound i)) ∧
      ∀ t : Term n, Name_d M B (t.eval ρ) := by
  obtain ⟨s, hs⟩ := Classical.axiomOfChoice (fun i => zf_check_l M hZF hb (v i))
  obtain ⟨t, _, ht, _⟩ := zf_check_l M hZF hb b
  refine ⟨⟨s, fun _ => t⟩, fun i => (hs i).1, ?_⟩
  intro a
  cases a with
  | free _ => exact ht
  | bound i => exact (hs i).2.1

variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

theorem forces_closed_regular_l {a n} (φ : Formula a n) (hφ : φ.FreeClosed) (ρ : Env M n)
    (hρ : ∀ i, Name_d M B (ρ.bound i)) : Regular_d M B R z (Forces_d M B R z φ ρ) := by
  obtain ⟨t, ht⟩ := zf_name_exists_l (B := B) hZF
  let η : Env M n := ⟨ρ.bound, fun _ => t⟩
  have hn (v : Term n) : Name_d M B (v.eval η) := by
    cases v with
    | free _ => exact ht
    | bound i => exact hρ i
  have he p := forces_env_l (B := B) (R := R) (z := z) hZF.1 φ hφ ρ η (fun _ => rfl) p
  have hr := forces_regular_l O hZF φ η hn
  exact ⟨fun p q hp hq h => (he q).mpr (hr.1 p q hp hq ((he p).mp h)),
    fun p hp hz h => (he p).mpr (hr.2 p hp hz (fun q hq =>
      (h q hq).elim fun r hh => ⟨r, hh.1, (he r).mp hh.2⟩))⟩

theorem forces_closed_congr_l {a n} (φ : Formula a n) (hφ : φ.FreeClosed) (ρ η : Env M n)
    (hρ : ∀ i, Name_d M B (ρ.bound i)) (hη : ∀ i, Name_d M B (η.bound i)) {p}
    (hp : M.mem p B) (hz : p ≠ z) (he : ∀ i, Eq_force_d M B R z p (ρ.bound i) (η.bound i)) :
    Forces_d M B R z φ ρ p ↔ Forces_d M B R z φ η p := by
  obtain ⟨t, ht⟩ := zf_name_exists_l (B := B) hZF
  let ρ' : Env M n := ⟨ρ.bound, fun _ => t⟩
  let η' : Env M n := ⟨η.bound, fun _ => t⟩
  have names (v : Fin n → M.Domain) (hv : ∀ i, Name_d M B (v i)) (s : Term n) :
      Name_d M B (s.eval (⟨v, fun _ => t⟩ : Env M n)) := by
    cases s with
    | free _ => exact ht
    | bound i => exact hv i
  have eqn (s : Term n) : Eq_force_d M B R z p (s.eval ρ') (s.eval η') := by
    cases s with
    | free _ => exact eq_force_refl_l O hZF hp ht
    | bound i => exact he i
  exact (forces_env_l hZF.1 φ hφ ρ ρ' (fun _ => rfl) p).trans
    ((forces_congr_below_l O hZF φ ρ' η' (names _ hρ) (names _ hη) hp eqn p
      (below_refl_l O hp hz)).trans (forces_env_l hZF.1 φ hφ η' η (fun _ => rfl) p))

theorem check_forces_bases_l {a n} (φ : Formula a n) (hφ : φ.FreeClosed)
    (v : Fin n → M.Domain) (ρ η : Env M n) {b c p} (hb : M.mem b B) (hc : M.mem c B)
    (hρ : ∀ i, Check_d M b (v i) (ρ.bound i)) (hη : ∀ i, Check_d M c (v i) (η.bound i))
    (hp : Below_d M B R z p b) (hpc : Entry_d M p c R) :
    Forces_d M B R z φ ρ p ↔ Forces_d M B R z φ η p :=
  forces_closed_congr_l O hZF φ hφ ρ η
    (fun i => check_name_l M (check_range_l M hZF) hb (hρ i))
    (fun i => check_name_l M (check_range_l M hZF) hc (hη i)) hp.1 hp.2.1
    (fun i => check_force_bases_l O hZF hb hc (hρ i) (hη i) hp.1 hp.2.2 hpc)

end YesMetaZFC.Model.Forcing.Internal
