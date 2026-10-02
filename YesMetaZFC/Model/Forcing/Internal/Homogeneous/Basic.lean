import YesMetaZFC.Model.Forcing.Internal.Automorphism.Forcing
import YesMetaZFC.Model.Forcing.Internal.Forcing.Finite
import YesMetaZFC.Model.Forcing.CCC.Basic

/-! # 弱齐性与地参数判定的一致性

任意两个正条件可经内部自同构变成相容条件。地参数的 check 名称以各自力迫条件
为基点，故无需最大条件；共同加强处的基点交换保证同一地参数命题不能得到相反判定。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Whom_d (B R z : M.Domain) : Prop := ∀ p q, M.mem p B → p ≠ z → M.mem q B → q ≠ z →
  ∃ F s, Aut_d M B R z F ∧ Entry_d M p s F ∧ Cmp_d M B R z s q

def whom_m {n} (B R z : Term n) : Formula 1 n :=
  Formula.forallMem B (Formula.forallMem B.weaken
    (.imp (.neg (Formula.extensionalEq (.bound 1) z.weaken.weaken))
      (.imp (.neg (Formula.extensionalEq .newest z.weaken.weaken))
        (.existsE (.existsE (.conj
          (aut_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
            z.weaken.weaken.weaken.weaken (.bound 1))
          (.conj (entry_m (.bound 3) .newest (.bound 1))
            (cmp_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
              z.weaken.weaken.weaken.weaken .newest (.bound 2)))))))))
derive_free_closed whom_m

theorem whom_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z : Term n) :
    Formula.satisfies ρ (whom_m B R z) ↔ Whom_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) := by
  simp only [whom_m, Whom_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, aut_sat_l hE,
    entry_sat_l M hE, cmp_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h p q hp hz hq hqz => h p hp q hq hz hqz, fun h p hp q hq hz hqz => h p q hp hz hq hqz⟩

/-- 基点与名称见证均量化；定义中没有预先指定的泛型或条件参数。 -/
def Gforce_d {n} (B R z : M.Domain) (φ : Formula 1 n) (v : Fin n → M.Domain) : Prop :=
  ∃ p, ∃ ρ : Env M n, M.mem p B ∧ p ≠ z ∧ (∀ i, Check_d M p (v i) (ρ.bound i)) ∧
    Forces_d M B R z φ ρ p

variable {M} {B R z : M.Domain} (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

theorem gforce_change_base_l {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (v : Fin n → M.Domain) (ρ : Env M n) {b p} (hb : M.mem b B)
    (hρ : ∀ i, Check_d M b (v i) (ρ.bound i)) (hp : Below_d M B R z p b)
    (hf : Forces_d M B R z φ ρ p) : Gforce_d M B R z φ v := by
  obtain ⟨η, hη, _⟩ := check_env_l hZF hp.1 v
  exact ⟨p, η, hp.1, hp.2.1, hη,
    (check_forces_bases_l O hZF φ hφ v ρ η hb hp.1 hρ hη hp (O.refl p hp.1)).mp hf⟩

/-- 弱齐性排除同一地参数正文的相反判定，包括没有最大条件的偏序。 -/
theorem whom_consistent_l (hH : Whom_d M B R z) {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (v : Fin n → M.Domain) (h : Gforce_d M B R z φ v) : ¬ Gforce_d M B R z (.neg φ) v := by
  rintro ⟨q, η, hq, hqz, hη, hn⟩
  obtain ⟨p, ρ, hp, hpz, hρ, hf⟩ := h
  obtain ⟨F, s, hF, hps, r, hrs, hrq⟩ := hH p q hp hpz hq hqz
  have hs := (hF.domain p s hps).2
  obtain ⟨ξ, hξ, hξn⟩ := check_env_l hZF hs v
  have hfn := (aut_forces_closed_l hZF hF φ hφ ρ ξ
    (fun i => check_name_l M (check_range_l M hZF) hp (hρ i))
    (fun i => aut_check_l hZF hF hps (hρ i) (hξ i)) hps).mp hf
  have hrφ := (forces_regular_l O hZF φ ξ hξn).1 s r hs hrs hfn
  exact (forces_neg_l hZF.1 φ η q).mp hn r ⟨hrs.1, hrs.2.1, hrq⟩
    ((check_forces_bases_l O hZF φ hφ v ξ η hs hq hξ hη hrs hrq).mp hrφ)

end YesMetaZFC.Model.Forcing.Internal
