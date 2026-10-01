import YesMetaZFC.Model.Forcing.CCC.Basic

/-! # 可数链条件的原公式

反链及其到内部 ω 的单射均使用原集合论公式，供内部归纳和名称力迫共用。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def antichain_m {n} (B R z A : Term n) : Formula 1 n :=
  .conj (Formula.forallMem A (.conj (.mem .newest B.weaken)
    (.neg (Formula.extensionalEq .newest z.weaken))))
    (Formula.forallMem A (Formula.forallMem A.weaken
      (.imp (cmp_m B.weaken.weaken R.weaken.weaken z.weaken.weaken (.bound 1) .newest)
        (Formula.extensionalEq (.bound 1) .newest))))
derive_free_closed antichain_m

def ccc_m (𝒞 : OrderedPairConvention) {n} (ω B R z : Term n) : Formula 1 n :=
  .forallE (.imp (antichain_m B.weaken R.weaken z.weaken .newest)
    (Formula.cardinalLessOrEqual 𝒞 .newest ω.weaken))
derive_free_closed ccc_m

/-- 不暴露 ω 名称选择的 CCC 原公式，零条件取条件集本身。 -/
def ccc_exists_m {n} (B R : Term n) : Formula 1 n :=
  .existsE (.conj (Formula.isOmega .newest)
    (ccc_m kpair_convention_l .newest B.weaken R.weaken B.weaken))
derive_free_closed ccc_exists_m

theorem antichain_sat_l (M : SetTheory.Structure.{u}) (hE : Extensional M) {n}
    (ρ : Env M n) (B R z A : Term n) : Formula.satisfies ρ (antichain_m B R z A) ↔
      Antichain_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (A.eval ρ) := by
  simp only [antichain_m, Antichain_d, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_imp_iff, cmp_sat_l M hE, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest, Term.eval_bound_one_push]
  exact ⟨fun h => ⟨h.1, fun p q hp hq => h.2 p hp q hq⟩,
    fun h => ⟨h.1, fun p hp q hq => h.2 p q hp hq⟩⟩

theorem ccc_sat_l {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention}
    (I : 𝒞.Interpretation M) (hE : Extensional M) {n} (ρ : Env M n) (ω B R z : Term n) :
    Formula.satisfies ρ (ccc_m 𝒞 ω B R z) ↔ Ccc_d M I (ω.eval ρ) (B.eval ρ) (R.eval ρ) (z.eval ρ) := by
  simp only [ccc_m, Ccc_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    antichain_sat_l M hE, Formula.satisfies_cardinalLessOrEqual_iff I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem ccc_exists_sat_l {M : SetTheory.Structure.{u}} (I : kpair_convention_l.Interpretation M)
    (hE : Extensional M) {n} (ρ : Env M n) (B R : Term n) :
    Formula.satisfies ρ (ccc_exists_m B R) ↔ ∃ ω, M.IsOmega ω ∧ Ccc_d M I ω (B.eval ρ) (R.eval ρ) (B.eval ρ) := by
  simp only [ccc_exists_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, ccc_sat_l I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

end YesMetaZFC.Model.Forcing.Internal
