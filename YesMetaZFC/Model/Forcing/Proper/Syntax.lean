import YesMetaZFC.Model.Forcing.Proper.Master.Syntax
import YesMetaZFC.SetTheory.CountableClub

/-! # properness 的内部 club 主条件刻画

在每个含条件域的集合 X 上，要求一个可数子集的 club；其每个成员 N 中的正条件
都可加强成 N 的主条件。该集合论刻画只量化模型内集合，直接给出原力迫公式。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Proper_d (I : kpair_convention_l.Interpretation M) (ω B R z : M.Domain) : Prop :=
  ∀ X, M.MemberSubset B X → ∃ C, Cc_club_d I ω X C ∧
    ∀ N, M.mem N C → ∀ p, M.mem p N → M.mem p B → p ≠ z →
      ∃ q, Below_d M B R z q p ∧ Mstr_d M B R z N q

def proper_m {n} (ω B R z : Term n) : Formula 1 n :=
  .forallE (.imp (Formula.subset B.weaken .newest) (.existsE
    (.conj (cc_club_m kpair_convention_l ω.weaken.weaken (.bound 1) .newest)
      (Formula.forallMem .newest (Formula.forallMem .newest
        (.imp (.mem .newest B.weaken.weaken.weaken.weaken)
          (.imp (.neg (Formula.extensionalEq .newest z.weaken.weaken.weaken.weaken)) (.existsE
            (.conj (below_m B.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken
              z.weaken.weaken.weaken.weaken.weaken .newest (.bound 1))
              (mstr_m B.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken
                z.weaken.weaken.weaken.weaken.weaken (.bound 2) .newest))))))))))
derive_free_closed proper_m

def proper_exists_m {n} (B R : Term n) : Formula 1 n :=
  .existsE (.conj (Formula.isOmega .newest) (proper_m .newest B.weaken R.weaken B.weaken))
derive_free_closed proper_exists_m

theorem proper_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (ω B R z : Term n) : Formula.satisfies ρ (proper_m ω B R z) ↔
      Proper_d I (ω.eval ρ) (B.eval ρ) (R.eval ρ) (z.eval ρ) := by
  simp only [proper_m, Proper_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    cc_club_sat_l I hE, Formula.satisfies_forallMem_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE, below_sat_l M hE,
    mstr_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem proper_exists_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (B R : Term n) : Formula.satisfies ρ (proper_exists_m B R) ↔
      ∃ ω, M.IsOmega ω ∧ Proper_d I ω (B.eval ρ) (R.eval ρ) (B.eval ρ) := by
  simp only [proper_exists_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, proper_sat_l I hE, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

end YesMetaZFC.Model.Forcing.Internal
