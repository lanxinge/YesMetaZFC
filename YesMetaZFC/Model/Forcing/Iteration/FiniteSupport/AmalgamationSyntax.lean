import YesMetaZFC.Model.Forcing.Iteration.FiniteSupport.DirectUnion

/-! # 有限支撑尾部合并的原公式

两个条件在指定前缀之外没有共同坐标时，前缀相容性应提升为整条条件相容性。
这里把该断言写成原公式，下一模块在模型内部对阶段序数归纳。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_disjoint_d (α p q : M.Domain) : Prop :=
  ∀ i s t, Entry_d M i s p → Entry_d M i t q → M.mem i α

def row_disjoint_m {n} (α p q : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.imp (entry_m (.bound 2) (.bound 1) p.weaken.weaken.weaken)
    (.imp (entry_m (.bound 2) .newest q.weaken.weaken.weaken) (.mem (.bound 2) α.weaken.weaken.weaken)))))
derive_free_closed row_disjoint_m

def Row_cmp_d (I : kpair_convention_l.Interpretation M) (α B R p q : M.Domain) : Prop :=
  ∃ a b, M.IsRestrictionOf I a p α ∧ M.IsRestrictionOf I b q α ∧ Cmp_d M B R B a b

def row_cmp_m {n} (α B R p q : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (Formula.isRestriction kpair_convention_l (.bound 1) p.weaken.weaken α.weaken.weaken)
    (.conj (Formula.isRestriction kpair_convention_l .newest q.weaken.weaken α.weaken.weaken)
      (cmp_m B.weaken.weaken R.weaken.weaken B.weaken.weaken (.bound 1) .newest))))
derive_free_closed row_cmp_m

theorem row_disjoint_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α p q : Term n) :
    Formula.satisfies ρ (row_disjoint_m α p q) ↔ Row_disjoint_d (α.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [row_disjoint_m, Row_disjoint_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    entry_sat_l M hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  rfl

theorem row_cmp_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (α B R p q : Term n) :
    Formula.satisfies ρ (row_cmp_m α B R p q) ↔ Row_cmp_d I (α.eval ρ) (B.eval ρ) (R.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [row_cmp_m, Row_cmp_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isRestriction_iff I, cmp_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

def Row_amalgam_d (I : kpair_convention_l.Interpretation M) (α B R F H β : M.Domain) : Prop :=
  ∀ D V p q, Entry_d M β D F → Entry_d M β V H → M.mem p D → M.mem q D → M.MemberSubset α β →
    Row_disjoint_d α p q → Row_cmp_d I α B R p q → Cmp_d M D V D p q

def row_amalgam_m {n} (α B R F H β : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE
    (.imp (entry_m β.weaken.weaken.weaken.weaken (.bound 3) F.weaken.weaken.weaken.weaken)
      (.imp (entry_m β.weaken.weaken.weaken.weaken (.bound 2) H.weaken.weaken.weaken.weaken)
        (.imp (.mem (.bound 1) (.bound 3)) (.imp (.mem .newest (.bound 3))
          (.imp (Formula.subset α.weaken.weaken.weaken.weaken β.weaken.weaken.weaken.weaken)
            (.imp (row_disjoint_m α.weaken.weaken.weaken.weaken (.bound 1) .newest)
              (.imp (row_cmp_m α.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken
                R.weaken.weaken.weaken.weaken (.bound 1) .newest)
                (cmp_m (.bound 3) (.bound 2) (.bound 3) (.bound 1) .newest)))))))))))
derive_free_closed row_amalgam_m

theorem row_amalgam_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (α B R F H β : Term n) :
    Formula.satisfies ρ (row_amalgam_m α B R F H β) ↔
      Row_amalgam_d I (α.eval ρ) (B.eval ρ) (R.eval ρ) (F.eval ρ) (H.eval ρ) (β.eval ρ) := by
  simp only [row_amalgam_m, Row_amalgam_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    entry_sat_l M hE, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff,
    row_disjoint_sat_l hE, row_cmp_sat_l I hE, cmp_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.Model.Forcing.Internal
