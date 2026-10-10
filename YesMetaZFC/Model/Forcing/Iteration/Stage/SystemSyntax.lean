import YesMetaZFC.Model.Forcing.Iteration.Stage.System

/-! # 内部迭代不变式的原公式

阶段链接与整个系统都以原有限变量公式表达。后续超限归纳只能使用这些实际
公式，不把外部阶段性质直接代入模型的分离或归纳模式。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (I : kpair_convention_l.Interpretation M)

def row_link_m {n} (α B R D V : Term n) : Formula 1 n :=
  let s := .forallE (.imp (.mem .newest B.weaken) (row_m α.weaken .newest))
  let a := .forallE (.imp (.mem .newest B.weaken) (.mem .newest D.weaken))
  let b := .forallE (.forallE (.imp (.mem (.bound 1) B.weaken.weaken)
    (.imp (.mem .newest B.weaken.weaken)
      (.iff (entry_m (.bound 1) .newest V.weaken.weaken) (entry_m (.bound 1) .newest R.weaken.weaken)))))
  let c := .forallE (.imp (.mem .newest D.weaken) (.existsE (.conj (.mem .newest B.weaken.weaken)
    (Formula.isRestriction kpair_convention_l .newest (.bound 1) α.weaken.weaken))))
  let d := .forallE (.forallE (.imp (.mem (.bound 1) D.weaken.weaken)
    (.imp (Formula.isRestriction kpair_convention_l .newest (.bound 1) α.weaken.weaken)
      (entry_m (.bound 1) .newest V.weaken.weaken))))
  let f := .forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 3) D.weaken.weaken.weaken.weaken)
    (.imp (.mem (.bound 2) D.weaken.weaken.weaken.weaken)
      (.imp (Formula.isRestriction kpair_convention_l (.bound 1) (.bound 3) α.weaken.weaken.weaken.weaken)
        (.imp (Formula.isRestriction kpair_convention_l .newest (.bound 2) α.weaken.weaken.weaken.weaken)
          (.imp (entry_m (.bound 3) (.bound 2) V.weaken.weaken.weaken.weaken)
            (entry_m (.bound 1) .newest R.weaken.weaken.weaken.weaken)))))))))
  let g := .forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 3) D.weaken.weaken.weaken.weaken)
    (.imp (Formula.isRestriction kpair_convention_l (.bound 2) (.bound 3) α.weaken.weaken.weaken.weaken)
      (.imp (.mem (.bound 1) B.weaken.weaken.weaken.weaken)
        (.imp (entry_m (.bound 1) (.bound 2) R.weaken.weaken.weaken.weaken)
          (.imp (row_splice_m α.weaken.weaken.weaken.weaken (.bound 1) (.bound 3) .newest)
            (.conj (.mem .newest D.weaken.weaken.weaken.weaken)
              (.conj (entry_m .newest (.bound 3) V.weaken.weaken.weaken.weaken)
                (entry_m .newest (.bound 1) V.weaken.weaken.weaken.weaken)))))))))))
  let j := .forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (.mem (.bound 4) D.weaken.weaken.weaken.weaken.weaken)
      (.imp (Formula.isRestriction kpair_convention_l (.bound 3) (.bound 4) α.weaken.weaken.weaken.weaken.weaken)
        (.imp (.mem (.bound 2) B.weaken.weaken.weaken.weaken.weaken)
          (.imp (entry_m (.bound 2) (.bound 3) R.weaken.weaken.weaken.weaken.weaken)
            (.imp (row_splice_m α.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 4) (.bound 1))
              (.imp (.mem .newest D.weaken.weaken.weaken.weaken.weaken)
                (.imp (entry_m .newest (.bound 4) V.weaken.weaken.weaken.weaken.weaken)
                  (.imp (entry_m .newest (.bound 2) V.weaken.weaken.weaken.weaken.weaken)
                    (entry_m .newest (.bound 1) V.weaken.weaken.weaken.weaken.weaken)))))))))))))
  .conj s (.conj a (.conj b (.conj c (.conj d (.conj f (.conj g (.conj j (row_tail_reg_m α B R D V))))))))
derive_free_closed row_link_m

theorem row_link_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α B R D V : Term n) :
    Formula.satisfies ρ (row_link_m α B R D V) ↔
      Row_link_d I (α.eval ρ) (B.eval ρ) (R.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [row_link_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, entry_sat_l M hE, Formula.satisfies_isRestriction_iff I,
    row_splice_sat_l M hE, row_sat_l M hE, row_tail_reg_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, j⟩ => ⟨a, b, c, d, e, f, g, h, j⟩,
    fun h => ⟨h.rows, h.mem, h.order, h.restrict, h.below, h.mono, h.splice, h.splice_glb, h.tail⟩⟩

def row_system_m {n} (δ F H e : Term n) : Formula 1 n :=
  let s := .forallE (.forallE (.forallE (.imp (entry_m (.bound 2) (.bound 1) F.weaken.weaken.weaken)
    (.imp (entry_m (.bound 2) .newest H.weaken.weaken.weaken)
      (row_stage_m (.bound 2) (.bound 1) .newest e.weaken.weaken.weaken)))))
  let l := .forallE (.forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (entry_m (.bound 5) (.bound 3) F.weaken.weaken.weaken.weaken.weaken.weaken)
      (.imp (entry_m (.bound 5) (.bound 2) H.weaken.weaken.weaken.weaken.weaken.weaken)
        (.imp (entry_m (.bound 4) (.bound 1) F.weaken.weaken.weaken.weaken.weaken.weaken)
          (.imp (entry_m (.bound 4) .newest H.weaken.weaken.weaken.weaken.weaken.weaken)
            (.imp (Formula.subset (.bound 5) (.bound 4))
              (row_link_m (.bound 5) (.bound 3) (.bound 2) (.bound 1) .newest)))))))))))
  .conj (Formula.isSequenceOfLength kpair_convention_l F δ)
    (.conj (Formula.isSequenceOfLength kpair_convention_l H δ) (.conj (Formula.isEmpty e) (.conj s l)))
derive_free_closed row_system_m

theorem row_system_sat_l (hE : Extensional M) {n} (ρ : Env M n) (δ F H e : Term n) :
    Formula.satisfies ρ (row_system_m δ F H e) ↔
      Row_system_d I (δ.eval ρ) (F.eval ρ) (H.eval ρ) (e.eval ρ) := by
  simp only [row_system_m, Formula.satisfies_conj_iff, Formula.satisfies_isSequenceOfLength_iff I hE,
    Formula.satisfies_isEmpty_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    entry_sat_l M hE, row_stage_sat_l hE, row_link_sat_l I hE, Formula.satisfies_subset_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
    fun h => ⟨h.conditions, h.relations, h.empty, h.stages, h.links⟩⟩

def row_system_supp_m (k : Bool) {n} (ω F : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp (entry_m (.bound 1) .newest F.weaken.weaken)
    (.forallE (.imp (.mem .newest (.bound 1)) (row_supp_m kpair_convention_l k ω.weaken.weaken.weaken .newest)))))
derive_free_closed row_system_supp_m

theorem row_system_supp_sat_l (hE : Extensional M) (k : Bool) {n} (ρ : Env M n) (ω F : Term n) :
    Formula.satisfies ρ (row_system_supp_m k ω F) ↔ Row_system_supp_d I k (ω.eval ρ) (F.eval ρ) := by
  simp only [row_system_supp_m, Row_system_supp_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, entry_sat_l M hE, row_supp_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

end YesMetaZFC.Model.Forcing.Internal
