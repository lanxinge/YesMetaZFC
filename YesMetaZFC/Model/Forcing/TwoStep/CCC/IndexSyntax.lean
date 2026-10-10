import YesMetaZFC.Model.Forcing.TwoStep.Presentation
import YesMetaZFC.Model.Forcing.Internal.Names.PairConstruction

/-! # 二步反链的泛型索引名称

索引名称收集首坐标被接受的旧二步条件；伴随图把它们映到解释后的第二坐标。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def Step_index_d (M : SetTheory.Structure.{u}) (B b D t g : M.Domain) : Prop :=
  (∀ a p, Entry_d M a p t ↔ ∃ x s, M.mem x D ∧ KPair_d M x p s ∧ Check_d M b x a) ∧
  (∀ a p, Entry_d M a p g ↔ ∃ x s c, M.mem x D ∧ KPair_d M x p s ∧ Check_d M b x c ∧ Nkpair_d M B c s a)

def step_idx_entry_m {n} (b D a p : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (.mem (.bound 1) D.weaken.weaken)
    (.conj (kpair_m (.bound 1) p.weaken.weaken .newest) (check_m b.weaken.weaken (.bound 1) a.weaken.weaken))))
derive_free_closed step_idx_entry_m

def step_graph_entry_m {n} (B b D a p : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.conj (.mem (.bound 2) D.weaken.weaken.weaken)
    (.conj (kpair_m (.bound 2) p.weaken.weaken.weaken (.bound 1))
      (.conj (check_m b.weaken.weaken.weaken (.bound 2) .newest)
        (nkpair_m B.weaken.weaken.weaken .newest (.bound 1) a.weaken.weaken.weaken))))))
derive_free_closed step_graph_entry_m

def step_index_m {n} (B b D t g : Term n) : Formula 1 n :=
  .conj (.forallE (.forallE (.iff (entry_m (.bound 1) .newest t.weaken.weaken)
    (step_idx_entry_m b.weaken.weaken D.weaken.weaken (.bound 1) .newest))))
    (.forallE (.forallE (.iff (entry_m (.bound 1) .newest g.weaken.weaken)
      (step_graph_entry_m B.weaken.weaken b.weaken.weaken D.weaken.weaken (.bound 1) .newest))))
derive_free_closed step_index_m

theorem step_idx_entry_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n}
    (ρ : Env M n) (b D a p : Term n) : Formula.satisfies ρ (step_idx_entry_m b D a p) ↔
      ∃ x s, M.mem x (D.eval ρ) ∧ KPair_d M x (p.eval ρ) s ∧ Check_d M (b.eval ρ) x (a.eval ρ) := by
  simp only [step_idx_entry_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, kpair_sat_l M hE, check_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

theorem step_graph_entry_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n}
    (ρ : Env M n) (B b D a p : Term n) : Formula.satisfies ρ (step_graph_entry_m B b D a p) ↔
      ∃ x s c, M.mem x (D.eval ρ) ∧ KPair_d M x (p.eval ρ) s ∧ Check_d M (b.eval ρ) x c ∧ Nkpair_d M (B.eval ρ) c s (a.eval ρ) := by
  simp only [step_graph_entry_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, kpair_sat_l M hE, check_sat_l M hE, nkpair_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

theorem step_index_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n}
    (ρ : Env M n) (B b D t g : Term n) : Formula.satisfies ρ (step_index_m B b D t g) ↔
      Step_index_d M (B.eval ρ) (b.eval ρ) (D.eval ρ) (t.eval ρ) (g.eval ρ) := by
  simp only [step_index_m, Step_index_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, entry_sat_l M hE, step_idx_entry_sat_l hE,
    step_graph_entry_sat_l hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.Model.Forcing.Internal
