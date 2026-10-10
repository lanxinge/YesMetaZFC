import YesMetaZFC.Model.Forcing.Internal.Names.Depth
import YesMetaZFC.Model.Forcing.TwoStep.Basic

/-! # 二步名称摊平的内部递归规格

τ 的三层条目后继 a 递归摊平；条件 (p,s) 在 p 迫使 (a,s)∈τ 时接入其值。
三层后继构成实际集合，所有力迫测试使用已有原公式，递归图仍为原模型内对象。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Flat_step_d (B R z C H x t : M.Domain) : Prop :=
  (∀ a, Entry_path_d M 3 x a → ∃ u, Entry_d M a u H) ∧
  ∀ v, M.mem v t ↔ ∃ a c p s u, Entry_path_d M 3 x a ∧ M.mem c C ∧ KPair_d M c p s ∧
    Rel_force_d M B R z x p a s ∧ Entry_d M a u H ∧ KPair_d M v u c

def Flat_graph_d (B R z C H : M.Domain) : Prop :=
  (∀ v, M.mem v H → ∃ x t, KPair_d M v x t) ∧
  ∀ x t, Entry_d M x t H → Flat_step_d M B R z C H x t

def Flat_d (B R z C x t : M.Domain) : Prop := ∃ H, Flat_graph_d M B R z C H ∧ Entry_d M x t H

def flat_step_m {n} (B R z C H x t : Term n) : Formula 1 n :=
  .conj (.forallE (.imp (entry_path_m 3 x.weaken .newest) (.existsE (entry_m (.bound 1) .newest H.weaken.weaken))))
    (.forallE (.iff (.mem .newest t.weaken) (.existsE (.existsE (.existsE (.existsE (.existsE
      (.conj (entry_path_m 3 x.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4))
        (.conj (.mem (.bound 3) C.weaken.weaken.weaken.weaken.weaken.weaken)
          (.conj (kpair_m (.bound 3) (.bound 2) (.bound 1))
            (.conj (rel_force_m B.weaken.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken.weaken
              z.weaken.weaken.weaken.weaken.weaken.weaken x.weaken.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 4) (.bound 1))
              (.conj (entry_m (.bound 4) .newest H.weaken.weaken.weaken.weaken.weaken.weaken)
                (kpair_m (.bound 5) .newest (.bound 3))))))))))))))
derive_free_closed flat_step_m

def flat_graph_m {n} (B R z C H : Term n) : Formula 1 n :=
  .conj (Formula.isRelation kpair_convention_l H) (.forallE (.forallE (.imp
    (entry_m (.bound 1) .newest H.weaken.weaken)
    (flat_step_m B.weaken.weaken R.weaken.weaken z.weaken.weaken C.weaken.weaken H.weaken.weaken (.bound 1) .newest))))
derive_free_closed flat_graph_m

def flat_m {n} (B R z C x t : Term n) : Formula 1 n :=
  .existsE (.conj (flat_graph_m B.weaken R.weaken z.weaken C.weaken .newest) (entry_m x.weaken t.weaken .newest))
derive_free_closed flat_m

theorem flat_step_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z C H x t : Term n) :
    Formula.satisfies ρ (flat_step_m B R z C H x t) ↔
      Flat_step_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (C.eval ρ) (H.eval ρ) (x.eval ρ) (t.eval ρ) := by
  simp only [flat_step_m, Flat_step_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, entry_path_sat_l hE, entry_sat_l M hE, kpair_sat_l M hE,
    rel_force_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem flat_graph_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z C H : Term n) :
    Formula.satisfies ρ (flat_graph_m B R z C H) ↔
      Flat_graph_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (C.eval ρ) (H.eval ρ) := by
  simp only [flat_graph_m, Flat_graph_d, Formula.isRelation, kpair_convention_l,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, entry_sat_l M hE,
    kpair_sat_l M hE, flat_step_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem flat_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z C x t : Term n) :
    Formula.satisfies ρ (flat_m B R z C x t) ↔
      Flat_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (C.eval ρ) (x.eval ρ) (t.eval ρ) := by
  simp only [flat_m, Flat_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    flat_graph_sat_l M hE, entry_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

end YesMetaZFC.Model.Forcing.Internal
