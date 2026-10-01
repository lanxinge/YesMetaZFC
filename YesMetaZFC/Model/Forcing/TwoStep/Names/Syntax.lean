import YesMetaZFC.Model.Forcing.Internal.Names.PairConstruction

/-! # 两步名称的递归转换规格

二步条目 (a,(p,s)) 变成以 p 加权的名称有序对 (H(a),s)。第一阶段解释后，
这些有序对正是第二阶段名称的条目；图的所有量词仍遍历原地模型对象。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Curry_step_d (B C H x t : M.Domain) : Prop :=
  (∀ a c, Entry_d M a c x → ∃ u, Entry_d M a u H) ∧
  ∀ v, M.mem v t ↔ ∃ a c u p s k, Entry_d M a c x ∧ M.mem c C ∧ KPair_d M c p s ∧
    Entry_d M a u H ∧ Nkpair_d M B u s k ∧ KPair_d M v k p

def Curry_graph_d (B C H : M.Domain) : Prop :=
  (∀ v, M.mem v H → ∃ x t, KPair_d M v x t) ∧
  ∀ x t, Entry_d M x t H → Curry_step_d M B C H x t

def Curry_d (B C x t : M.Domain) : Prop := ∃ H, Curry_graph_d M B C H ∧ Entry_d M x t H

def curry_step_m {n} (B C H x t : Term n) : Formula 1 n :=
  .conj (.forallE (.forallE (.imp (entry_m (.bound 1) .newest x.weaken.weaken)
    (.existsE (entry_m (.bound 2) .newest H.weaken.weaken.weaken)))))
    (.forallE (.iff (.mem .newest t.weaken) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
      (.conj (entry_m (.bound 5) (.bound 4) x.weaken.weaken.weaken.weaken.weaken.weaken.weaken)
        (.conj (.mem (.bound 4) C.weaken.weaken.weaken.weaken.weaken.weaken.weaken)
          (.conj (kpair_m (.bound 4) (.bound 2) (.bound 1))
            (.conj (entry_m (.bound 5) (.bound 3) H.weaken.weaken.weaken.weaken.weaken.weaken.weaken)
              (.conj (nkpair_m B.weaken.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) .newest)
                (kpair_m (.bound 6) .newest (.bound 2)))))))))))))))
derive_free_closed curry_step_m

def curry_graph_m {n} (B C H : Term n) : Formula 1 n :=
  .conj (Formula.isRelation kpair_convention_l H) (.forallE (.forallE (.imp
    (entry_m (.bound 1) .newest H.weaken.weaken)
    (curry_step_m B.weaken.weaken C.weaken.weaken H.weaken.weaken (.bound 1) .newest))))
derive_free_closed curry_graph_m

def curry_m {n} (B C x t : Term n) : Formula 1 n :=
  .existsE (.conj (curry_graph_m B.weaken C.weaken .newest) (entry_m x.weaken t.weaken .newest))
derive_free_closed curry_m

theorem curry_step_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B C H x t : Term n) :
    Formula.satisfies ρ (curry_step_m B C H x t) ↔
      Curry_step_d M (B.eval ρ) (C.eval ρ) (H.eval ρ) (x.eval ρ) (t.eval ρ) := by
  simp only [curry_step_m, Curry_step_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, entry_sat_l M hE, kpair_sat_l M hE, nkpair_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem curry_graph_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B C H : Term n) :
    Formula.satisfies ρ (curry_graph_m B C H) ↔ Curry_graph_d M (B.eval ρ) (C.eval ρ) (H.eval ρ) := by
  simp only [curry_graph_m, Curry_graph_d, Formula.isRelation, kpair_convention_l,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, entry_sat_l M hE,
    curry_step_sat_l M hE, kpair_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem curry_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B C x t : Term n) :
    Formula.satisfies ρ (curry_m B C x t) ↔ Curry_d M (B.eval ρ) (C.eval ρ) (x.eval ρ) (t.eval ρ) := by
  simp only [curry_m, Curry_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    curry_graph_sat_l M hE, entry_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

end YesMetaZFC.Model.Forcing.Internal
