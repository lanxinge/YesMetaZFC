import YesMetaZFC.Model.Forcing.TwoStep.Order

/-! # 二步装配证书的原公式呈现

条件集、闭名称库与关系图的每个字段都由原公式表达，供有限参数反射和
嵌套力迫直接使用；语义仍是已构造的 `Two_step_d`。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def step_cond_m {n} (B R z b W A x : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (kpair_m x.weaken.weaken (.bound 1) .newest)
    (.conj (.mem .newest W.weaken.weaken)
      (.conj (below_m B.weaken.weaken R.weaken.weaken z.weaken.weaken (.bound 1) b.weaken.weaken)
        (mem_force_m B.weaken.weaken R.weaken.weaken z.weaken.weaken (.bound 1) .newest A.weaken.weaken)))))
derive_free_closed step_cond_m

def two_step_m {n} (B R z b A T W C S : Term n) : Formula 1 n :=
  .conj (Formula.isRelation kpair_convention_l S) (.conj (.mem b B) (.conj (.mem A W) (.conj (supp_m B W)
    (.conj (.forallE (.iff (.mem .newest C.weaken)
      (step_cond_m B.weaken R.weaken z.weaken b.weaken W.weaken A.weaken .newest)))
      (.forallE (.forallE (.iff (entry_m (.bound 1) .newest S.weaken.weaken)
        (.conj (.mem (.bound 1) C.weaken.weaken) (.conj (.mem .newest C.weaken.weaken)
          (step_le_m B.weaken.weaken R.weaken.weaken z.weaken.weaken T.weaken.weaken (.bound 1) .newest))))))))))
derive_free_closed two_step_m

theorem step_cond_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (B R z b W A x : Term n) : Formula.satisfies ρ (step_cond_m B R z b W A x) ↔
      Step_cond_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (W.eval ρ) (A.eval ρ) (x.eval ρ) := by
  simp only [step_cond_m, Step_cond_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, kpair_sat_l M hE, below_sat_l M hE, mem_force_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem two_step_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (B R z b A T W C S : Term n) : Formula.satisfies ρ (two_step_m B R z b A T W C S) ↔
      Two_step_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (A.eval ρ) (T.eval ρ) (W.eval ρ) (C.eval ρ) (S.eval ρ) := by
  simp only [two_step_m, Formula.isRelation, kpair_convention_l, Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff, kpair_sat_l M hE, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, supp_sat_l M hE, entry_sat_l M hE,
    step_cond_sat_l hE, step_le_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
    fun h => ⟨h.graph, h.base, h.root, h.closed, h.conditions, h.relation⟩⟩

end YesMetaZFC.Model.Forcing.Internal
