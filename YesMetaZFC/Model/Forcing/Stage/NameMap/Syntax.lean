import YesMetaZFC.Model.Forcing.Internal.Check.Syntax

/-! # 内部名称搬运的递归图规格

K 是标签关系：每个条目 (s,b) 变成所有 (H(s),c)，其中 (b,c)∈K。
允许标签被删除或展开为多个标签；阶段嵌入图是其中的实际函数实例。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Nmap_step_d (K H x t : M.Domain) : Prop :=
  (∀ s b, Entry_d M s b x → ∃ a, Entry_d M s a H) ∧
  ∀ v, M.mem v t ↔ ∃ s b a c,
    Entry_d M s b x ∧ Entry_d M s a H ∧ Entry_d M b c K ∧ KPair_d M v a c

def Nmap_graph_d (K H : M.Domain) : Prop :=
  (∀ v, M.mem v H → ∃ x t, KPair_d M v x t) ∧
  ∀ x t, Entry_d M x t H → Nmap_step_d M K H x t

def Nmap_d (K x t : M.Domain) : Prop := ∃ H, Nmap_graph_d M K H ∧ Entry_d M x t H

def nmap_step_m {n} (K H x t : Term n) : Formula 1 n :=
  .conj (.forallE (.forallE (.imp (entry_m (.bound 1) .newest x.weaken.weaken)
    (.existsE (entry_m (.bound 2) .newest H.weaken.weaken.weaken)))))
    (.forallE (.iff (.mem .newest t.weaken) (.existsE (.existsE (.existsE (.existsE
      (.conj (entry_m (.bound 3) (.bound 2) x.weaken.weaken.weaken.weaken.weaken)
        (.conj (entry_m (.bound 3) (.bound 1) H.weaken.weaken.weaken.weaken.weaken)
          (.conj (entry_m (.bound 2) .newest K.weaken.weaken.weaken.weaken.weaken)
            (kpair_m (.bound 4) (.bound 1) .newest))))))))))
derive_free_closed nmap_step_m

def nmap_graph_m {n} (K H : Term n) : Formula 1 n :=
  .conj (Formula.isRelation kpair_convention_l H)
    (.forallE (.forallE (.imp (entry_m (.bound 1) .newest H.weaken.weaken)
      (nmap_step_m K.weaken.weaken H.weaken.weaken (.bound 1) .newest))))
derive_free_closed nmap_graph_m

def nmap_m {n} (K x t : Term n) : Formula 1 n :=
  .existsE (.conj (nmap_graph_m K.weaken .newest) (entry_m x.weaken t.weaken .newest))
derive_free_closed nmap_m

theorem nmap_step_sat_l (hE : Extensional M) {n} (ρ : Env M n) (K H x t : Term n) :
    Formula.satisfies ρ (nmap_step_m K H x t) ↔
      Nmap_step_d M (K.eval ρ) (H.eval ρ) (x.eval ρ) (t.eval ρ) := by
  simp only [nmap_step_m, Nmap_step_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, entry_sat_l M hE, kpair_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem nmap_graph_sat_l (hE : Extensional M) {n} (ρ : Env M n) (K H : Term n) :
    Formula.satisfies ρ (nmap_graph_m K H) ↔ Nmap_graph_d M (K.eval ρ) (H.eval ρ) := by
  simp only [nmap_graph_m, Nmap_graph_d, Formula.isRelation, kpair_convention_l,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_exists_iff, Formula.satisfies_imp_iff,
    entry_sat_l M hE, nmap_step_sat_l M hE, kpair_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem nmap_sat_l (hE : Extensional M) {n} (ρ : Env M n) (K x t : Term n) :
    Formula.satisfies ρ (nmap_m K x t) ↔ Nmap_d M (K.eval ρ) (x.eval ρ) (t.eval ρ) := by
  simp only [nmap_m, Nmap_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    nmap_graph_sat_l M hE, entry_sat_l M hE, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]

end YesMetaZFC.Model.Forcing.Internal
