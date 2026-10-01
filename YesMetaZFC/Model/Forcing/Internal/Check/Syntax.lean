import YesMetaZFC.Model.Forcing.Internal.Names.Basic

/-! # 规范名称的内部递归图

部分递归图的定义域向成员封闭，且每个值恰由前驱值加上固定标签 b 构成。
规范名称由包含指定输入输出的这种集合图定义；所有证书都是地模型对象。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Check_step_d (b F x t : M.Domain) : Prop :=
  (∀ y, M.mem y x → ∃ s, Entry_d M y s F) ∧
  ∀ p, M.mem p t ↔ ∃ y s, M.mem y x ∧ Entry_d M y s F ∧ KPair_d M p s b

def Check_graph_d (b F : M.Domain) : Prop :=
  (∀ p, M.mem p F → ∃ x t, KPair_d M p x t) ∧
  ∀ x t, Entry_d M x t F → Check_step_d M b F x t

def Check_d (b x t : M.Domain) : Prop :=
  ∃ F, Check_graph_d M b F ∧ Entry_d M x t F

def entry_m {n} (x t F : Term n) : Formula 1 n :=
  Formula.orderedPairMem kpair_convention_l x t F

derive_free_closed entry_m

def check_step_m {n} (b F x t : Term n) : Formula 1 n :=
  .conj (Formula.forallMem x (.existsE (entry_m (.bound 1) .newest F.weaken.weaken)))
    (.forallE (.iff (.mem .newest t.weaken)
      (Formula.existsMem x.weaken (.existsE (.conj
        (entry_m (.bound 1) .newest F.weaken.weaken.weaken)
        (kpair_m (.bound 2) .newest b.weaken.weaken.weaken))))))

derive_free_closed check_step_m

def check_graph_m {n} (b F : Term n) : Formula 1 n :=
  .conj (Formula.isRelation kpair_convention_l F)
    (.forallE (.forallE (.imp (entry_m (.bound 1) .newest F.weaken.weaken)
      (check_step_m b.weaken.weaken F.weaken.weaken (.bound 1) .newest))))

derive_free_closed check_graph_m

def check_m {n} (b x t : Term n) : Formula 1 n :=
  .existsE (.conj (check_graph_m b.weaken .newest) (entry_m x.weaken t.weaken .newest))

derive_free_closed check_m

theorem entry_sat_l (hE : Extensional M) {n} (ρ : Env M n) (x t F : Term n) :
    Formula.satisfies ρ (entry_m x t F) ↔ Entry_d M (x.eval ρ) (t.eval ρ) (F.eval ρ) := by
  simp only [entry_m, Formula.orderedPairMem, kpair_convention_l, Entry_d,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    kpair_sat_l M hE, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

theorem check_step_sat_l (hE : Extensional M) {n} (ρ : Env M n) (b F x t : Term n) :
    Formula.satisfies ρ (check_step_m b F x t) ↔
      Check_step_d M (b.eval ρ) (F.eval ρ) (x.eval ρ) (t.eval ρ) := by
  simp only [check_step_m, Check_step_d, Formula.satisfies_conj_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_exists_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, entry_sat_l M hE, kpair_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push]
  exact and_congr_right fun _ => forall_congr' fun p => iff_congr Iff.rfl
    ⟨fun ⟨y, hy, s, hs, hp⟩ => ⟨y, s, hy, hs, hp⟩,
      fun ⟨y, s, hy, hs, hp⟩ => ⟨y, hy, s, hs, hp⟩⟩

theorem check_graph_sat_l (hE : Extensional M) {n} (ρ : Env M n) (b F : Term n) :
    Formula.satisfies ρ (check_graph_m b F) ↔ Check_graph_d M (b.eval ρ) (F.eval ρ) := by
  simp only [check_graph_m, Check_graph_d, Formula.isRelation, kpair_convention_l,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_exists_iff, Formula.satisfies_imp_iff,
    entry_sat_l M hE, check_step_sat_l M hE, kpair_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push]

theorem check_sat_l (hE : Extensional M) {n} (ρ : Env M n) (b x t : Term n) :
    Formula.satisfies ρ (check_m b x t) ↔ Check_d M (b.eval ρ) (x.eval ρ) (t.eval ρ) := by
  simp only [check_m, Check_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    check_graph_sat_l M hE, entry_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 不先假定递归值唯一，就已能取得子对象的递归图证书。 -/
theorem check_child_l {b x t} (h : Check_d M b x t) {y} (hy : M.mem y x) :
    ∃ s, Check_d M b y s := by
  obtain ⟨F, hF, ht⟩ := h
  obtain ⟨s, hs⟩ := (hF.2 x t ht).1 y hy
  exact ⟨s, F, hF, hs⟩

end YesMetaZFC.Model.Forcing.Internal
