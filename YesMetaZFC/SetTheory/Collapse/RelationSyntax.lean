import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.SetTheory.FunctionConstruction
import YesMetaZFC.SetTheory.MembershipInduction

/-! # 任意内部良基关系的坍塌证书

良基性只量化模型中的子集。部分坍塌图的定义域向关系前驱封闭，且每个值恰为
前驱值之集；不预设外部良基性，也不预设坍塌存在或单值。非外延关系允许重复值。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Wf_rel_d (X R : M.Domain) : Prop := ∀ Y, M.MemberSubset Y X → (∃ a, M.mem a Y) →
  ∃ a, M.mem a Y ∧ ∀ b, M.mem b Y → ¬ Rd_entry_d b a R

def wf_rel_m {n} (X R : Term n) : Formula 1 n := .forallE
  (.imp (Formula.subset .newest X.weaken) (.imp (.existsE (.mem .newest (.bound 1)))
    (Formula.existsMem .newest (Formula.forallMem (.bound 1)
      (.neg (rd_entry_m .newest (.bound 1) R.weaken.weaken.weaken))))))
derive_free_closed wf_rel_m

def Wc_step_d (X R F a x : M.Domain) : Prop :=
  (∀ b, M.mem b X → Rd_entry_d b a R → ∃ y, Rd_entry_d b y F) ∧
  ∀ y, M.mem y x ↔ ∃ b, M.mem b X ∧ Rd_entry_d b a R ∧ Rd_entry_d b y F

def Wc_graph_d (X R F : M.Domain) : Prop :=
  (∀ p, M.mem p F → ∃ a x, KPair_d M p a x) ∧
  ∀ a x, Rd_entry_d a x F → M.mem a X ∧ Wc_step_d X R F a x

def Wc_value_d (X R a x : M.Domain) : Prop := ∃ F, Wc_graph_d X R F ∧ Rd_entry_d a x F

def wc_step_m {n} (X R F a x : Term n) : Formula 1 n :=
  .conj (Formula.forallMem X (.imp (rd_entry_m .newest a.weaken R.weaken)
    (.existsE (rd_entry_m (.bound 1) .newest F.weaken.weaken))))
    (.forallE (.iff (.mem .newest x.weaken) (Formula.existsMem X.weaken
      (.conj (rd_entry_m .newest a.weaken.weaken R.weaken.weaken)
        (rd_entry_m .newest (.bound 1) F.weaken.weaken)))))
derive_free_closed wc_step_m

def wc_graph_m {n} (X R F : Term n) : Formula 1 n :=
  .conj (Formula.isRelation kpair_convention_l F) (.forallE (.forallE
    (.imp (rd_entry_m (.bound 1) .newest F.weaken.weaken)
      (.conj (.mem (.bound 1) X.weaken.weaken)
        (wc_step_m X.weaken.weaken R.weaken.weaken F.weaken.weaken (.bound 1) .newest)))))
derive_free_closed wc_graph_m

def wc_value_m {n} (X R a x : Term n) : Formula 1 n := .existsE
  (.conj (wc_graph_m X.weaken R.weaken .newest) (rd_entry_m a.weaken x.weaken .newest))
derive_free_closed wc_value_m

theorem wf_rel_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R : Term n) :
    Formula.satisfies ρ (wf_rel_m X R) ↔ Wf_rel_d (X.eval ρ) (R.eval ρ) := by
  simp only [wf_rel_m, Wf_rel_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_exists_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_neg_iff, rd_entry_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem wc_step_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R F a x : Term n) :
    Formula.satisfies ρ (wc_step_m X R F a x) ↔
      Wc_step_d (X.eval ρ) (R.eval ρ) (F.eval ρ) (a.eval ρ) (x.eval ρ) := by
  simp only [wc_step_m, Wc_step_d, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, rd_entry_sat_l hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem wc_graph_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R F : Term n) :
    Formula.satisfies ρ (wc_graph_m X R F) ↔ Wc_graph_d (X.eval ρ) (R.eval ρ) (F.eval ρ) := by
  simp only [wc_graph_m, Wc_graph_d, Formula.isRelation, kpair_convention_l,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    kpair_sat_l M hE, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rd_entry_sat_l hE, Formula.satisfies_mem_iff, wc_step_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem wc_value_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R a x : Term n) :
    Formula.satisfies ρ (wc_value_m X R a x) ↔ Wc_value_d (X.eval ρ) (R.eval ρ) (a.eval ρ) (x.eval ρ) := by
  simp only [wc_value_m, Wc_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    wc_graph_sat_l hE, rd_entry_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

/-- 实际隶属关系给出任意载体上的内部良基关系实例。 -/
theorem wf_membership_l (hZF : M.Models ZF) (X : M.Domain) : ∃ R, Wf_rel_d X R ∧
    ∀ a b, Rd_entry_d a b R ↔ M.mem a X ∧ M.mem b X ∧ M.mem a b := by
  let φ : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  obtain ⟨R, _, hr⟩ := ZF.exists_setRelationOn_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ⟨Fin.elim0, fun _ => X⟩ X
  have hR a b : Rd_entry_d a b R ↔ M.mem a X ∧ M.mem b X ∧ M.mem a b := by
    simpa only [φ, BinarySchema.denote, Formula.satisfies_mem_iff] using! hr a b
  refine ⟨R, fun Y _ hn => ?_, hR⟩
  obtain ⟨a, ha, hm⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) hn
  exact ⟨a, ha, fun b hb hr => hm b hb ((hR b a).mp hr).2.2⟩

/-- 分离实际原公式的反例集，再消费模型内的极小元性质。 -/
theorem wf_rel_ind_l (hZF : M.Models ZF) {X R} (hw : Wf_rel_d X R) {n}
    (φ : UnarySchema n) (ρ : Env M n)
    (h : ∀ a, M.mem a X → (∀ b, M.mem b X → Rd_entry_d b a R → φ.denote ρ b) → φ.denote ρ a) :
    ∀ a, M.mem a X → φ.denote ρ a := by
  classical
  obtain ⟨Y, hY⟩ := ZF.separation_exists_d hZF φ.neg ρ X
  have hy a : M.mem a Y ↔ M.mem a X ∧ ¬ φ.denote ρ a := by
    simpa only [UnarySchema.neg, UnarySchema.denote, Formula.satisfies_neg_iff] using hY a
  intro a ha
  apply Classical.byContradiction
  intro hn
  obtain ⟨b, hb, hm⟩ := hw Y (fun c hc => ((hy c).mp hc).1) ⟨a, (hy a).mpr ⟨ha, hn⟩⟩
  exact ((hy b).mp hb).2 (h b ((hy b).mp hb).1 (fun c hc hcb =>
    Classical.byContradiction (fun hn => hm c ((hy c).mpr ⟨hc, hn⟩) hcb)))

end YesMetaZFC.SetTheory
