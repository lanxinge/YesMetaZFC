import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.WellFounded

/-! # 在指标上递增的极限下降链

若极限关系不良基，DC 可把每个新节点放到同时容纳当前节点的后继分量。
这样整条下降链的指标递增，下一步的测度约束属于下一节点自己的分量。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Di_step_d (p T S u v : M.Domain) : Prop := ∃ i w,
  Rd_entry_d v i p ∧ Rd_entry_d w i p ∧ Rd_entry_d u w T ∧ Rd_entry_d v w S
def di_step_m {d} (p T S u v : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (rd_entry_m v.weaken.weaken (.bound 1) p.weaken.weaken)
    (.conj (rd_entry_m .newest (.bound 1) p.weaken.weaken) (.conj
      (rd_entry_m u.weaken.weaken .newest T.weaken.weaken) (rd_entry_m v.weaken.weaken .newest S.weaken.weaken)))))
derive_free_closed di_step_m
theorem di_step_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p T S u v : Term d) :
    Formula.satisfies ρ (di_step_m p T S u v) ↔ Di_step_d (p.eval ρ) (T.eval ρ) (S.eval ρ) (u.eval ρ) (v.eval ρ) := by
  simp only [di_step_m, Di_step_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem di_wf_of_no_step_l (hZF : M.Models ZF) {ω J O A p T S q C R : M.Domain}
    (hDC : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω) (h : Di_system_d J O A p T S)
    (hq : Di_limit_d A p T S q C R)
    (hn : ∀ f, Fn0_d ω A f → ¬ (∀ i j u v, M.SuccessorOf j i →
      Rd_entry_d i u f → Rd_entry_d j v f → Di_step_d p T S u v)) : Wf_rel_d C R := by
  classical
  intro Y hY hne
  apply Classical.byContradiction
  intro hmin
  let I := kp_pair_l (ZF.modelsKP hZF)
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 1) (rd_entry_m (.bound 1) .newest (.bound 3)) }
  obtain ⟨B, hb⟩ := ZF.separation_exists_d hZF φ ((⟨fun _ => q, fun _ => q⟩ : Env M 1).push Y) A
  have spec u : M.mem u B ↔ M.mem u A ∧ ∃ D, M.mem D Y ∧ Rd_entry_d u D q := by
    simpa only [φ, Formula.satisfies_existsMem_iff, rd_entry_sat_l hZF.1] using! hb u
  let ψ : BinarySchema 3 := { body := di_step_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨P, _, hp⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ
    (((⟨fun _ => p, fun _ => p⟩ : Env M 1).push T).push S) B
  have ps u v : Rd_entry_d u v P ↔ M.mem u B ∧ M.mem v B ∧ Di_step_d p T S u v :=
    (hp u v).trans (and_congr_right fun _ => and_congr_right fun _ => di_step_sat_l hZF.1 _ _ _ _ _ _)
  have serial u (hu : M.mem u B) : ∃ v, M.mem v B ∧ Rd_entry_d u v P := by
    obtain ⟨huA, D, hDY, huD⟩ := (spec u).mp hu
    have below : ∃ E, M.mem E Y ∧ Rd_entry_d E D R := by
      apply Classical.byContradiction
      intro hh
      exact hmin ⟨D, hDY, fun E hE hED => hh ⟨E, hE, hED⟩⟩
    obtain ⟨E, hEY, hED⟩ := below
    obtain ⟨v, hvE⟩ := (hq.range E).mp (hY E hEY)
    obtain ⟨i, w, z, hwi, hzi, hvw, huz, hwz⟩ := (hq.relation v u E D hvE huD).mp hED
    obtain ⟨F, _, hwF⟩ := hq.projection.2.1 w (h.bound v w hvw).2
    have eq := hq.commute_l h hvw hvE hwF
    have hwB := (spec w).mpr ⟨(h.bound v w hvw).2, F, eq ▸ hEY, hwF⟩
    exact ⟨w, hwB, (ps u w).mpr ⟨hu, hwB, i, z, hwi, hzi, huz, hwz⟩⟩
  obtain ⟨D, hDY⟩ := hne
  obtain ⟨u, huD⟩ := (hq.range D).mp (hY D hDY)
  obtain ⟨f, hf, _, step⟩ := hDC B P u ((spec u).mpr ⟨(hq.projection.bound_l huD).1, D, hDY, huD⟩) serial
  exact hn f ((fn0_of_function_l (ZF.modelsKP hZF) hf).mono_target_l fun v hv => ((spec v).mp hv).1)
    (fun i j u v hij hiu hjv => ((ps u v).mp (step i j u v hij hiu hjv)).2.2)

end YesMetaZFC.SetTheory.Internal
