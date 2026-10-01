import YesMetaZFC.SetTheory.InnerModel.ProofCode.Minimum.Representative

/-! # 最小代表的 Σ₁ 图

否定只用于“完整表中没有这一条目”的 Δ₀ 检查；初段和完整求值表都有正向
Σ₁ 证书。因此这里没有对无界的 Σ₁ 求值关系直接取否定。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Pm_build_d (ρ : Env M 0) (v x : M.Domain) : Prop := ∃ I F,
  pi_initial_s.schema.denote ρ v I ∧ (sg_table_s pn_eval_s).schema.denote ρ I F ∧ pn_eval_s.schema.denote ρ v x ∧
    ∀ u, M.mem u I → ¬ Rd_entry_d u x F

def pm_min_s : S1_binary 0 where
  matrix := {
    body := Formula.existsMem .newest <| Formula.existsMem (.bound 1) <| Formula.existsMem (.bound 2) <|
      Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <|
        .conj (pi_initial_s.matrix_m Fin.elim0 (.bound 6) (.bound 4) (.bound 2)) <|
          .conj ((sg_table_s pn_eval_s).matrix_m Fin.elim0 (.bound 4) (.bound 3) (.bound 1)) <|
            .conj (pn_eval_s.matrix_m Fin.elim0 (.bound 6) (.bound 7) .newest)
              (Formula.forallMem (.bound 4) (.neg (rd_entry0_m .newest (.bound 8) (.bound 4))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (pi_initial_s.matrix.delta0.bind_l _) (.conj ((sg_table_s pn_eval_s).matrix.delta0.bind_l _)
        (.conj (pn_eval_s.matrix.delta0.bind_l _) (.forallMem _ (.neg (rd_entry0_delta_l ..)))))))))) }

theorem pm_min_build_l (hKP : M.Models KP) (ρ : Env M 0) (x v : M.Domain) :
    pm_min_s.schema.denote ρ x v ↔ Pm_build_d ρ v x := by
  rw [S1_binary.sat_l]
  simp only [pm_min_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    po_matrix_env_l pi_initial_s ρ, po_matrix_env_l (sg_table_s pn_eval_s) ρ, po_matrix_env_l pn_eval_s ρ,
    Formula.satisfies_forallMem_iff, Formula.satisfies_neg_iff, rd_entry0_sat_l hKP.1]
  change (∃ T I, M.mem I T ∧ ∃ F, M.mem F T ∧ ∃ Wi, M.mem Wi T ∧ ∃ Wf, M.mem Wf T ∧ ∃ Wv, M.mem Wv T ∧
    pi_initial_s.matrix_binary.toBinarySchema.denote (ρ.push v) I Wi ∧
      (sg_table_s pn_eval_s).matrix_binary.toBinarySchema.denote (ρ.push I) F Wf ∧
        pn_eval_s.matrix_binary.toBinarySchema.denote (ρ.push v) x Wv ∧ ∀ u, M.mem u I → ¬ Rd_entry_d u x F) ↔ _
  constructor
  · rintro ⟨T, I, _, F, _, Wi, _, Wf, _, Wv, _, hi, hf, hv, hn⟩
    exact ⟨I, F, (pi_initial_s.sat_l ρ v I).mpr ⟨Wi, hi⟩, ((sg_table_s pn_eval_s).sat_l ρ I F).mpr ⟨Wf, hf⟩,
      (pn_eval_s.sat_l ρ v x).mpr ⟨Wv, hv⟩, hn⟩
  · rintro ⟨I, F, hi, hf, hv, hn⟩
    obtain ⟨Wi, hi⟩ := (pi_initial_s.sat_l ρ v I).mp hi
    obtain ⟨Wf, hf⟩ := ((sg_table_s pn_eval_s).sat_l ρ I F).mp hf
    obtain ⟨Wv, hv⟩ := (pn_eval_s.sat_l ρ v x).mp hv
    obtain ⟨T, ht⟩ := kp_finite_cover_l hKP [I, F, Wi, Wf, Wv]
    exact ⟨T, I, (ht I (by simp)).2, F, (ht F (by simp)).2, Wi, (ht Wi (by simp)).2,
      Wf, (ht Wf (by simp)).2, Wv, (ht Wv (by simp)).2, hi, hf, hv, hn⟩

theorem pm_min_sat_l (hM : M.Models KPi) (ρ : Env M 0) (x v : M.Domain) :
    pm_min_s.schema.denote ρ x v ↔ Pm_min_d v x := by
  let hKP := (KPi.models_iff_l.mp hM).1
  rw [pm_min_build_l hKP]
  constructor
  · rintro ⟨I, F, hi, hf, hv, hn⟩
    have hI := (pi_initial_sat_l hM ρ v I).mp hi
    have hF := (pn_eval_table_sat_l hM (fun u hu => ((hI.2 u).mp hu).1) ρ).mp hf
    refine ⟨(pn_eval_sat_l hKP ρ v x).mp hv, fun u hu hlt => ?_⟩
    have hui := (hI.2 u).mpr ⟨pn_eval_domain_l hu, hlt⟩
    exact hn u hui ((hF.entry_l hKP).mpr ⟨hui, (pn_eval_sat_l hKP ρ u x).mpr hu⟩)
  · intro hv
    obtain ⟨I, hi⟩ := pi_initial_exists_l hM hv.valid_l
    have valid u hu := ((hi.2 u).mp hu).1
    obtain ⟨F, hf⟩ := pn_eval_table_exists_l hM valid ρ
    refine ⟨I, F, (pi_initial_sat_l hM ρ v I).mpr hi, (pn_eval_table_sat_l hM valid ρ).mpr hf,
      (pn_eval_sat_l hKP ρ v x).mpr hv.1, fun u hui hue => ?_⟩
    exact hv.2 u ((pn_eval_sat_l hKP ρ u x).mp ((hf.entry_l hKP).mp hue).2) ((hi.2 u).mp hui).2

end YesMetaZFC.SetTheory.InnerModel
