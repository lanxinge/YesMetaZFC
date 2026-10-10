import YesMetaZFC.SetTheory.InnerModel.ProofCode.Initial.Formula

/-! # 精确全局前驱集合的存在、唯一性及 Σ₁ 图 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Pi_initial_d (w I : M.Domain) : Prop := Pn_valid_d w ∧ ∀ v, M.mem v I ↔ Pn_valid_d v ∧ Pn_lt_d v w

theorem pi_build_correct_l (hM : M.Models KPi) {w I : M.Domain} (hi : Pi_build_d w I) : Pi_initial_d w I := by
  obtain ⟨a, h, c, ω, C, B, D, hw, ha, hω, hc, hb, hd, hwD, hi⟩ := hi
  have ht := rd_closure_transitive_l hM ha.transitive hc
  have family := pi_box_family_l (KPi.models_iff_l.mp hM).1.1 ha hω hb
  have hD := (pg_filter_sat_l hM ht family).mp hd
  have valid v hv := ((hD v).mp hv).2
  have hvw := valid w hwD
  have name : Pn_name_d w a h c := by
    obtain ⟨b, n, d, hp⟩ := hvw
    obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hw hp.1
    exact hp
  have hI := (pi_slice_sat_l hM hvw valid).mp hi
  refine ⟨hvw, fun v => (hI v).trans ?_⟩
  exact ⟨fun h => ⟨valid v h.1, h.2⟩, fun h => ⟨(hD v).mpr
    ⟨pi_box_predecessor_l hM name hω hc hb h.1 h.2, h.1⟩, h.2⟩⟩

theorem pi_build_exists_l (hM : M.Models KPi) {w : M.Domain} (hw : Pn_valid_d w) : ∃ I, Pi_build_d w I := by
  obtain ⟨a, h, c, hn⟩ := hw
  obtain ⟨C, hc, _⟩ := hn.2.2.2.2
  obtain ⟨ω, hω⟩ := omega0_exists_l hM
  obtain ⟨B, hb⟩ := pi_box_exists_l (KPi.models_iff_l.mp hM).1 a ω C
  have ht := rd_closure_transitive_l hM hn.2.1.transitive hc
  have family := pi_box_family_l (KPi.models_iff_l.mp hM).1.1 hn.2.1 hω hb
  obtain ⟨D, hd⟩ := pg_filter_exists_l hM ht family
  have hD := (pg_filter_sat_l hM ht family).mp hd
  have hwD := (hD w).mpr ⟨pi_box_contains_l hM hn hω hc hb, a, h, c, hn⟩
  obtain ⟨I, hi⟩ := pi_slice_exists_l hM (show Pn_valid_d w from ⟨a, h, c, hn⟩) (fun v hv => ((hD v).mp hv).2)
  exact ⟨I, a, h, c, ω, C, B, D, hn.1, hn.2.1, hω, hc, hb, hd, hwD, hi⟩

theorem pi_initial_unique_l (hE : Extensional M) {w I J : M.Domain} (hi : Pi_initial_d w I) (hj : Pi_initial_d w J) : I = J :=
  hE.eq_of_same_members I J (fun v => (hi.2 v).trans (hj.2 v).symm)

theorem pi_initial_exists_l (hM : M.Models KPi) {w : M.Domain} (hw : Pn_valid_d w) : ∃ I, Pi_initial_d w I :=
  (pi_build_exists_l hM hw).imp (fun _ hi => pi_build_correct_l hM hi)

theorem pi_initial_sat_l (hM : M.Models KPi) (ρ : Env M 0) (w I : M.Domain) :
    pi_initial_s.schema.denote ρ w I ↔ Pi_initial_d w I := by
  rw [pi_initial_build_l (KPi.models_iff_l.mp hM).1]
  refine ⟨pi_build_correct_l hM, fun hi => ?_⟩
  obtain ⟨J, hj⟩ := pi_build_exists_l hM hi.1
  exact pi_initial_unique_l (KPi.models_iff_l.mp hM).1.1 (pi_build_correct_l hM hj) hi ▸ hj

end YesMetaZFC.SetTheory.InnerModel
