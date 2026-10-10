import YesMetaZFC.SetTheory.InnerModel.ProofCode.Global.Order

/-! # L 对象初段的集合化及 Σ₁ 函数图

一个对象的前驱集合，恰好是其最小码名初段的完整求值像。不同码名同值时，
最小代表不会变晚，因而像中没有多余对象，也没有遗漏任何前驱。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem pm_min_le_l (hM : M.Models KPi) {v u x : M.Domain} (hv : Pm_min_d v x) (hu : Pn_eval_d u x) : v = u ∨ Pn_lt_d v u := by
  rcases pn_compare_l hM hv.valid_l (pn_eval_domain_l hu) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hv.2 u hu h).elim

theorem lo_predecessor_iff_l (hM : M.Models KPi) {v x I : M.Domain} (hv : Pm_min_d v x) (hi : Pi_initial_d v I) (y : M.Domain) :
    Lo_lt_d y x ↔ ∃ u, M.mem u I ∧ Pn_eval_d u y := by
  constructor
  · rintro ⟨u, w, hu, hw, hlt⟩
    have he := pm_min_unique_l hM hw hv; subst w
    exact ⟨u, (hi.2 u).mpr ⟨hu.valid_l, hlt⟩, hu.1⟩
  · rintro ⟨u, huI, huy⟩
    obtain ⟨w, hw⟩ := pm_min_exists_l hM ((pn_cover_l hM y).mpr ⟨u, huy⟩)
    obtain ⟨hu, huv⟩ := (hi.2 u).mp huI
    refine ⟨w, v, hw, hv, ?_⟩
    exact (pm_min_le_l hM hw huy).elim (fun he => he.symm ▸ huv)
      (fun hwu => pn_trans_l hM hw.valid_l hu hv.valid_l hwu huv)

theorem pn_eval_image_sat_l (hM : M.Models KPi) {I Y : M.Domain} (hi : ∀ u, M.mem u I → Pn_valid_d u) (ρ : Env M 0) :
    pn_eval_s.image.schema.denote ρ I Y ↔ ∀ y, M.mem y Y ↔ ∃ u, M.mem u I ∧ Pn_eval_d u y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  rw [S1_binary.image_sat_l hKP _ _ _ _
    (fun u hu => (pn_eval_total_l hM (hi u hu)).imp (fun y hy => (pn_eval_sat_l hKP ρ u y).mpr hy))
    (fun u _ y z hy hz => pn_eval_unique_l hM ((pn_eval_sat_l hKP ρ u y).mp hy) ((pn_eval_sat_l hKP ρ u z).mp hz))]
  simp only [pn_eval_sat_l hKP]

def Lo_initial_d (x Y : M.Domain) : Prop := L_d x ∧ ∀ y, M.mem y Y ↔ Lo_lt_d y x
def lo_initial_s : S1_binary 0 := pm_min_s.comp (pi_initial_s.comp pn_eval_s.image)

theorem lo_initial_exists_l (hM : M.Models KPi) {x : M.Domain} (hx : L_d x) : ∃ Y, Lo_initial_d x Y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  let ρ := jh_env_l x
  obtain ⟨v, hv⟩ := pm_min_exists_l hM hx
  obtain ⟨I, hi⟩ := pi_initial_exists_l hM hv.valid_l
  obtain ⟨Y, hy⟩ := KP.s1_image_l hKP pn_eval_s ρ I
    (fun u hu => (pn_eval_total_l hM ((hi.2 u).mp hu).1).imp (fun y hy => (pn_eval_sat_l hKP ρ u y).mpr hy))
    (fun u _ y z hy hz => pn_eval_unique_l hM ((pn_eval_sat_l hKP ρ u y).mp hy) ((pn_eval_sat_l hKP ρ u z).mp hz))
  refine ⟨Y, hx, fun y => (hy y).trans ?_⟩
  exact (exists_congr fun u => and_congr_right fun _ => pn_eval_sat_l hKP ρ u y).trans (lo_predecessor_iff_l hM hv hi y).symm

theorem lo_initial_unique_l (hE : Extensional M) {x Y Z : M.Domain} (hy : Lo_initial_d x Y) (hz : Lo_initial_d x Z) : Y = Z :=
  hE.eq_of_same_members Y Z (fun y => (hy.2 y).trans (hz.2 y).symm)

theorem lo_initial_sat_l (hM : M.Models KPi) (ρ : Env M 0) (x Y : M.Domain) :
    lo_initial_s.schema.denote ρ x Y ↔ Lo_initial_d x Y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  rw [lo_initial_s, S1_binary.comp_sat_l hKP]
  simp only [pm_min_sat_l hM, S1_binary.comp_sat_l hKP, pi_initial_sat_l hM]
  constructor
  · rintro ⟨v, hv, I, hi, hY⟩
    have hy := (pn_eval_image_sat_l hM (fun u hu => ((hi.2 u).mp hu).1) ρ).mp hY
    exact ⟨(pm_min_iff_l hM x).mpr ⟨v, hv⟩, fun y => (hy y).trans (lo_predecessor_iff_l hM hv hi y).symm⟩
  · intro hY
    obtain ⟨v, hv⟩ := pm_min_exists_l hM hY.1
    obtain ⟨I, hi⟩ := pi_initial_exists_l hM hv.valid_l
    exact ⟨v, hv, I, hi, (pn_eval_image_sat_l hM (fun u hu => ((hi.2 u).mp hu).1) ρ).mpr
      (fun y => (hY.2 y).trans (lo_predecessor_iff_l hM hv hi y))⟩

end YesMetaZFC.SetTheory.InnerModel
