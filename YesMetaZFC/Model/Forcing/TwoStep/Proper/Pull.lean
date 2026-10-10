import YesMetaZFC.Model.Forcing.TwoStep.Proper.Decision

/-! # 二步主条件在固定首阶段泛型中的稠密见证

对首坐标的每次加强应用二步主性，得到一张真实可定义的稠密原像。
原泛型遇到该原像，因而共同加强的首坐标仍被接受，不另换首阶段泛型。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
include O hZF hU

theorem two_step_master_meet_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hT : Name_d M B T) {N v D r p s} (hm : Mstr_d M C S C N v)
    (hDN : M.mem D N) (hD : Dense_set_d M C S C D) (hr : Below_d M C S C r v)
    (hrp : KPair_d M r p s) (hp : U p) :
    ∃ x j a u, M.mem x D ∧ M.mem x N ∧ KPair_d M j a u ∧ U a ∧
      Below_d M C S C j r ∧ Entry_d M j x S := by
  let ρ : Env M 5 := ((((⟨fun _ => C, fun _ => C⟩ : Env M 1).push S).push N).push D).push r
  let φ : UnarySchema 5 := {
    body := .existsE (.existsE (.existsE (.conj (.mem (.bound 2) (.bound 5))
      (.conj (.mem (.bound 2) (.bound 6))
      (.conj (below_m (.bound 8) (.bound 7) (.bound 8) (.bound 1) (.bound 4))
      (.conj (entry_m (.bound 1) (.bound 2) (.bound 7)) (kpair_m (.bound 1) (.bound 3) .newest))))))) }
  have hφ a : φ.denote ρ a ↔ ∃ x j u, M.mem x D ∧ M.mem x N ∧
      Below_d M C S C j r ∧ Entry_d M j x S ∧ KPair_d M j a u := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, below_sat_l M hZF.1, entry_sat_l M hZF.1, kpair_sat_l M hZF.1]
    rfl
  obtain ⟨a, ha, x, j, u, hxD, hxN, hjr, hjx, hja⟩ := generic_pick_l hZF hU ⟨5, φ, ρ, hφ⟩ hp (by
    intro d hd
    obtain ⟨y, hyd, hyr⟩ := two_step_lift_l O hZF h L hT hr.1 hrp hd
    obtain ⟨x, hxD, hxN, j, hjy, hjx⟩ := hm.2.2 D hDN hD y (below_trans_l L hm.1 hyr hr)
    obtain ⟨a, u, hja, _, _, _⟩ := (h.conditions j).mp hjy.1
    have had := ((two_step_le_l h hjy.1 hyr.1 hja hyd).mp hjy.2.2).1
    exact ⟨a, had, x, j, u, hxD, hxN, below_trans_l L hr.1 hjy hyr, hjx, hja⟩)
  exact ⟨x, j, a, u, hxD, hxN, hja, ha, hjr, hjx⟩

/-- 后阶段稠密集在每个首坐标被接受的二步条件以下均能实际命中。 -/
theorem two_step_hits_possible_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    {F x p s} (hx : M.mem x C) (hxp : KPair_d M x p s) (hp : U p)
    {Q V Y : (E).Domain} (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T V)
    (hF : Qval_d M B R z U F Y) (hY : Dense_set_d E Q V Q Y) :
    ∃ y, Below_d M C S C y x ∧ Step_hits_d M B R z F y := by
  have hsN : Name_d M B s := ⟨W, ((two_step_mem_l h hxp).mp hx).1, h.closed⟩
  obtain ⟨a, hs⟩ := name_value_l (R := R) (z := z) (U := U) hsN
  let ρ := stage_env_l M A T F s
  let η := stage_env_l E Q V Y a
  let φ : Formula 1 4 := stage_dense_m (.bound 3) (.bound 2) (.bound 1) .newest
  have hφ : φ.FreeClosed := stage_dense_m_freeClosed _ _ _ _ rfl rfl rfl rfl
  have hρ : Env_val_d hZF ρ η := by
    intro t
    cases t with
    | free _ => exact hA
    | bound i => exact Fin.cases hs (Fin.cases hF (Fin.cases hT (fun _ => hA))) i
  have hd : Stage_dense_d E Q V Y a := by
    intro t ht _
    have htne : t ≠ Q := fun he => KP.mem_irrefl_d (ZF.modelsKP (preserves_zf_l O hZF hU)) Q (he ▸ ht)
    obtain ⟨u, hu, huY⟩ := hY.2 t ht htne
    exact ⟨u, hu.1, hu.2.2, huY⟩
  obtain ⟨c, hc, hforce⟩ := (forcing_truth_l O hZF hU φ hφ ρ η hρ).mpr
    ((stage_dense_sat_l E (extension_ext_l O hZF hU) η _ _ _ _).mpr hd)
  obtain ⟨d, hdU, hdp, hdc⟩ := hU.directed p c hp hc
  have hd' := hU.proper d hdU
  obtain ⟨y, hyd, hyx⟩ := two_step_lift_l O hZF h L (qval_name_l hT) hx hxp ⟨hd'.1, hd'.2, hdp⟩
  have hforce' := (forces_regular_l O hZF φ ρ (fun t => qval_name_l (hρ t))).1 c d (hU.proper c hc).1
    ⟨hd'.1, hd'.2, hdc⟩ hforce
  obtain ⟨k, hky, hk⟩ := two_step_dense_l O hZF h L (qval_name_l hT) (qval_name_l hF)
    hx hyx.1 hxp hyd hyx.2.2 hforce' y (below_refl_l L hyx.1 hyx.2.1)
  exact ⟨k, below_trans_l L hx hky hyx, hk⟩

end YesMetaZFC.Model.Forcing.Internal
