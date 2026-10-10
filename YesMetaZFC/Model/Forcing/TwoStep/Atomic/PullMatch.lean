import YesMetaZFC.Model.Forcing.TwoStep.Atomic.PullSyntax
import YesMetaZFC.Model.Forcing.TwoStep.Atomic.Match

/-! # 嵌套等号的第二阶段匹配提升

在首阶段泛型中解释嵌套等号，匹配后的条件和条目都回到原二步名称。
第一次真值定理再给出新的嵌套等号证书，作为内部双模拟的下一条边。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
include O hZF hU

theorem curry_pull_generic_match_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hT : Name_d M B T) {x y c a d q p s} (hx : Name_d M C x) (hy : Name_d M C y)
    (hc : M.mem c C) (he : Curry_pull_d M B R z A T C c x y)
    (had : Entry_d M a d x) (hq : Below_d M C S C q c) (hqd : Entry_d M q d S)
    (hqp : KPair_d M q p s) (hp : U p) : Curry_pull_wit_d M B R z A T C S q a y := by
  have names {x t} (ht : Curry_d M B C x t) : Name_d M B t :=
    curry_name_l M hZF (fun c p s hc hcp => by
      obtain ⟨hs, hp, _⟩ := (two_step_mem_l h hcp).mp hc
      exact ⟨hp.1, W, hs, h.closed⟩) ht
  obtain ⟨Q, hA⟩ := name_value_l (R := R) (z := z) (U := U) (show Name_d M B A from ⟨W, h.root, h.closed⟩)
  obtain ⟨D, hD⟩ := name_value_l (R := R) (z := z) (U := U) hT
  obtain ⟨p₀, s₀, u, v, hcp, hu, hv, he⟩ := he
  obtain ⟨hs₀, hp₀, _⟩ := (two_step_mem_l h hcp).mp hc
  obtain ⟨s₀', hs₀'⟩ := name_value_l (R := R) (z := z) (U := U) (show Name_d M B s₀ from ⟨W, hs₀, h.closed⟩)
  obtain ⟨u', huu⟩ := name_value_l (R := R) (z := z) (U := U) (names hu)
  obtain ⟨v', hvv⟩ := name_value_l (R := R) (z := z) (U := U) (names hv)
  have hqc := (two_step_le_l h hq.1 hc hqp hcp).mp hq.2.2
  have hp₀U := hU.upward p p₀ hp hp₀.1 hqc.1.2.2
  have hEN := preserves_zf_l O hZF hU
  have huN := curry_second_name_l O hZF hU h hx hu hA huu
  have hvN := curry_second_name_l O hZF hU h hy hv hA hvv
  have hEq : Eq_force_d E Q D Q s₀' u' v' := he.elim
    (fun he => (iter_eq_truth_l O hZF hU hA hD hs₀' huu hvv).mp ⟨p₀, hp₀U, he⟩)
    (fun he => eq_force_symm_l hEN hvN huN
      ((iter_eq_truth_l O hZF hU hA hD hs₀' hvv huu).mp ⟨p₀, hp₀U, he⟩))
  obtain ⟨hs, _, hsm⟩ := (two_step_mem_l h hqp).mp hq.1
  obtain ⟨s', hss⟩ := name_value_l (R := R) (z := z) (U := U) (show Name_d M B s from ⟨W, hs, h.closed⟩)
  have hsQ := (qval_mem_forcing_l O hZF hU hss hA).mp ⟨p, hp, hsm⟩
  have hss₀ := (rel_force_truth_l O hZF hU hss hs₀' hD).mp ⟨p, hp, hqc.2⟩
  have hdC := (name_entry_l M hx had).2
  obtain ⟨pd, sd, hdp, hsd, hpd, _⟩ := (h.conditions d).mp hdC
  obtain ⟨sd', hsdd⟩ := name_value_l (R := R) (z := z) (U := U) (show Name_d M B sd from ⟨W, hsd, h.closed⟩)
  have hqd' := (two_step_le_l h hq.1 hdC hqp hdp).mp hqd
  have hpdU := hU.upward p pd hp hpd.1 hqd'.1.2.2
  have hssd := (rel_force_truth_l O hZF hU hss hsdd hD).mp ⟨p, hp, hqd'.2⟩
  obtain ⟨ua, hau, hua, _⟩ := two_step_curry_l M hZF h a
  obtain ⟨a', hua'⟩ := name_value_l (R := R) (z := z) (U := U) hua
  have had' := (curry_val_entry_l O hZF hU h hu huu).mpr ⟨a, d, ua, pd, sd, had, hdC, hdp, hpdU, hau, hua', hsdd⟩
  have hsq : Below_d E Q D Q s' s₀' :=
    ⟨hsQ, fun hh => KP.mem_irrefl_d (ZF.modelsKP hEN) Q (hh ▸ hsQ), hss₀⟩
  obtain ⟨r', e', f', hrs, hef, hrf, hae⟩ := ((eq_force_unfold_l E hEN huN hvN).mp hEq).2.1 a' sd' had' s' hsq hssd
  obtain ⟨e, f, ve, pe, se, hef₀, hfC, hfp, hpe, hev, hve', hse'⟩ :=
    (curry_val_entry_l O hZF hU h hv hvv).mp hef
  obtain ⟨r, l, t, hrl, hl, htr, hrq, hreff⟩ := two_step_common_l O hZF hU h L hA hD
    hq.1 hfC hqp hfp hp hpe hss hse' hrs.1 hrs.2.2 hrf
  obtain ⟨k, hk, hit⟩ := (iter_eq_truth_l O hZF hU hA hD htr hua' hve').mpr hae
  obtain ⟨j, hj, hjk, hjl⟩ := hU.directed k l hk hl
  have hj' := hU.proper j hj
  have hρ : ∀ w : Term 5, Name_d M B (w.eval (iter_eq_env_l A T t ua ve)) := by
    intro w
    cases w with
    | free _ => exact qval_name_l hA
    | bound i => exact Fin.cases (qval_name_l hve') (Fin.cases (qval_name_l hua')
        (Fin.cases (qval_name_l htr) (Fin.cases hT (fun _ => qval_name_l hA)))) i
  have hit' : Iter_eq_d M B R z A T j t ua ve :=
    (forces_regular_l O hZF iter_eq_body_m (iter_eq_env_l A T t ua ve) hρ).1 k j (hU.proper k hk).1 ⟨hj'.1, hj'.2, hjk⟩ hit
  obtain ⟨w, hwj, hwr⟩ := two_step_lift_l O hZF h L hT hrq.1 hrl ⟨hj'.1, hj'.2, hjl⟩
  exact ⟨w, e, f, below_trans_l L hq.1 hwr hrq, hef₀,
    (below_trans_l L hfC hwr hreff).2.2, j, t, ua, ve, hwj, hau, hev, Or.inl hit'⟩

end YesMetaZFC.Model.Forcing.Internal
