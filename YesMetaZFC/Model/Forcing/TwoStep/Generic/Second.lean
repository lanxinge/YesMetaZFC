import YesMetaZFC.Model.Forcing.TwoStep.Generic.Density

/-! # 二步泛型的第二阶段分解

第二坐标在第一阶段泛型商中解释，再取序向上闭包。稠密性使用实际名称公式的
真值定理与地模型二步稠密集提升，因此结论覆盖全部扩张内稠密集。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def Second_generic_d (M : SetTheory.Structure.{u}) (hZF : M.Models ZF) (B R z : M.Domain)
    (U V : M.Domain → Prop) (Q D q : Name_quot_l M B R z U) : Prop :=
  q ∈ Q ∧ ∃ x p s a, V x ∧ KPair_d M x p s ∧ Qval_d M B R z U s a ∧
    Entry_d (extension_l M hZF B R z U) a q D

variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain} {V : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
local notation "G" => First_generic_d M B R V
local notation "E" => extension_l M hZF B R z G
include O hZF

/-- 每个二步泛型都分解出第一阶段扩张上的实际泛型，不要求外部良基性或可数性。 -/
theorem two_step_second_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hP : Forces_d M B R z (preord_m (.bound 0) (.bound 1)) (ord_env_l M A T) b)
    (hV : Generic_d M C S C V) {Q D : (E).Domain}
    (hA : Qval_d M B R z G A Q) (hT : Qval_d M B R z G T D) :
    Generic_d E Q D Q (Second_generic_d M hZF B R z G V Q D) := by
  have hU := two_step_generic_l O hZF h L (qval_name_l hT) hV
  have hE := preserves_zf_l O hZF hU
  have pos {q : (E).Domain} (hq : q ∈ Q) : q ≠ Q :=
    fun he => KP.mem_irrefl_d (ZF.modelsKP hE) Q (he ▸ hq)
  have coords {x} (hx : V x) := (h.conditions x).mp (hV.proper x hx).1
  have coord {x p s a} (hx : V x) (hxp : KPair_d M x p s) (hs : Qval_d M B R z G s a) :
      G p ∧ a ∈ Q := by
    obtain ⟨_, hp, hm⟩ := (two_step_mem_l h hxp).mp (hV.proper x hx).1
    have hUp : G p := ⟨hp.1, x, p, s, hx, hxp, O.refl p hp.1⟩
    exact ⟨hUp, (qval_mem_forcing_l O hZF hU hs hA).mp ⟨p, hUp, hm⟩⟩
  obtain ⟨x₀, hx₀⟩ := hV.inhabited
  obtain ⟨p₀, s₀, h₀, hs₀, hp₀, _⟩ := coords hx₀
  have hb : G b := ⟨h.base, x₀, p₀, s₀, hx₀, h₀, hp₀.2.2⟩
  have P := two_step_preord_l O hZF hU hA hT hb hP
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨hq.1, pos hq.1⟩
  · obtain ⟨a, ha⟩ := name_value_l (R := R) (z := z) (U := G) (show Name_d M B s₀ from ⟨W, hs₀, h.closed⟩)
    have haQ := (coord hx₀ h₀ ha).2
    exact ⟨a, haQ, x₀, p₀, s₀, a, hx₀, h₀, ha, P.1 a haQ⟩
  · rintro q r ⟨hq, x, p, s, a, hx, hxp, hs, haq⟩ hr hqr
    exact ⟨hr, x, p, s, a, hx, hxp, hs, P.2 a q r (coord hx hxp hs).2 hq hr haq hqr⟩
  · rintro q r ⟨hq, x, p, s, a, hx, hxp, hs, haq⟩ ⟨hr, y, t, v, c, hy, hyt, hv, hcr⟩
    obtain ⟨w, hw, hwx, hwy⟩ := hV.directed x y hx hy
    obtain ⟨d, u, hwd, hu, _, _⟩ := coords hw
    obtain ⟨e, he⟩ := name_value_l (R := R) (z := z) (U := G) (show Name_d M B u from ⟨W, hu, h.closed⟩)
    have heQ := coord hw hwd he
    have hea := (rel_force_truth_l O hZF hU he hs hT).mp ⟨d, heQ.1,
      ((two_step_le_l h (hV.proper w hw).1 (hV.proper x hx).1 hwd hxp).mp hwx).2⟩
    have hec := (rel_force_truth_l O hZF hU he hv hT).mp ⟨d, heQ.1,
      ((two_step_le_l h (hV.proper w hw).1 (hV.proper y hy).1 hwd hyt).mp hwy).2⟩
    exact ⟨e, ⟨heQ.2, w, d, u, e, hw, hwd, he, P.1 e heQ.2⟩,
      P.2 e a q heQ.2 (coord hx hxp hs).2 hq hea haq,
      P.2 e c r heQ.2 (coord hy hyt hv).2 hr hec hcr⟩
  · rintro q ⟨hq, x, p, s, a, hx, hxp, hs, haq⟩ F hDense
    have haQ := (coord hx hxp hs).2
    have hd : Stage_dense_d E Q D F a := by
      intro v hv hva
      obtain ⟨w, hw, hwF⟩ := hDense v ⟨hv, pos hv, P.2 v a q hv haQ hq hva haq⟩
      exact ⟨w, hw.1, hw.2.2, hwF⟩
    obtain ⟨f, hfN, hf⟩ := value_name_l F
    let ρ := stage_env_l M A T f s
    let η := stage_env_l E Q D F a
    let φ : Formula 1 4 := stage_dense_m (.bound 3) (.bound 2) (.bound 1) (.bound 0)
    have hφ : φ.FreeClosed := stage_dense_m_freeClosed _ _ _ _ rfl rfl rfl rfl
    have hρ : Env_val_d hZF ρ η := by
      intro v
      cases v with
      | free _ => exact hA
      | bound i => exact Fin.cases hs (Fin.cases hf (Fin.cases hT (fun _ => hA))) i
    have hd' : Formula.satisfies η φ := (stage_dense_sat_l E (extension_ext_l O hZF hU) η _ _ _ _).mpr hd
    obtain ⟨c, hc, hφc⟩ := (forcing_truth_l O hZF hU φ hφ ρ η hρ).mpr hd'
    obtain ⟨hcB, y, d, t, hy, hyd, hdc⟩ := hc
    obtain ⟨v, hv, hvx, hvy⟩ := hV.directed x y hx hy
    obtain ⟨r, w, hvr, _, hr, _⟩ := coords hv
    have hyC := (hV.proper y hy).1
    have hvC := (hV.proper v hv).1
    have hdB := ((two_step_mem_l h hyd).mp hyC).2.1.1
    have hrd := ((two_step_le_l h hvC hyC hvr hyd).mp hvy).1.2.2
    have hφr := (forces_regular_l O hZF φ ρ (fun t => qval_name_l (hρ t))).1 c r hcB
      ⟨hr.1, hr.2.1, O.trans r d c hr.1 hdB hcB hrd hdc⟩ hφc
    have hdV := two_step_dense_l O hZF h L (qval_name_l hT) hfN (hV.proper x hx).1 hvC hxp hvr hvx hφr
    obtain ⟨u, hu, d, t, hud, htF⟩ := generic_pick_l hZF hV (step_hits_defined_l M hZF.1 B R z f) hv hdV
    have htW := ((two_step_mem_l h hud).mp (hV.proper u hu).1).1
    obtain ⟨v, htv⟩ := name_value_l (R := R) (z := z) (U := G) (show Name_d M B t from ⟨W, htW, h.closed⟩)
    have hvQ := coord hu hud htv
    exact ⟨v, ⟨hvQ.2, u, d, t, v, hu, hud, htv, P.1 v hvQ.2⟩,
      (qval_mem_forcing_l O hZF hU htv hf).mp ⟨d, hvQ.1, htF⟩⟩

/-- 一次提取两阶段泛型与第二阶段合法条件序；名称解释和关系限制均自动完成。 -/
theorem two_step_factors_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hT : Name_d M B T)
    (hP : Forces_d M B R z (preord_m (.bound 0) (.bound 1)) (ord_env_l M A T) b)
    (hV : Generic_d M C S C V) : Generic_d M B R z G ∧
      ∃ Q D J : (E).Domain, Qval_d M B R z G A Q ∧ Qval_d M B R z G T D ∧
        (∀ p q, Entry_d E p q J ↔ p ∈ Q ∧ q ∈ Q ∧ Entry_d E p q D) ∧
        Cond_order_d E Q J Q ∧ Generic_d E Q J Q (Second_generic_d M hZF B R z G V Q D) ∧
        ∀ {a n} (φ : Formula a n) (ρ : Env E n), (∀ t : Term n, Name_d E Q (t.eval ρ)) →
          ∀ p, p ∈ Q → (Forces_d E Q D Q φ ρ p ↔ Forces_d E Q J Q φ ρ p) := by
  have hG := two_step_generic_l O hZF h L hT hV
  obtain ⟨Q, hQ⟩ := name_value_l (R := R) (z := z) (U := G) (show Name_d M B A from ⟨W, h.root, h.closed⟩)
  obtain ⟨D, hD⟩ := name_value_l (R := R) (z := z) (U := G) hT
  obtain ⟨x, hx⟩ := hV.inhabited
  obtain ⟨p, s, hxp, _, hp, _⟩ := (h.conditions x).mp (hV.proper x hx).1
  have hb : G b := ⟨h.base, x, p, s, hx, hxp, hp.2.2⟩
  obtain ⟨J, hJ, LJ, hGeneric, hForces⟩ := preord_order_l (preserves_zf_l O hZF hG)
    (two_step_preord_l O hZF hG hQ hD hb hP)
  exact ⟨hG, Q, D, J, hQ, hD, hJ, LJ, (hGeneric _).mp (two_step_second_l O hZF h L hP hV hQ hD), hForces⟩

end YesMetaZFC.Model.Forcing.Internal
