import YesMetaZFC.Model.Forcing.TwoStep.Generic.Second

/-! # 二步泛型从两阶段数据精确恢复

组合条件要求第一坐标进入首阶段泛型，第二坐标的解释进入后阶段泛型。
恢复方向把第二阶段的真实序关系加强为首阶段力迫见证，再利用二步提升与传递性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def Compose_generic_d (M : SetTheory.Structure.{u}) (B R z C : M.Domain)
    (U : M.Domain → Prop) (H : Name_quot_l M B R z U → Prop) (x : M.Domain) : Prop :=
  M.mem x C ∧ ∃ p s a, KPair_d M x p s ∧ U p ∧ Qval_d M B R z U s a ∧ H a

variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain} {V : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
local notation "G" => First_generic_d M B R V
local notation "E" => extension_l M hZF B R z G
include O hZF

/-- 分解后重组精确恢复原泛型滤子，适用于名称有重复代表的预序。 -/
theorem two_step_recover_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hV : Generic_d M C S C V) {Q D : (E).Domain}
    (hA : Qval_d M B R z G A Q) (hT : Qval_d M B R z G T D) (x : M.Domain) :
    V x ↔ Compose_generic_d M B R z C G (Second_generic_d M hZF B R z G V Q D) x := by
  have hG := two_step_generic_l O hZF h L (qval_name_l hT) hV
  constructor
  · intro hx
    have hxC := (hV.proper x hx).1
    obtain ⟨p, s, hxp, hs, hp, hm⟩ := (h.conditions x).mp hxC
    obtain ⟨a, ha⟩ := name_value_l (R := R) (z := z) (U := G) (show Name_d M B s from ⟨W, hs, h.closed⟩)
    have hpG : G p := ⟨hp.1, x, p, s, hx, hxp, O.refl p hp.1⟩
    have haQ := (qval_mem_forcing_l O hZF hG ha hA).mp ⟨p, hpG, hm⟩
    have haa := (rel_force_truth_l O hZF hG ha ha hT).mp
      ⟨p, hpG, ((two_step_le_l h hxC hxC hxp hxp).mp (L.refl x hxC)).2⟩
    exact ⟨hxC, p, s, a, hxp, hpG, ha, haQ, x, p, s, a, hx, hxp, ha, haa⟩
  · rintro ⟨hxC, p, s, a, hxp, hpG, hs, _, y, q, t, c, hy, hyq, ht, hca⟩
    obtain ⟨r, hrG, hrp, hts⟩ := rel_force_below_l O hZF hG hpG ht hs hT hca
    obtain ⟨hrB, v, d, f, hv, hvd, hdr⟩ := hrG
    obtain ⟨w, hw, hwy, hwv⟩ := hV.directed y v hy hv
    have hyC := (hV.proper y hy).1
    have hvC := (hV.proper v hv).1
    have hwC := (hV.proper w hw).1
    obtain ⟨k, u, hwk, _, hkb, _⟩ := (h.conditions w).mp hwC
    have hdB := ((two_step_mem_l h hvd).mp hvC).2.1.1
    have hkd := ((two_step_le_l h hwC hvC hwk hvd).mp hwv).1.2.2
    have hkr : Below_d M B R z k r := ⟨hkb.1, hkb.2.1, O.trans k d r hkb.1 hdB hrB hkd hdr⟩
    obtain ⟨hkq, hut⟩ := (two_step_le_l h hwC hyC hwk hyq).mp hwy
    obtain ⟨j, hjk, hjy⟩ := two_step_lift_l O hZF h L (qval_name_l hT) hyC hyq hkq
    have hjx := (two_step_le_l h hjy.1 hxC hjk hxp).mpr
      ⟨below_trans_l O ((two_step_mem_l h hxp).mp hxC).2.1.1 hkr hrp,
        (rel_force_regular_l O hZF (qval_name_l hT) (qval_name_l ht) (qval_name_l hs)).1 r k hrB hkr hts⟩
    have hwj := (two_step_le_l h hwC hjy.1 hwk hjk).mpr ⟨below_refl_l O hkb.1 hkb.2.1, hut⟩
    exact hV.upward w x hw hxC (L.trans w j x hwC hjy.1 hxC hwj hjx)

end YesMetaZFC.Model.Forcing.Internal
