import YesMetaZFC.Model.Forcing.TwoStep.Generic.DenseImage

/-! # 保留首阶段泛型的二步等号匹配

二步等号给出的匹配见证须保留被首阶段泛型接受的第一坐标。把见证谓词分离成
真实条件集，再把其稠密性投影到首阶段；仅有二步加强的存在性不足以完成此步。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain} {U : M.Domain → Prop}

/-- 匹配原名称条目时，自动取得第一坐标仍属于给定泛型的加强和子名称等号。 -/
theorem two_step_eq_pick_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (hU : Generic_d M B R z U) (h : Two_step_d M B R z b A T W C S)
    (L : Cond_order_d M C S C) (hT : Name_d M B T) {x y c a d w p s}
    (hx : Name_d M C x) (hy : Name_d M C y) (he : Eq_force_d M C S C c x y)
    (had : Entry_d M a d x) (hw : Below_d M C S C w c) (hwd : Entry_d M w d S)
    (hwp : KPair_d M w p s) (hp : U p) :
    ∃ r q t e f, Below_d M C S C r w ∧ KPair_d M r q t ∧ U q ∧
      Entry_d M e f y ∧ Entry_d M r f S ∧ Eq_force_d M C S C r a e := by
  obtain ⟨D, hD⟩ := defined_set_l M hZF (wit_defined_l M hZF.1 false C S C a y) C
  have hd : Dense_d M C S C (fun r => M.mem r D) w := by
    intro q hq
    have hqc := below_trans_l L he.1 hq hw
    have hqd := L.trans q w d hq.1 hw.1 (name_entry_l M hx had).2 hq.2.2 hwd
    obtain ⟨r, e, f, hr, hef, hrf, hae⟩ := ((eq_force_unfold_l M hZF hx hy).mp he).2.1 a d had q hqc hqd
    exact ⟨r, hr, (hD r).mpr ⟨hr.1, e, f, hef, hrf, hae⟩⟩
  obtain ⟨q, hq, r, t, hr, hrD, hrq, hrw⟩ := generic_pick_l hZF hU
    (proj_below_defined_l M hZF.1 C S D w) hp
    (two_step_projection_dense_l O hZF h L hT hw.1 hwp hd)
  obtain ⟨e, f, hef, hrf, hae⟩ := ((hD r).mp hrD).2
  exact ⟨r, q, t, e, f, ⟨hr, fun hh => KP.mem_irrefl_d (ZF.modelsKP hZF) C (hh ▸ hr), hrw⟩,
    hrq, hq, hef, hrf, hae⟩

end YesMetaZFC.Model.Forcing.Internal
