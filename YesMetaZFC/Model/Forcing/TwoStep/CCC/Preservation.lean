import YesMetaZFC.Model.Forcing.TwoStep.CCC.Forcing

/-! # 任意名称后继的 CCC 保持

二步反链的被接受索引名称被迫可数。最大值原理给出一个实际单射名称，首阶段
CCC 对其每个自然数值计数，再把全部旧反链成员覆盖，得到二步 CCC。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S ω : M.Domain}

/-- CCC 偏序迭代任意被迫 CCC 的名称偏序仍为 CCC。 -/
theorem two_step_ccc_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
    (hω : M.IsOmega ω)
    (hc : Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R z)
    (h : Two_step_d M B R z b A T W C S) (hT : Name_d M B T)
    (hP : Forces_d M B R z (preord_m (.bound 0) (.bound 1)) (ord_env_l M A T) b)
    (hC : Forces_d M B R z (ccc_exists_m (.bound 0) (.bound 1)) (ord_env_l M A T) b) :
    Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω C S C := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  intro D hd
  classical
  by_cases hb : b = z
  · apply ZF.exists_inclusionInjection hZF I
    intro x hx
    obtain ⟨p, _, _, _, hp, _⟩ := (h.conditions x).mp (hd.1 x hx).1
    exact False.elim (hp.2.1 (O.zero p hp.1 (hb ▸ hp.2.2)))
  · obtain ⟨t, g, ht, hg, hi⟩ := step_index_l hZF h (fun x hx => (hd.1 x hx).1)
    obtain ⟨w, hw, hwn, _⟩ := zf_check_l M hZF h.base ω
    have hcount := step_index_forces_countable_l O hZF h hT hP hC hd ht hg hi hω hw hwn hb
    let φ : UnarySchema 2 := { body := inj_body_m, freeClosed := inj_body_closed_l }
    obtain ⟨f, hf, _, hmax⟩ := maximum_l O hZFC φ (ord_env_l M t w) (Fin.cases ht (fun _ => hwn))
    have hinj : Inj_name_d M B R z b t w f := ⟨ht, hwn, hf, (hmax b h.base hb).mp hcount⟩
    apply ccc_name_cover_l O hZFC hω h.base hc hinj hw
    intro x hx
    obtain ⟨p, s, hxp, _, hp, _⟩ := (h.conditions x).mp (hd.1 x hx).1
    obtain ⟨a, hxa, han, _⟩ := zf_check_l M hZF h.base x
    exact ⟨p, a, hp, hxa, mem_force_entry_l O hZF hp.1 han hp.1
      ((hi.1 a p).mpr ⟨x, s, hx, hxp, hxa⟩) (O.refl p hp.1)⟩

end YesMetaZFC.Model.Forcing.Internal
