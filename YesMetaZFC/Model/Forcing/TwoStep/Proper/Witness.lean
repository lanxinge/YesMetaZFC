import YesMetaZFC.Model.Forcing.TwoStep.Proper.Image
import YesMetaZFC.Model.Forcing.Proper.Master.Name

/-! # 二步主条件的稠密见证提升

首阶段主条件把第二阶段稠密像中的 N[G] 见证取回 D∩N；第二阶段主条件提供
共同加强，再由实际二步共同加强定理回到地模型条件。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u

variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
include O

/-- 每个接受下方首坐标的泛型，给出地模型中真实的 D∩N 相容见证。 -/
theorem two_step_master_hit_l {ω χ H c J d N K q t μ v r p s D} {U}
    (hU : Generic_d M B R z U) (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ)
    (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hJ : ∀ x y, M.PairMember I x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H J N K) (hElem : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hz : M.mem z N)
    (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C) (hT : Name_d M B T)
    (hv : M.mem v C) (hvq : KPair_d M v q t) (hr : Below_d M C S C r v) (hrp : KPair_d M r p s)
    (hm : Mstr_d M B R z N q) (hμ : Ng_name_d M B N μ)
    (hForce : Forces_d M B R z mstr_body_m (mstr_env_l A T μ t) q) (hpU : U p)
    (hDN : M.mem D N) (hD : Dense_set_d M C S C D) :
    ∃ x, M.mem x D ∧ M.mem x N ∧ Cmp_d M C S C r x := by
  let E := extension_l M hZF B R z U
  have haN : Name_d M B A := ⟨W, h.root, h.closed⟩
  have hvt := (two_step_mem_l h hvq).mp hv
  have hrs := (two_step_mem_l h hrp).mp hr.1
  have htN : Name_d M B t := ⟨W, hvt.1, h.closed⟩
  have hsN : Name_d M B s := ⟨W, hrs.1, h.closed⟩
  have hle := (two_step_le_l h hr.1 hv hrp hvq).mp hr.2.2
  have hqU := hU.upward p q hpU hm.1 hle.1.2.2
  have hbU := hU.upward q b hqU h.base hvt.2.1.2.2
  obtain ⟨Q, hQ⟩ := name_value_l (R := R) (z := z) (U := U) haN
  obtain ⟨V, hV⟩ := name_value_l (R := R) (z := z) (U := U) hT
  obtain ⟨Z, hZ⟩ := name_value_l (R := R) (z := z) (U := U) hμ.1
  obtain ⟨a, ha⟩ := name_value_l (R := R) (z := z) (U := U) htN
  obtain ⟨a', ha'⟩ := name_value_l (R := R) (z := z) (U := U) hsN
  have hval : Env_val_d hZF (mstr_env_l A T μ t) (mstr_env_l Q V Z a) := by
    intro u
    cases u with
    | free _ => exact hQ
    | bound i => exact Fin.cases ha (Fin.cases hZ (Fin.cases hV (fun _ => hQ))) i
  have haMaster : Mstr_d E Q V Q Z a := (mstr_sat_l E (extension_ext_l O hZF hU) _ _ _ _ _ _).mp
    ((forcing_truth_l O hZF hU mstr_body_m mstr_body_closed_l _ _ hval).mp ⟨q, hqU, hForce⟩)
  obtain ⟨F, hFN, hF⟩ := selem_inverse_l hZFC hω hχ hωχ hH hJ hSub hElem hDN
  have hDC : M.MemberSubset D C := fun x hx => (hD.1 x hx).1
  have hFn := two_step_inverse_name_l hZF h hDC hF
  obtain ⟨Y, hY⟩ := name_value_l (R := R) (z := z) (U := U) hFn
  have hImage := two_step_inverse_value_l O hZF hU hDC hF hY
  have hYdense := two_step_image_dense_set_l O hZF hU h L hbU hQ hV hD hImage
  have hYinZ := (ng_value_l O hZF hU hμ hZ Y).mpr ⟨F, hFN, hY⟩
  have ha'Q := (qval_mem_forcing_l O hZF hU ha' hQ).mp ⟨p, hpU, hrs.2.2⟩
  have ha'ne : a' ≠ Q := fun he => KP.mem_irrefl_d (ZF.modelsKP (preserves_zf_l O hZF hU)) Q (he ▸ ha'Q)
  have ha'a := (rel_force_truth_l O hZF hU ha' ha hV).mp ⟨p, hpU, hle.2⟩
  obtain ⟨y, hyY, hyZ, u, hua', huy⟩ := haMaster.2.2 Y hYinZ hYdense a' ⟨ha'Q, ha'ne, ha'a⟩
  obtain ⟨x, k, l, hxN, hxD, hkU, hxk, hl⟩ := two_step_image_pick_l hZFC O hU hω hχ hωχ hH hJ hSub hElem
    hB hR hz hF hFN hm hqU (ng_value_l O hZF hU hμ hZ) hY hyZ hyY
  obtain ⟨j, _, _, _, _, _, hjr, hjx⟩ := two_step_common_l O hZF hU h L hQ hV hr.1 (hDC x hxD)
    hrp hxk hpU hkU ha' hl hua'.1 hua'.2.2 huy
  exact ⟨x, hxD, hxN, j, hjr, hjx.2.2⟩

end YesMetaZFC.Model.Forcing.Internal
