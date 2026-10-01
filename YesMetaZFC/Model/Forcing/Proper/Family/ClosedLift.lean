import YesMetaZFC.Model.Forcing.Proper.Family.ClosedSyntax
import YesMetaZFC.Model.Forcing.Proper.Family.IndexedLift
import YesMetaZFC.Model.Forcing.Proper.Hereditary.Correspondence

/-! # 对指定闭集 N 的 H(χ) 泛型提升

输入两张实际运算图的闭包证书。提升对这个确定的 N 逐点成立，因而可在整个
交集 club 上复用；不在每个泛型中重新选择地模型小模型。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R b : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R B) (hZFC : M.Models ZFC) (hU : Generic_d M B R B U)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R B U
local notation "J" => kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)

theorem ng_closed_lift_l {ω χ H δ F G N w i q} (hb : U b) (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H) (hBH : M.mem B H)
    (hNX : M.MemberSubset N H) (hn : M.CardinalLessOrEqual I N ω) (hw : Check_d M b ω w)
    (hF : M.IsSetFunction I F) (hG : M.IsSetFunction I G) (hc : Ng_closed_d I ω δ F G b H N w)
    (hi : M.mem i δ) (hiN : M.mem i N) (hiB : Entry_d M i B F) (hiR : Entry_d M i R G)
    (hm : Mstr_d M B R B N q) (hq : U q) :
    ∃ (e : M.Domain → (E).Domain) (Y Z v c T d S : (E).Domain),
      (∀ a t, Check_d M b a t → Qval_d M B R B U t (e a)) ∧
      (∀ a y, y ∈ e a ↔ ∃ s, M.mem s a ∧ e s = y) ∧ Function.Injective e ∧
      (E).IsRegularCardinal J (e χ) ∧ H_d J (e χ) Y ∧
      (∀ x, x ∈ Y ↔ Ng_mem_d M B R B U H x) ∧ (∀ x, x ∈ Z ↔ Ng_mem_d M B R B U N x) ∧
      (E).IsOmega v ∧ (E).TransitiveSet Y ∧ (E).CardinalLessOrEqual J Z v ∧
      Smem_d J c Y T ∧ Ssub_d J c d Y T Z S ∧ Selem_d J v c d := by
  obtain ⟨u, C, S, T, D, P, Q, ⟨hu, hC, hS, hT, hD, hP, hQ, hp, hq'⟩, huN, hNP, hNQ⟩ := hc
  have hun := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B u hu
  obtain ⟨Y, Z, v, c, T', d, S', hY, hZ, hv, hM', hS', hEl'⟩ :=
    ng_indexed_lift_l O hZF hU hb hω hun huN hw hC hT hS hD hP hQ hF hG hp hq'
      hNX hNP hNQ hi hiN hiB hiR hm hq
  obtain ⟨e, hval, hmem, hinj⟩ := check_map_l O hZF hU hb
  obtain ⟨hreg, hH'⟩ := h_generic_l O hZFC hU hω hχ hωχ hH hBH hb e hinj hmem hval hY
  obtain ⟨Z', v', hZ', hv', hz'⟩ := ng_countable_l O hZF hU hω hn
  have heZ : Z' = Z := (extension_ext_l O hZF hU).eq_of_same_members _ _
    (fun x => (hZ' x).trans (hZ x).symm)
  have hev : v' = v := (extension_ext_l O hZF hU).eq_of_same_members _ _
    (fun x => ⟨hv'.2 v hv.1 x, hv.2 v' hv'.1 x⟩)
  subst Z' v'
  exact ⟨e, Y, Z, v, c, T', d, S', hval, hmem, hinj, hreg, hH', hY, hZ, hv,
    ng_transitive_l O hZF hU (ZF.h_transitive_l I hZF hH) hY, hz', hM', hS', hEl'⟩

end YesMetaZFC.Model.Forcing.Internal
