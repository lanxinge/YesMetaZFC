import YesMetaZFC.Model.Forcing.Proper.Family.Indexed

/-! # 一个内部小模型在全部成员阶段的泛型提升

从两张共同图切出当前阶段的运算。阶段编号已在 N 中，故切片的闭性自动从
共同图继承；随后直接应用覆盖全部内部公式码的泛型初等性定理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R b : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R B) (hZF : M.Models ZF) (hU : Generic_d M B R B U)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R B U
local notation "J" => kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)

theorem ng_indexed_lift_l {ω δ F G X u w C T S D K L N i q}
    (hb : U b) (hω : M.IsOmega ω) (hu : Name_d M B u) (huN : M.mem u N) (hw : Check_d M b ω w)
    (hC : Scode_d I ω C) (hT : M.IsCartesianProduct I T C ω)
    (hS : Fseq_space_d I ω X S) (hD : M.IsCartesianProduct I D T S)
    (hK : M.IsSetFunctionFromTo I K D X) (hL : M.IsSetFunctionFromTo I L D X)
    (hF : M.IsSetFunction I F) (hG : M.IsSetFunction I G)
    (hk : ∀ p t, Entry_d M p t K → Ng_joint_d I false ω δ F G b X w u p t)
    (hl : ∀ p t, Entry_d M p t L → Ng_joint_d I true ω δ F G b X w u p t)
    (hNX : M.MemberSubset N X) (hKN : Fc_closed_d I ω T K N) (hLN : Fc_closed_d I ω T L N)
    (hi : M.mem i δ) (hiN : M.mem i N) (hB : Entry_d M i B F) (hR : Entry_d M i R G)
    (hm : Mstr_d M B R B N q) (hq : U q) :
    ∃ Y Z v c A d H : (E).Domain,
      (∀ x, x ∈ Y ↔ Ng_mem_d M B R B U X x) ∧ (∀ x, x ∈ Z ↔ Ng_mem_d M B R B U N x) ∧
      (E).IsOmega v ∧ Smem_d J c Y A ∧ Ssub_d J c d Y A Z H ∧ Selem_d J v c d := by
  obtain ⟨μ, hμ⟩ := ng_name_exists_l M hZF B X
  obtain ⟨K', hK', hk', hcK⟩ := ng_joint_slice_l hZF hω hS hD hK hF hG hk hi (hNX i hiN) hB hR hμ
  obtain ⟨L', hL', hl', hcL⟩ := ng_joint_slice_l hZF hω hS hD hL hF hG hl hi (hNX i hiN) hB hR hμ
  exact ng_elementary_l O hZF hU hb hω hu huN hw hμ hC hT hS hD hK' hL' hk' hl'
    hNX (hcK N hiN hKN) (hcL N hiN hLN) hm hq

end YesMetaZFC.Model.Forcing.Internal
