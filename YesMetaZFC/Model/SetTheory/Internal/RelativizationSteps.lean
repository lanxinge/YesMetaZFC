import YesMetaZFC.Model.SetTheory.Internal.RelativizationSyntax
import YesMetaZFC.Model.SetTheory.Internal.InstructionAppend

/-! # 限制编译的实际语法构造

每一步只追加合法指令。存在量词的五行代码完整保留在输出证书中，
正确性另对该纯语法证书证明，编译器不把真值保持作为定义条件。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

private theorem sr_add_l (hZF : M.Models ZF) {ω m G c i j} {k : Nat} (hω : M.IsOmega ω)
    (hG : Sfm_d I ω m G) (hc : Sfm_node_d I ω m c) (hs : Sop_d I k c i j) :
    ∃ l H, Sbuild_d I ω m G l H m ∧ Sr_at_d I k H m i j := by
  obtain ⟨l, H, h, row⟩ := sfm_node_build_l I hZF hω hG hc
  exact ⟨l, H, h, c, row, hs⟩

private theorem sr_ex_syntax_l (hZF : M.Models ZF) {ω b T m G c i j v}
    (hω : M.IsOmega ω) (hG : Sfm_d I ω m G) (hc : Sop_d I 3 c i j)
    (hv : M.mem v m) (hjv : M.PairMember I j v T) (hi : M.mem i ω) (hb : M.mem b ω) :
    ∃ l H k, Sbuild_d I ω m G l H k ∧ Sr_rule_d I b T H c k := by
  obtain ⟨m₁, G₁, h₁, a₁⟩ := sr_rel_add_l I hZF hω hG hi hb
  obtain ⟨m₂, G₂, t, h₂, a₂⟩ := sr_and_build_l I hZF hω h₁.program h₁.root (h₁.span v hv)
  obtain ⟨l, H, h₃, a₃⟩ := sr_ex_add_l I hZF hω h₂.program hi h₂.root
  obtain ⟨p, q, hp, hq, ht⟩ := a₂
  exact ⟨l, H, m₂, (h₁.comp I h₂).comp I h₃,
    Or.inr (Or.inr (Or.inr ⟨i, j, v, m, p, q, t, hc, hjv,
      a₁.extend_l I (h₂.comp I h₃), hp.extend_l I h₃, hq.extend_l I h₃, ht.extend_l I h₃, a₃⟩))⟩

/-- 每个旧指令都有实际新代码，返回的纯语法规则可独立核验。 -/
theorem sr_step_l (hZF : M.Models ZF) {ω b F n r c T m G : M.Domain}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (hb : M.mem b ω) (hc : M.PairMember I r c F)
    (map : M.IsSetFunctionFromTo I T r m) (hG : Sfm_d I ω m G) :
    ∃ l H u, Sbuild_d I ω m G l H u ∧ Sr_rule_d I b T H c u := by
  rcases hF.2.2 r c hc with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ |
    ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
  · obtain ⟨l, H, h, row⟩ := sr_add_l I hZF hω hG (Or.inl ⟨i, j, hs, hi, hj⟩) hs
    exact ⟨l, H, m, h, Or.inl ⟨i, j, hs, row⟩⟩
  · obtain ⟨l, H, h, row⟩ := sr_add_l I hZF hω hG (Or.inr (Or.inl ⟨i, j, hs, hi, hj⟩)) hs
    exact ⟨l, H, m, h, Or.inr (Or.inl ⟨i, j, hs, row⟩)⟩
  · obtain ⟨u, hu, hiu⟩ := map.2.2 i hi
    obtain ⟨v, hv, hjv⟩ := map.2.2 j hj
    obtain ⟨l, H, h, row⟩ := sr_nor_add_l I hZF hω hG hu hv
    exact ⟨l, H, m, h, Or.inr (Or.inr (Or.inl ⟨i, j, u, v, hs, hiu, hjv, row⟩))⟩
  · obtain ⟨v, hv, hjv⟩ := map.2.2 j hj
    exact sr_ex_syntax_l I hZF hω hG hs hv hjv hi hb

end YesMetaZFC.SetTheory.Internal
