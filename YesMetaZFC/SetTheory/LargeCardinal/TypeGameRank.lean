import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlMove
import YesMetaZFC.Model.SetTheory.Internal.TransitiveCardinal

/-! # 合法尝试树的秩在传递反射层中绝对读取

原控制记录已经包含实际秩函数的存在性。取出层内见证后，只读取其 Δ₀
图证书，故得到背景中的真秩下降关系，不对反射层附加 ZF 或 DC。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) (hKP : M.Models KP)
variable {C : M.Domain} (trans : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
  (ρ : Env (rt_model_l C nc) 19)
include trans

include hKP in
theorem tg_control_rank_l (valid : Formula.satisfies ρ tg_control0_m) :
    ∃ α F, M.mem α C ∧ M.mem F C ∧ Cg_rank_d (ρ.bound 0).val (ρ.bound 12).val (ρ.bound 18).val α F := by
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at valid
  have rank := valid.2.2.2.2.2.2.2.2.1
  simp only [cg_rank_m, Formula.satisfies_exists_iff] at rank
  obtain ⟨α, F, rank⟩ := rank
  have lifted := (rt_model_delta_l trans nc (cg_rank0_delta_l ..) ((ρ.push α).push F)).mp rank
  exact ⟨α.val, F.val, α.property, F.property, (cg_rank0_sat_l hKP ..).mp lifted⟩

include hZF in
/-- 传递目标中的原控制树不能含背景内部的无限合法延长链。 -/
theorem tg_control_no_chain_l {ω H : M.Domain} (hω : M.IsOmega ω)
    (hw : (ρ.bound 0).val = ω) (valid : Formula.satisfies ρ tg_control0_m)
    (fn : Fn0_d ω (ρ.bound 18).val H) :
    ¬ (∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s H → Rd_entry_d j t H →
      Tb_step_d ω (ρ.bound 12).val s t) := by
  obtain ⟨_, _, _, _, rank⟩ := tg_control_rank_l (ZF.modelsKP hZF) trans nc ρ valid
  exact (hw ▸ rank).no_chain_l hZF hω fn

end YesMetaZFC.SetTheory.LargeCardinal
