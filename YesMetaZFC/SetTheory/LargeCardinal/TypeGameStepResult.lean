import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRound
import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePastStep
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnchor
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameIssued
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameOdd

/-! # 两种实际树后继共用的完整回答证书

第一边产生回答所在的奇数模型，第二边从原偶数模型出发。保留原请求的
字面对应、两个根图、共同层、奇数边的图恢复以及同一次历史追加。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_tree_step_d (ω X η c₀ α ξ T J G E c o Cᵣ γ Z H : M.Domain)
    {C : M.Domain} (nc : Nonempty {x // M.mem x C}) (ι : Env (rt_model_l C nc) 46) : Prop :=
  ∃ k β T₁ J₁ G₁ E₁ H₁ a Y R μ K η₁ C₁ π₁,
    It_pnice_d hZF ω c₀ β T₁ J₁ G₁ E₁ H₁ ∧ It_extension_d α ξ k T J G E β T₁ J₁ G₁ E₁ ∧
    Rd_entry_d α a J₁ ∧ Smem_d I a Y R ∧ Ic_model_d hZF ω μ K Y R ∧ Tg_context_d ω Y η₁ C₁ ∧
    It_map_d G₁ o α π₁ ∧ Rd_entry_d Cᵣ C₁ π₁ ∧ Tg_anchor_d γ Z Y π₁ ∧
    ∃ n₁ : Nonempty {x // M.mem x C₁}, ∃ ρ : Env (rt_model_l C₁ n₁) 54,
      let q := fun i => (ρ.bound i).val
      let σ := Fin.cases (q 47) (Fin.cases (q 48) (Fin.cases (q 49)
        (Fin.cases (q 50) (Fin.cases (q 51) (Fin.cases (q 52) (fun _ => q 53))))))
      Formula.satisfies ρ tg_round0_m ∧ Tg_request_d (fun i => (ι.bound i).val) q ∧ M.MemberSubset γ (q 15) ∧
      Tg_odd_d ω H ξ α k G₁ (ι.bound 1).val (ι.bound 23).val (ι.bound 22).val (q 19) (q 22) (q 42) ∧
      ∃ β₂ T₂ J₂ G₂ E₂ H₂ d j N R₂ K₂ L F κ U D u η₂ C₂ W π₂,
        It_pnice_d hZF ω c₀ β₂ T₂ J₂ G₂ E₂ H₂ ∧ It_extension_d β α ξ T₁ J₁ G₁ E₁ β₂ T₂ J₂ G₂ E₂ ∧
        Rd_entry_d β d J₂ ∧ It_map_d G₂ ξ β j ∧ Smem_d I d N R₂ ∧ Ic_model_d hZF ω L K₂ N R₂ ∧
        It_ultra_d hZF ω (ι.bound 24).val L F c d j ∧ Wd_crit_d I X j (ι.bound 24).val κ ∧
        M.IsLimitOrdinal L ∧ M.mem (q 15) L ∧ M.MemberSubset L κ ∧
        (∀ i ν, Rd_entry_d i ν H₂ → M.mem ν κ ∨ ν = κ) ∧
        Rd_entry_d (ι.bound 30).val U j ∧ Rd_entry_d (ι.bound 31).val D j ∧ Rd_entry_d (ι.bound 25).val u j ∧
        Tg_reply_d I ω (q 23) (q 24) κ (q 15) U D (q 12) u (q 11) (q 36) σ (q 38) ⟨q 2, q 1, q 0⟩ ∧
        Rd_entry_d η η₂ j ∧ Rd_entry_d C C₂ j ∧ Tg_context_d ω N η₂ C₂ ∧
        M.mem W Y ∧ Vr_d Y L W ∧ Er_level_d N L W ∧
        It_map_d G₂ o β π₂ ∧ Rd_entry_d Cᵣ C₂ π₂ ∧ Tg_anchor_d γ Z N π₂ ∧
        Tg_past_update_d hZF ω X (ι.bound 24).val α Y R μ K η₁ C₁ L W N κ j J J₂ q

end YesMetaZFC.SetTheory.LargeCardinal
