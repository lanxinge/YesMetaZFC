import YesMetaZFC.Model.SetTheory.Internal.SubtypeWitness

/-! # 定义 3.9 的超过关系

原类型与候选类型使用同一指定常量。低层保留完整元组与实际排列，
秩间隔使用原 ν+1<η；并给出同一元组、恒等排列的实际构造入口。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tx_exceeds_d (hZF : M.Models ZF) (ω δ κ n U D u τ m V W w : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  M.mem κ τ ∧ M.MemberSubset n m ∧ ∃ η Y c R s, V_d I η Y ∧ Smem_d I c Y R ∧
    Tt_realized_d I ω c Y R n s δ U D u ∧ ∃ ν μ, M.SuccessorOf μ ν ∧ M.mem μ η ∧
      Ts_at_d hZF ω δ n s m V W w ν

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tx_exceeds_same_l {ω δ κ n U D u τ V W w η Y c R ν A d S μ s : M.Domain}
    (hω : M.IsOmega ω) (hκτ : M.mem κ τ) (hY : V_d I η Y) (upper : Smem_d I c Y R)
    (hu : Tt_realized_d I ω c Y R n s δ U D u) (hA : V_d I ν A) (lower : Smem_d I d A S)
    (hw : Tt_realized_d I ω d A S n s δ V W w) (hs : M.SuccessorOf μ ν) (hμη : M.mem μ η) :
    Tx_exceeds_d hZF ω δ κ n U D u τ n V W w :=
  ⟨hκτ, fun _ h => h, η, Y, c, R, s, hY, upper, hu, ν, μ, hs, hμη, ts_at_self_l hZF hω hA lower hw⟩

end YesMetaZFC.SetTheory.Internal
