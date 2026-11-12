import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundScope
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RankStep
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawPowerStep

/-! # 计数回合读取原 Woodin 参数

不可达性从同一请求或档案回合的实际 Woodin 证书读取，不另增大基数前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem td_round_woodin_l (hKP : M.Models KP) (ρ : Env M 62)
    (round : Formula.satisfies ρ td_round0_m) : Woodin_d (kp_pair_l hKP) (ρ.bound 21) := by
  have seed := (Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp round).1
  simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff] at seed
  exact (woodin_sat_l (kp_pair_l hKP) hKP.1 ..).mp seed.2.2.1

theorem td_issued_woodin_l (hKP : M.Models KP) (ι : Env M 47)
    (issued : Formula.satisfies ι td_issued0_m) : Woodin_d (kp_pair_l hKP) (ι.bound 5) := by
  have control := (td_issued_sat_l (kp_pair_l hKP) hKP.1 ι).mp issued |>.control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at control
  have geometry := control.2.2.2.2.2.2.2.2.2
  simp only [td_geometry_m,Formula.satisfies_conj_iff] at geometry
  exact (woodin_sat_l (kp_pair_l hKP) hKP.1 ..).mp geometry.1

end YesMetaZFC.SetTheory.LargeCardinal
