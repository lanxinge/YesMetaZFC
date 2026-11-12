import YesMetaZFC.Model.Forcing.Stage.AntichainChoice

/-! # 正锥内稠密集的实际极大反链

先在稠密集的局部正锥中作内部贪心选择，再把对该集合的极大性提升为
整个正锥中的预稠密性。该构造供坍缩树逐层细化直接调用。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC) {B R z : M.Domain}
local notation "hZF" => ZFC.models_zf_l hZFC
include hZFC

theorem antichain_dense_l (O : Cond_order_d M B R z) {p D : M.Domain} (hp : M.mem p B)
    (dense : Dense_d M B R z (fun q => M.mem q D) p) : ∃ A,
      Antichain_d M B R z A ∧ (∀ a, M.mem a A → M.mem a D ∧ Below_d M B R z a p) ∧
      ∀ q, Below_d M B R z q p → ∃ a, M.mem a A ∧ Cmp_d M B R z q a := by
  let ρ : Env M 4 := ⟨fun i => [B,R,z,p].get i,fun _ => p⟩
  let φ : UnarySchema 4 := { body := below_m (.bound 1) (.bound 2) (.bound 3) .newest (.bound 4) }
  obtain ⟨E,members⟩ := ZF.separation_exists_d hZF φ ρ D
  have member a : M.mem a E ↔ M.mem a D ∧ Below_d M B R z a p :=
    (members a).trans (and_congr_right fun _ => below_sat_l M hZFC.1 ..)
  obtain ⟨A,sub,antichain,maximal⟩ := antichain_subset_l hZFC O E
  refine ⟨A,antichain,fun a ha => (member a).mp (sub a ha),fun q hq => ?_⟩
  obtain ⟨r,hr,rd⟩ := dense q hq
  obtain ⟨a,ha,s,hs,sa⟩ := maximal r ((member r).mpr ⟨rd,below_trans_l O hp hr hq⟩) hr.1 hr.2.1
  exact ⟨a,ha,s,below_trans_l O hq.1 hs hr,sa⟩

end YesMetaZFC.Model.Forcing.Internal
