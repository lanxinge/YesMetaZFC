import YesMetaZFC.Model.Forcing.Internal.Ground.FiniteSequence
import YesMetaZFC.Model.SetTheory.ProjectBounded
import YesMetaZFC.SetTheory.Descriptive.LegalMoveBounded

/-! # 地模型有限合法走法的双向保持 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
local notation "J" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hN))
include hi he

theorem image_end_l {ω X F t h a : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (space : Fseq_space_d I ω X F) (ht : M.mem t F) (hh : M.mem h F) :
    Fseq_end_d I ω t h a ↔ Fseq_end_d J (e ω) (e t) (e h) (e a) := by
  let ρ : Env M 5 := ⟨fun i => [ω, X, t, h, a].get i, fun _ => ω⟩
  exact (ds_end_bound_sat_l hM ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) hw space ht hh).symm.trans
    ((delta0_image_l e hi he (ds_end_bound_delta_l (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)) ρ).trans
      (ds_end_bound_sat_l hN (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
        hw' (image_fseq_l hM hN e hi he hw hw' space) ((image_member_l e hi he).mpr ht) ((image_member_l e hi he).mpr hh)))

theorem image_admit_l {ω X F L h a : M.Domain} (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (space : Fseq_space_d I ω X F) (legal : M.MemberSubset L F) (hh : M.mem h F) :
    Cg_admit_d hM ω L h a ↔ Cg_admit_d hN (e ω) (e L) (e h) (e a) := by
  let ρ : Env M 5 := ⟨fun i => [ω, X, L, h, a].get i, fun _ => ω⟩
  have space' := image_fseq_l hM hN e hi he hw hw' space
  have legal' : N.MemberSubset (e L) (e F) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (he L y).mp hy
    exact (image_member_l e hi he).mpr (legal x hx)
  exact (cg_admit_bound_sat_l hM ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) hw space legal hh).symm.trans
    ((delta0_image_l e hi he (cg_admit_bound_delta_l (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)) ρ).trans
      (cg_admit_bound_sat_l hN (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
        hw' space' legal' ((image_member_l e hi he).mpr hh)))

end YesMetaZFC.Model.Forcing.Internal
