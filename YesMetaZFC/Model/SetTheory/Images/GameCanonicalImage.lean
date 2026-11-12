import YesMetaZFC.SetTheory.Descriptive.Game.GameWitness
import YesMetaZFC.Model.SetTheory.ProjectBounded
import YesMetaZFC.Model.Forcing.Ground.TreeShift

/-! # 同实数的成员满模型之间的决定性绝对性

局面编号与回合奇偶性在源模型内实际构造。策略由实数编码后，
完整获胜条件和决定性成为 Δ₀；成员满性双向搬运全部策略实数。
不要求全初等性，也不把目标中的任意策略图假设为旧对象。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel Descriptive
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem det_image_l (hM : M.Models ZF) (hN : N.Models ZF)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
    {ω B T A : M.Domain} (space : Baire_d (kp_pair_l (ZF.modelsKP hM)) ω B)
    (finite : Fseq_space_d (kp_pair_l (ZF.modelsKP hM)) ω ω T)
    (target : Baire_d (kp_pair_l (ZF.modelsKP hN)) (e ω) (e B)) :
    Det_d (kp_pair_l (ZF.modelsKP hM)) ω B T A ↔
      Det_d (kp_pair_l (ZF.modelsKP hN)) (e ω) (e B) (e T) (e A) := by
  obtain ⟨E,V,number,_,parity⟩ := gs_setup_l (kp_pair_l (ZF.modelsKP hM)) hM space.1 finite
  have index := number.function
  let ρ : Env M 6 := ⟨fun i => [ω,B,T,E,V,A].get i,fun _ => ω⟩
  have base := (gs_base_iff_l hM space).mpr ⟨finite,index,parity⟩
  have moved := (delta0_image_l e inj full (gs_base_delta_l (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)) ρ).mp
    ((gs_base_sat_l hM.1 ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mpr base)
  obtain ⟨finite',index',parity'⟩ := (gs_base_iff_l hN target).mp
    ((gs_base_sat_l hN.1 (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mp moved)
  exact (gs_det_iff_l hM space finite index parity).trans
    ((gs_det_sat_l hM.1 ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5)).symm.trans
      ((delta0_image_l e inj full (gs_det_delta_l ..) ρ).trans
        ((gs_det_sat_l hN.1 (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5)).trans
          (gs_det_iff_l hN target finite' index' parity').symm)))

end YesMetaZFC.SetTheory

/-! ## 规范局面编号下的策略实数运输

源中的实际赢家先用规范编号编码为实数，再将有界获胜条件沿成员满嵌入
运输。有限局面空间及编号逐一相等；奇偶集合只需在同一 ω 上一致。
目标实数族取源实数集的完整像，不要求它包含背景的全部实数。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}}

theorem gs_det_parity_l {ω B T E V W A : M.Domain}
    (parity : ∀ n, M.mem n ω → (M.mem n V ↔ M.mem n W)) :
    Gs_det_d ω B T E V A ↔ Gs_det_d ω B T E W A := by
  have follows p r x : Gs_follows_d p ω T E V r x ↔ Gs_follows_d p ω T E W r x := by
    have turn n (hn : M.mem n ω) :
        (if p then M.mem n V else ¬ M.mem n V) ↔ (if p then M.mem n W else ¬ M.mem n W) := by
      cases p
      · exact not_congr (parity n hn)
      · exact parity n hn
    exact ⟨fun h n hn hp => h n hn ((turn n hn).mpr hp),
      fun h n hn hp => h n hn ((turn n hn).mp hp)⟩
  have win p r : Gs_win_d p ω B T E V A r ↔ Gs_win_d p ω B T E W A r :=
    ⟨fun h x hx follow => h x hx ((follows p r x).mpr follow),
      fun h x hx follow => h x hx ((follows p r x).mp follow)⟩
  exact or_congr (exists_congr fun r => and_congr_right fun _ => win true r)
    (exists_congr fun r => and_congr_right fun _ => win false r)

theorem det_canonical_image_l {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
    (e : M.Domain → N.Domain) (ei : Function.Injective e)
    (ef : ∀ a x, N.mem x (e a) ↔ ∃ b, M.mem b a ∧ e b = x)
    {ω B T A : M.Domain} (space : Baire_d (kp_pair_l (ZF.modelsKP hM)) ω B)
    (finite : Fseq_space_d (kp_pair_l (ZF.modelsKP hM)) ω ω T)
    (hw : N.IsOmega (e ω)) {T' E' V' : N.Domain}
    (finite' : Fseq_space_d (kp_pair_l (ZF.modelsKP hN)) (e ω) (e ω) T')
    (number' : Gs_number_d (kp_pair_l (ZF.modelsKP hN)) (e ω) T' E')
    (parity' : Gs_parity_d (e ω) V')
    (det : Det_d (kp_pair_l (ZF.modelsKP hM)) ω B T A) :
    Gs_det_d (e ω) (e B) T' E' V' (e A) := by
  obtain ⟨E,V,number,_,parity⟩ := gs_setup_l (kp_pair_l (ZF.modelsKP hM)) hM space.1 finite
  have actual := image_fseq_l hM hN e ei ef space.1 hw finite
  have eqT : e T = T' := hN.1.eq_of_same_members _ _ (fun s => (actual s).trans (finite' s).symm)
  have copied := number.image_l hM hN e ei ef space.1
  rw [eqT] at copied
  have eqE := copied.unique_l (kp_pair_l (ZF.modelsKP hN)) hN.1 number'
  let ρ : Env M 6 := ⟨fun i => [ω,B,T,E,V,A].get i,fun _ => ω⟩
  have base := (gs_base_iff_l hM space).mpr ⟨finite,number.function,parity⟩
  have rawBase := (gs_base_sat_l hN.1 (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mp
    ((delta0_image_l e ei ef (gs_base_delta_l (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)) ρ).mp
      ((gs_base_sat_l hM.1 ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mpr base))
  have raw := (gs_det_sat_l hN.1 (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5)).mp
    ((delta0_image_l e ei ef (gs_det_delta_l (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5)) ρ).mp
      ((gs_det_sat_l hM.1 ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5)).mpr
        ((gs_det_iff_l hM space finite number.function parity).mp det)))
  change Gs_det_d (e ω) (e B) (e T) (e E) (e V) (e A) at raw
  rw [eqT,eqE] at raw
  have even := (gs_parity_iff_l hN hw).mp rawBase.2.2
  have even' := (gs_parity_iff_l hN hw).mp parity'
  exact (gs_det_parity_l (fun n hn => (even n hn).trans (even' n hn).symm)).mp raw

end YesMetaZFC.SetTheory
