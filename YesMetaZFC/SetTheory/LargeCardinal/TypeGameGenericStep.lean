import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRoundSet
import YesMetaZFC.SetTheory.Descriptive.ScanStrategy

/-! # 扩张中的最小编号响应仍产生真实地状态

枚举满射与地模型重置走法保证最小合法编号存在。三次追加均为旧有限历史，
因而可回拉到原 I 策略的控制集合；原类型规则始终只在地模型中求值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hZFC : M.Models ZFC) (hN : N.Models ZF)
variable (e : M.Domain → N.Domain) (hi : Function.Injective e)
  (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

omit hi in
theorem Tg_aux_data_d.image_l {a ℓ t κ u : M.Domain} (data : Tg_aux_data_d a ℓ t κ u) :
    Tg_aux_data_d (e a) (e ℓ) (e t) (e κ) (e u) := by
  obtain ⟨b, ⟨d, pair₀, pair₁⟩, pair₂⟩ := data
  exact ⟨e b, ⟨e d, image_kpair_l e he pair₀, image_kpair_l e he pair₁⟩, image_kpair_l e he pair₂⟩

theorem Tg_ready_d.generic_step_l {p : Tg_params_d M.Domain} {X F L G O σ R n m h : M.Domain}
    {g K D T x q t : N.Domain}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (histories : Tg_histories_d hM p X F L) (owner : Tg_owner_d hM p.ω p.c p.a p.b O)
    (control : Cg_control_d I true p.ω p.e X F L G O σ R)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ready : Tg_ready_d hM p X n h)
    (hh : M.mem h R) (succ : M.SuccessorOf m n) (hx : N.mem x (e p.A))
    (pair : (J).Codes q (e h) x) (qt : Rd_entry_d q t T) :
    ∃ t₀ i a, e t₀ = t ∧ M.mem t₀ R ∧ Tg_ready_d hM p X m t₀ ∧ Tg_aux_d hM p n h a ∧ Tg_event_d I p.c n p.e t₀ a ∧
      Rd_entry_d (e h) i K ∧ Rd_entry_d i (e a) g ∧ Cg_scan_d hN (e p.ω) (e L) g (e h) i := by
  have hhF := ((control.legal h).mp ((control.positions h).mp hh).1).1
  have legalImage (a : M.Domain) := image_admit_l hM hN e hi he (a := a) setup.omega hw histories.1
    (fun s hs => ((histories.2 s).mp hs).1) hhF
  obtain ⟨a₀, ha₀, aux₀⟩ := setup.ready_move_l hZFC hd root ready
  have current := ready
  obtain ⟨_, l, z, hl, fh, div, _⟩ := current
  have admissible := histories.admit_l hM setup.omega hl ready.1 fh div ha₀ aux₀
  obtain ⟨j, hj, ja₀⟩ := surj (e a₀) ((image_member_l e hi he).mpr ha₀)
  obtain ⟨i, a, h₁, w, h₂, l₂, y, ki, ga, h₁F, e₁, sw, h₂F, e₂, fh₂, own, tF, e₃⟩ := c.step (e h) x q t pair qt
  have scan := c.least (e h) i ki ⟨j, e a₀, hj, ja₀, (legalImage a₀).mp admissible⟩
  obtain ⟨a', ga', legal⟩ := scan.2.1
  have eq := (fn0_function_l (ZF.modelsKP hN) c.enumeration).1.2 i a' a ga' ga; subst a'
  obtain ⟨a₁, ha₁, eq⟩ := (he X a).mp (c.enumeration.bound_l ga).2; subst a
  obtain ⟨s₁, hs₁, eq⟩ := (he F h₁).mp h₁F; subst h₁
  obtain ⟨s₂, hs₂, eq⟩ := (he F h₂).mp h₂F; subst h₂
  obtain ⟨s₃, hs₃, eq⟩ := (he F t).mp tF; subst t
  obtain ⟨w₀, hw₀, eq⟩ := (he X w).mp (c.strategy.bound_l sw).2; subst w
  obtain ⟨k₂, hk₂, fs₂⟩ := (histories.1 s₂).mp hs₂
  have fs₂' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fs₂
  have eq := fh₂.domain_eq_l hN.1 (fn0_of_function_l (ZF.modelsKP hN) fs₂'); subst l₂
  obtain ⟨k₃, hk₃, fs₃⟩ := (histories.1 s₃).mp hs₃
  have fs₃' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fs₃
  obtain ⟨d, b, dec⟩ := e₃
  have eq := dec.prefix_sequence.2.2.2.eq hN.1 fs₂'.2.1
  have last : Rd_entry_d (e k₂) y (e s₃) := eq ▸ dec.last_value
  obtain ⟨y₀, hy₀, eqy⟩ := (he X y).mp (fs₃'.output_mem_of_pairMember last); subst y
  have end₁ := (image_end_l hM hN e hi he setup.omega hw histories.1 hs₁ hhF).mpr e₁
  have end₂ := (image_end_l hM hN e hi he setup.omega hw histories.1 hs₂ hs₁).mpr e₂
  have end₃ := (image_end_l hM hN e hi he setup.omega hw histories.1 hs₃ hs₂).mpr ⟨d, b, dec⟩
  have value := (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 s₁ w₀ σ).mpr sw
  have digit : (M.mem k₂ O ∧ Rd_entry_d s₂ y₀ σ) ∨ (¬ M.mem k₂ O ∧ M.mem y₀ p.A) := by
    rcases own with ⟨turn, val⟩ | ⟨turn, val⟩
    · exact Or.inl ⟨(image_member_l e hi he).mp turn,
        (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 s₂ y₀ σ).mpr val⟩
    · exact Or.inr ⟨fun h => turn ((image_member_l e hi he).mpr h),
        (image_member_l e hi he).mp (val.symm ▸ hx)⟩
  obtain ⟨next, state, aux, event⟩ := ready.advance_l hZFC setup histories owner control hh succ hs₁ hs₂ hs₃
    end₁ end₂ end₃ ((legalImage a₁).mpr legal) value ⟨k₂, fn0_of_function_l (ZF.modelsKP hM) fs₂, digit⟩
  exact ⟨s₃, i, a₁, rfl, next, state, aux, event, ki, ga, scan⟩

end YesMetaZFC.SetTheory.LargeCardinal
