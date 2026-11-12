import YesMetaZFC.SetTheory.LargeCardinal.Game.GenericPreparation
import YesMetaZFC.SetTheory.Descriptive.Game.GameAttemptRank
import YesMetaZFC.SetTheory.Descriptive.Tree.ScanStrategy
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope

/-! # 原 I 策略下三步响应保持可继续状态

最小请求合法后，I 的两种应答由原获胜策略的控制集合保证合法；奇数轮读取
对手的原字母。三个实际追加图同时给出下一轮时钟和实数前缀，未引入续步谕示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}
variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hZ)

theorem Tg_ready_d.advance_l {p : Tg_params_d M.Domain} {X F L G J σ R n m h h₁ h₂ t a w y : M.Domain}
    (setup : Tg_setup_d hZFC p X) (histories : Tg_histories_d hZ p X F L)
    (owner : Tg_owner_d hZ p.ω p.c p.a p.b J) (control : Cg_control_d K true p.ω p.e X F L G J σ R)
    (ready : Tg_ready_d hZ p X n h) (hh : M.mem h R) (succ : M.SuccessorOf m n)
    (h₁F : M.mem h₁ F) (h₂F : M.mem h₂ F) (tF : M.mem t F)
    (e₁ : Fseq_end_d K p.ω h₁ h a) (e₂ : Fseq_end_d K p.ω h₂ h₁ w) (e₃ : Fseq_end_d K p.ω t h₂ y)
    (legal : Cg_admit_d hZ p.ω L h a) (value : Rd_entry_d h₁ w σ)
    (digit : ∃ j, Fn0_d j X h₂ ∧ ((M.mem j J ∧ Rd_entry_d h₂ y σ) ∨ (¬ M.mem j J ∧ M.mem y p.A))) :
    M.mem t R ∧ Tg_ready_d hZ p X m t ∧ Tg_aux_d hZ p n h a ∧ Tg_event_d K p.c n p.e t a ∧
      M.mem y p.A ∧ ∃ j, Fn0_d j X h₂ ∧ M.IsOrdinalDivision K j p.c n p.b ∧
        Tg_answer_d hZ p n h₁ w ∧ Tg_event_d K p.c n p.e h₁ a ∧ Tg_event_d K p.c n p.a t w := by
  obtain ⟨hn, i, z, hi, fh, div, digits, _⟩ := ready
  obtain ⟨j₁, hj₁, fh₁⟩ := (histories.1 h₁).mp h₁F
  obtain ⟨j₂, hj₂, fh₂⟩ := (histories.1 h₂).mp h₂F
  obtain ⟨j₃, hj₃, ft⟩ := (histories.1 t).mp tF
  have ends {s t x i j : M.Domain} (fs : Fn0_d i X s) (ft : M.IsSetFunctionFromTo K t j X)
      (en : Fseq_end_d K p.ω t s x) : M.SuccessorOf j i ∧ Rd_entry_d i x t := by
    obtain ⟨a, b, d⟩ := en
    have ei := d.prefix_sequence.2.2.2.eq hZ.1 (fn0_function_l (ZF.modelsKP hZ) fs).2.1
    have ej := d.source.2.2.2.eq hZ.1 ft.2.1
    exact ⟨ej ▸ ei ▸ d.length_successor, ei ▸ d.last_value⟩
  obtain ⟨s₁, v₁⟩ := ends fh fh₁ e₁
  obtain ⟨s₂, v₂⟩ := ends (fn0_of_function_l (ZF.modelsKP hZ) fh₁) fh₂ e₂
  obtain ⟨s₃, v₃⟩ := ends (fn0_of_function_l (ZF.modelsKP hZ) fh₂) ft e₃
  obtain ⟨hc, _⟩ := tg_clock_l hZ setup.omega setup.empty setup.one setup.two setup.three hi
  have oc := setup.omega.members_areOrdinals (ZF.modelsKP hZ) p.c hc
  have ab := oc.transitive p.b setup.three.predecessor_mem p.a setup.two.predecessor_mem
  have div₁ := tg_division_next_l hZ oc div setup.one s₁ ab
  have div₂ := tg_division_next_l hZ oc div₁ setup.two s₂ setup.three.predecessor_mem
  have ne₀ : p.e ≠ p.a := fun eq => setup.empty p.e (eq.symm ▸ setup.one.predecessor_mem)
  have ne₁ : p.e ≠ p.b := fun eq => setup.empty p.a (eq.symm ▸ setup.two.predecessor_mem)
  have turn₀ : ¬ M.mem i J := fun own => ((owner.read_l hZ (setup.omega.isOrdinal (ZF.modelsKP hZ)) oc
    ⟨p.b, setup.three.predecessor_mem⟩ hi hn div).mp own).elim ne₀ (fun h => ne₁ h.1)
  obtain ⟨h₁', check, endt⟩ := legal
  have eq := fseq_end_rebuild_l K hZ.1 endt e₁; subst h₁'
  have h₁R := control.step i h a h₁ hi hh (fh₁.output_mem_of_pairMember v₁) fh e₁ (Or.inl ⟨turn₀, check⟩)
  have turn₁ := (owner.read_l hZ (setup.omega.isOrdinal (ZF.modelsKP hZ)) oc ⟨p.b, setup.three.predecessor_mem⟩ hj₁ hn div₁).mpr (Or.inl rfl)
  have h₂R := control.step j₁ h₁ w h₂ hj₁ h₁R (fh₂.output_mem_of_pairMember v₂)
    (fn0_of_function_l (ZF.modelsKP hZ) fh₁) e₂ (Or.inr ⟨turn₁, value⟩)
  have replyStep := (tg_step_read_l hZ (setup.omega.members_areOrdinals (ZF.modelsKP hZ) j₁ hj₁) oc
    ⟨p.b, setup.three.predecessor_mem⟩ hn div₁).mp
    (((histories.2 h₂).mp (control.legal.current_l ((control.positions h₂).mp h₂R).1)).2.end_l hZ
      (fn0_of_function_l (ZF.modelsKP hZ) fh₁) e₂)
  have answer : Tg_answer_d hZ p n h₁ w := replyStep.elim (fun h => (ne₀ h.1.symm).elim)
    (fun h => h.elim And.right (fun h => (KP.mem_irrefl_d (ZF.modelsKP hZ) p.a (h.1.symm ▸ setup.two.predecessor_mem)).elim))
  obtain ⟨j, fj, digit⟩ := digit
  have eq := fj.domain_eq_l hZ.1 (fn0_of_function_l (ZF.modelsKP hZ) fh₂); subst j
  have tR : M.mem t R := by
    rcases digit with ⟨own, value⟩ | ⟨own, hy⟩
    · exact control.step j₂ h₂ y t hj₂ h₂R (ft.output_mem_of_pairMember v₃)
        (fn0_of_function_l (ZF.modelsKP hZ) fh₂) e₃ (Or.inr ⟨own, value⟩)
    ·
      have chk := tg_check_end_l hZ hj₃ s₃ (fn0_of_function_l (ZF.modelsKP hZ) ft)
        (fn0_of_function_l (ZF.modelsKP hZ) fh₂) e₃ ⟨n, p.b, hn, div₂, Or.inr (Or.inr ⟨rfl, hy⟩)⟩
      exact control.step j₂ h₂ y t hj₂ h₂R (ft.output_mem_of_pairMember v₃)
        (fn0_of_function_l (ZF.modelsKP hZ) fh₂) e₃ (Or.inl ⟨own, (histories.2 t).mpr ⟨tF, chk⟩⟩)
  have step := (tg_step_read_l hZ (setup.omega.members_areOrdinals (ZF.modelsKP hZ) j₂ hj₂) oc
    ⟨p.b, setup.three.predecessor_mem⟩ hn div₂).mp
    (((histories.2 t).mp (control.legal.current_l ((control.positions t).mp tR).1)).2.end_l hZ
      (fn0_of_function_l (ZF.modelsKP hZ) fh₂) e₃)
  have be : p.b ≠ p.e := Ne.symm ne₁
  have ba : p.b ≠ p.a := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZ) p.a (eq ▸ setup.two.predecessor_mem)
  have hy := step.elim (fun h => (be h.1).elim) (fun h => h.elim (fun h => (ba h.1).elim) And.right)
  have sub : M.MemberSubset h t := fun x hx => e₃.subset_l K x (e₂.subset_l K x (e₁.subset_l K x hx))
  obtain ⟨z', _, digits'⟩ := digits.append_l hZ setup.omega oc hn succ sub ft.1 hy ⟨j₂, div₂, v₃⟩
  have auxStep := (tg_step_read_l hZ (setup.omega.members_areOrdinals (ZF.modelsKP hZ) i hi) oc
    ⟨p.b, setup.three.predecessor_mem⟩ hn div).mp (((histories.2 h₁).mp check).2.end_l hZ fh e₁)
  have aux := auxStep.elim And.right (fun h => h.elim (fun h => (ne₀ h.1).elim) (fun h => (ne₁ h.1).elim))
  have saved := aux
  obtain ⟨ℓ, q, κ, u, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, data, hκ, _⟩ := saved
  obtain ⟨m', sm', hm'⟩ := setup.omega.1.2 n hn
  have eq := sm'.eq hZ.1 succ
  exact ⟨tR, ⟨eq ▸ hm', j₃, z', hj₃, fn0_of_function_l (ZF.modelsKP hZ) ft,
    tg_division_cycle_l hZ oc div₂ setup.three succ s₃ setup.empty, digits',
    Or.inr ⟨n, a, ℓ, q, κ, u, succ, (Tg_event_d.end_l (Tg_event_d.end_l ⟨i, div, v₁⟩ e₂) e₃), data, hκ⟩⟩,
    aux, (Tg_event_d.end_l (Tg_event_d.end_l ⟨i, div, v₁⟩ e₂) e₃), hy, j₂,
    fn0_of_function_l (ZF.modelsKP hZ) fh₂, div₂, answer, ⟨i, div, v₁⟩, Tg_event_d.end_l ⟨j₁, div₁, v₂⟩ e₃⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 地模型中的可继续轮状态集合

把原有限状态公式分离为真实关系 D。扩张中的归纳只读取 D 的规范像，
不在扩张的分离公理中使用任意地模型谓词。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_round_set_l (p : Tg_params_d M.Domain) (X R : M.Domain) :
    ∃ D, M.IsSetRelation I D ∧ ∀ n h, Rd_entry_d n h D ↔ M.mem h R ∧ Tg_ready_d hZF p X n h := by
  obtain ⟨C, union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) p.ω R
  let ρ : Env M 8 := ⟨fun i => [p.ω, p.e, p.c, p.b, p.δ, p.A, X, R].get i, fun _ => p.ω⟩
  let φ : BinarySchema 8 := {
    body := .conj (.mem .newest (.bound 9))
      (tg_ready_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 1) .newest) }
  have sat n h : φ.denote ρ n h ↔ M.mem h R ∧ Tg_ready_d hZF p X n h := by
    have h := tg_ready_sat_l hZF ((ρ.push n).push h)
      (⟨.bound 2, .bound 3, .bound 3, .bound 5, .bound 4, .bound 6, .bound 7,
        .bound 3, .bound 3, .bound 3, .bound 3, .bound 3⟩ : Tg_params_d (Term 10)) (.bound 8) (.bound 1) .newest
    exact and_congr Iff.rfl h
  obtain ⟨D, rel, read⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ C
  refine ⟨D, rel.1, fun n h => (read n h).trans ?_⟩
  exact ⟨fun h => (sat n _).mp h.2.2, fun h =>
    ⟨(union n).mpr (Or.inl h.2.1), (union _).mpr (Or.inr h.1), (sat n _).mpr h⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 扩张中的最小编号响应仍产生真实地状态

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
      Rd_entry_d (e h) i K ∧ Rd_entry_d i (e a) g ∧ Cg_scan_d hN (e p.ω) (e L) g (e h) i ∧
      ∃ z y, Fseq_end_d J (e p.ω) t z y ∧ N.mem y (e p.A) ∧ Tg_event_d J (e p.c) (e n) (e p.b) t y ∧
        (¬ Gm_even_d J (e p.ω) (e n) → y = x) ∧
        ∃ h₁ b, M.IsSetFunction I h₁ ∧ Tg_answer_d hM p n h₁ b ∧ Tg_event_d I p.c n p.e h₁ a ∧ Tg_event_d I p.c n p.a t₀ b := by
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
  obtain ⟨next, state, aux, event, hyA, j, fj, clock, answer, ae, be⟩ := ready.advance_l hZFC setup histories owner control hh succ hs₁ hs₂ hs₃
    end₁ end₂ end₃ ((legalImage a₁).mpr legal) value ⟨k₂, fn0_of_function_l (ZF.modelsKP hM) fs₂, digit⟩
  have eqj := fj.domain_eq_l hM.1 (fn0_of_function_l (ZF.modelsKP hM) fs₂); subst j
  obtain ⟨hc, _⟩ := tg_clock_l hM setup.omega setup.empty setup.one setup.two setup.three ready.1
  refine ⟨s₃, i, a₁, rfl, next, state, aux, event, ki, ga, scan, e s₂, e y₀, ⟨d, b, dec⟩,
    (image_member_l e hi he).mpr hyA,
    ⟨e k₂, image_nat_div_l hM hN e hi he setup.omega hc ready.1 clock, last⟩, ?_, s₁, w₀, ?_, answer, ae, be⟩
  · intro odd
    have notOwn : ¬ N.mem (e k₂) (e O) := by
      intro yes
      have phase := (owner.read_l hM (setup.omega.isOrdinal (ZF.modelsKP hM)) (setup.omega.members_areOrdinals (ZF.modelsKP hM) p.c hc)
        ⟨p.b, setup.three.predecessor_mem⟩ hk₂ ready.1 clock).mp ((image_member_l e hi he).mp yes)
      rcases phase with eq | even
      · exact KP.mem_irrefl_d (ZF.modelsKP hM) p.a (eq ▸ setup.two.predecessor_mem)
      · exact odd ((image_even_l hM hN e hi he setup.omega).mp even.2)
    exact own.elim (fun h => (notOwn h.1).elim) And.right
  · obtain ⟨_, _, fs₁⟩ := (histories.1 s₁).mp hs₁
    exact fs₁.1

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 扩张内部的最小请求递归

对地状态集合的像作扩张内部 ω 归纳。每个递归状态都对应真实地有限历史，
且仍受原 I 获胜策略控制；没有借用外部标准 ω 或地模型的外部良基性。
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

theorem Tg_setup_d.generic_states_l {p : Tg_params_d M.Domain} {X F L G O σ R a : M.Domain}
    {g K D T f H : N.Domain}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (histories : Tg_histories_d hM p X F L) (owner : Tg_owner_d hM p.ω p.c p.a p.b O)
    (control : Cg_control_d I true p.ω p.e X F L G O σ R) (ha : M.mem a p.A)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ff : Fn0_d (e p.ω) (e p.A) f)
    (run : Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H) :
    ∀ n h, Rd_entry_d n h H → ∃ n₀ h₀, e n₀ = n ∧ e h₀ = h ∧ M.mem h₀ R ∧ Tg_ready_d hM p X n₀ h₀ := by
  obtain ⟨B, rel, read⟩ := tg_round_set_l hM p X R
  let ρ : Env N 2 := ⟨fun i => [H, e B].get i, fun _ => H⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪∀ h,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 3)⌝ₛ, h, ⌜(.bound 1 : Term 3)⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 3)⌝ₛ, h, ⌜(.bound 2 : Term 3)⌝ₛ)⟫ }
  have sat n : φ.denote ρ n ↔ ∀ h, Rd_entry_d n h H → Rd_entry_d n h (e B) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hN.1, Definitional.Term.eval_weaken]; rfl
  have empty : ∀ x, ¬ N.mem x (e p.e) := fun x hx => (he p.e x).mp hx |>.elim fun y hy => setup.empty y hy.1
  have all : ∀ n, N.mem n (e p.ω) → ∀ h, Rd_entry_d n h H → Rd_entry_d n h (e B) := by
    apply hw.induction
    · obtain ⟨C, sep⟩ := ZF.separation_exists_d hN φ ρ (e p.ω)
      exact ⟨C, fun n => (sep n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz h zh
      have eq := hN.1.eq_of_same_members z (e p.e) (fun x => iff_of_false (hz x) (empty x)); subst z
      have eq := (fn0_function_l (ZF.modelsKP hN) run.1).1.2 (e p.e) h (e p.e) zh (run.2.1 (e p.e) empty); subst h
      exact (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 p.e p.e B).mp
        ((read p.e p.e).mpr ⟨control.root, setup.ready_empty_l hZFC⟩)
    · intro n hn ih m succ h mh
      obtain ⟨s, _, ns⟩ := run.1.2.1 n hn
      obtain ⟨n₀, s₀, state, en, es⟩ := (image_entries_l e he rel n s).mp (ih s ns)
      subst n s
      obtain ⟨hs₀, ready⟩ := (read n₀ s₀).mp state
      obtain ⟨m₀, sm₀, hm₀⟩ := setup.omega.1.2 n₀ ready.1
      have eq := (image_successor_l (hEN := hN.1) e hi he hM.1 sm₀).eq hN.1 succ; subst m
      obtain ⟨x, q, input, pair, qt⟩ := run.2.2 (e n₀) (e m₀) (e s₀) h succ ns mh
      have hx : N.mem x (e p.A) := input.elim (fun h => (ff.bound_l h.2).2)
        (fun h => h.2.symm ▸ (image_member_l e hi he).mpr ha)
      obtain ⟨t₀, _, _, et, ht, next, _⟩ := ready.generic_step_l hZFC hN e hi he setup hd root histories owner control
        hw c surj hs₀ sm₀ hx pair qt
      exact et ▸ (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 m₀ t₀ B).mp ((read m₀ t₀).mpr ⟨ht, next⟩)
  intro n h nh
  obtain ⟨n₀, h₀, nh₀, en, eh⟩ := (image_entries_l e he rel n h).mp (all n (run.1.bound_l nh).1 h nh)
  exact ⟨n₀, h₀, en, eh, (read n₀ h₀).mp nh₀⟩

theorem Tg_setup_d.generic_round_l {p : Tg_params_d M.Domain} {X F L G O σ R a : M.Domain}
    {g K D T f H n : N.Domain}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (histories : Tg_histories_d hM p X F L) (owner : Tg_owner_d hM p.ω p.c p.a p.b O)
    (control : Cg_control_d I true p.ω p.e X F L G O σ R) (ha : M.mem a p.A)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ff : Fn0_d (e p.ω) (e p.A) f)
    (run : Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H) (hn : N.mem n (e p.ω)) :
    ∃ n₀ m₀ h₀ t₀ a₀ i, e n₀ = n ∧ M.SuccessorOf m₀ n₀ ∧ M.mem n₀ p.ω ∧
      Rd_entry_d n (e h₀) H ∧ Rd_entry_d (e m₀) (e t₀) H ∧ M.IsSetFunction I h₀ ∧
      Tg_aux_d hM p n₀ h₀ a₀ ∧ Tg_event_d I p.c n₀ p.e t₀ a₀ ∧
      Rd_entry_d (e h₀) i K ∧ Rd_entry_d i (e a₀) g ∧ Cg_scan_d hN (e p.ω) (e L) g (e h₀) i ∧
      ∃ h₁ b, M.IsSetFunction I h₁ ∧ Tg_answer_d hM p n₀ h₁ b ∧ Tg_event_d I p.c n₀ p.e h₁ a₀ ∧ Tg_event_d I p.c n₀ p.a t₀ b := by
  obtain ⟨h, _, nh⟩ := run.1.2.1 n hn
  obtain ⟨n₀, h₀, en, eh, hh, ready⟩ := setup.generic_states_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run n h nh
  subst n h
  obtain ⟨m₀, succ, hm₀⟩ := setup.omega.1.2 n₀ ready.1
  obtain ⟨t, _, mt⟩ := run.1.2.1 (e m₀) ((image_member_l e hi he).mpr hm₀)
  obtain ⟨x, q, input, pair, qt⟩ := run.2.2 (e n₀) (e m₀) (e h₀) t
    (image_successor_l (hEN := hN.1) e hi he hM.1 succ) nh mt
  have hx : N.mem x (e p.A) := input.elim (fun h => (ff.bound_l h.2).2)
    (fun h => h.2.symm ▸ (image_member_l e hi he).mpr ha)
  obtain ⟨t₀, i, a₀, et, _, _, aux, event, ki, ga, scan, _, _, _, _, _, _, reply⟩ := ready.generic_step_l hZFC hN e hi he setup hd root histories owner control hw c surj hh succ hx pair qt
  obtain ⟨_, _, fh⟩ := (histories.1 h₀).mp (((control.legal h₀).mp ((control.positions h₀).mp hh).1).1)
  exact ⟨n₀, m₀, h₀, t₀, a₀, i, rfl, succ, ready.1, nh, et.symm ▸ mt, fh.1, aux, event, ki, ga, scan, reply⟩

/-- 从原 I 获胜策略与实际枚举直接构造原有限历史策略；全部输入递归都保持地状态。 -/
theorem Tg_game_d.generic_strategy_l {p : Tg_params_d M.Domain} {X F L G O B W C Z v σ a : M.Domain}
    {g S : N.Domain} (game : Tg_game_d hZFC p X F L G O B W C Z v)
    (hd : Woodin_d I p.δ) (root : M.mem p.e p.S) (win : Cg_win_d I true p.ω X F O B W σ)
    (ha : M.mem a p.A) (hw : N.IsOmega (e p.ω)) (fg : Fn0_d (e p.ω) (e X) g)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (space : Fseq_space_d J (e p.ω) (e p.A) S) :
    ∃ R K D T τ, Cg_control_d I true p.ω p.e X F L G O σ R ∧
      Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T ∧ Fn0_d S (e p.A) τ ∧
      (∀ s y, Rd_entry_d s y τ ↔ N.mem s S ∧ Cg_scan_answer_d hN (e p.ω) (e p.A) (e F) T (e p.e) (e a) s y) ∧
      ∀ f, Fn0_d (e p.ω) (e p.A) f → ∃ H, Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H ∧
        ∀ n h, Rd_entry_d n h H → ∃ n₀ h₀, e n₀ = n ∧ e h₀ = h ∧ M.mem h₀ R ∧ Tg_ready_d hM p X n₀ h₀ := by
  obtain ⟨R, control⟩ := cg_control_l hM game.setup.omega game.setup.empty game.histories.1 game.legal
    (game.empty_l hZFC) game.runs game.payoff win
  have empty : ∀ x, ¬ N.mem x (e p.e) := fun x hx => (he p.e x).mp hx |>.elim fun y hy => game.setup.empty y hy.1
  have imageSpace := image_fseq_l hM hN e hi he game.setup.omega hw game.histories.1
  have fs := fn0_of_function_l (ZF.modelsKP hN)
    (image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he (fn0_function_l (ZF.modelsKP hM) win.1))
  have sub : N.MemberSubset (e p.A) (e X) := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := (he p.A x).mp hx
    exact (image_member_l e hi he).mpr (v_transitive_l I game.setup.rank p.A game.setup.letters x₀ hx₀)
  obtain ⟨K, D, T, scan⟩ := cg_scan_table_l hN hw empty imageSpace fg fs sub
  have ha' := (image_member_l e hi he).mpr ha
  obtain ⟨τ, fτ, answer⟩ := scan.strategy_l hN hw empty ha' space
  refine ⟨R, K, D, T, τ, control, scan, fτ, answer, fun f ff => ?_⟩
  have heF := (imageSpace (e p.e)).mpr ⟨e p.e, num_mem_l hN.1 hw (show Num_d 0 (e p.e) from empty), ds_empty_fun_l J empty⟩
  obtain ⟨H, run⟩ := gi_exists_l hN (b := false) hw scan.product scan.response heF ha'
    (fn0_function_l (ZF.modelsKP hN) ff).1 (fun _ _ entry => (ff.bound_l entry).2)
  exact ⟨H, run, game.setup.generic_states_l hZFC hN e hi he hd root game.histories game.owner control ha hw scan surj ff run⟩

end YesMetaZFC.SetTheory.LargeCardinal
