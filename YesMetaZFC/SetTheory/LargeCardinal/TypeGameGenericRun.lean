import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericStep
import YesMetaZFC.SetTheory.LargeCardinal.TypeGame

/-! # 扩张内部的最小请求递归

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
    exact (image_member_l e hi he).mpr (ZF.v_transitive_l I hM game.setup.rank p.A game.setup.letters x₀ hx₀)
  obtain ⟨K, D, T, scan⟩ := cg_scan_table_l hN hw empty imageSpace fg fs sub
  have ha' := (image_member_l e hi he).mpr ha
  obtain ⟨τ, fτ, answer⟩ := scan.strategy_l hN hw empty ha' space
  refine ⟨R, K, D, T, τ, control, scan, fτ, answer, fun f ff => ?_⟩
  have heF := (imageSpace (e p.e)).mpr ⟨e p.e, num_mem_l hN.1 hw (show Num_d 0 (e p.e) from empty), ds_empty_fun_l J empty⟩
  obtain ⟨H, run⟩ := gi_exists_l hN (b := false) hw scan.product scan.response heF ha'
    (fn0_function_l (ZF.modelsKP hN) ff).1 (fun _ _ entry => (ff.bound_l entry).2)
  exact ⟨H, run, game.setup.generic_states_l hZFC hN e hi he hd root game.histories game.owner control ha hw scan surj ff run⟩

end YesMetaZFC.SetTheory.LargeCardinal
