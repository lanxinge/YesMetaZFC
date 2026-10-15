import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericRun

/-! # 泛型策略的原对局与辅助实数坐标一致

在扩张内部对实际纯公式作 ω 归纳：偶数轮由有限前缀因果性读取所构造的
I 策略，奇数轮读取对手输入。这里仅搬运有限图和算术，不重解释旧完整类型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} (hM : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)

theorem Tg_digits_d.unique_l {c b n A h z t : M.Domain}
    (left : Tg_digits_d hM c b n A h z) (right : Tg_digits_d hM c b n A h t) : z = t := by
  have fz := fn0_function_l (ZF.modelsKP hM) left.1
  have ft := fn0_function_l (ZF.modelsKP hM) right.1
  apply fz.1.1.eq_of_pairMember_iff hM.1 ft.1.1
  exact fun i y => ⟨fun iy => (right.2 i y (left.1.bound_l iy).1).mpr ((left.2 i y (left.1.bound_l iy).1).mp iy),
    fun iy => (left.2 i y (right.1.bound_l iy).1).mpr ((right.2 i y (right.1.bound_l iy).1).mp iy)⟩

variable {N : Structure.{v}} (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Tg_digits_d.image_l {ω c b n A h z r : M.Domain} (hw : M.IsOmega ω) (hc : M.mem c ω) (hn : M.mem n ω)
    (fh : M.IsSequenceOfLength I h r) (digits : Tg_digits_d hM c b n A h z) :
    Tg_digits_d hN (e c) (e b) (e n) (e A) (e h) (e z) := by
  have fz := fn0_of_function_l (ZF.modelsKP hN)
    (image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he (fn0_function_l (ZF.modelsKP hM) digits.1))
  have fh' := (image_sequence_l hM hN e hi he fh).2.1
  have oc := image_ord_l hM hN e hi he (hw.members_areOrdinals hM c hc)
  refine ⟨fz, fun i y hin => ?_⟩
  obtain ⟨i₀, hi₀, rfl⟩ := (he n i).mp hin
  obtain ⟨v, _, iv⟩ := digits.1.2.1 i₀ hi₀
  have ev : Tg_event_d J (e c) (e i₀) (e b) (e h) (e v) := by
    obtain ⟨j, clock, jv⟩ := (digits.2 i₀ v hi₀).mp iv
    exact ⟨e j, image_nat_div_l hM hN e hi he hw hc (hw.transitive hM n hn i₀ hi₀) clock,
      (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 j v h).mp jv⟩
  have iv' := (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i₀ v z).mp iv
  exact ⟨fun iy => ((fn0_function_l (ZF.modelsKP hN) fz).1.2 (e i₀) (e v) y iv' iy) ▸ ev,
    fun ey => (ev.unique_l hN oc fh' ey) ▸ iv'⟩

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hZ)

theorem Tg_setup_d.generic_play_l {p : Tg_params_d M.Domain} {X F L G O σ R a : M.Domain}
    {g B D T f H τ : N.Domain}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d K p.δ) (root : M.mem p.e p.S)
    (histories : Tg_histories_d hZ p X F L) (owner : Tg_owner_d hZ p.ω p.c p.a p.b O)
    (control : Cg_control_d K true p.ω p.e X F L G O σ R) (ha : M.mem a p.A)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g B D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ff : Fn0_d (e p.ω) (e p.A) f)
    (values : ∀ s y, Rd_entry_d s y τ → Cg_scan_answer_d hN (e p.ω) (e p.A) (e F) T (e p.e) (e a) s y)
    (follows : Gm_follows_d J true (e p.ω) τ f) (run : Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H) :
    ∀ n h z, Rd_entry_d n h H → Tg_digits_d hN (e p.c) (e p.b) n (e p.A) h z → N.IsRestrictionOf J z f n := by
  classical
  have fn := fn0_function_l (ZF.modelsKP hN) ff
  have heω := num_mem_l hZ.1 setup.omega (show Num_d 0 p.e from setup.empty)
  obtain ⟨hc, _⟩ := tg_clock_l hZ setup.omega setup.empty setup.one setup.two setup.three heω
  have oc := image_ord_l hZ hN e hi he (setup.omega.members_areOrdinals hZ p.c hc)
  let ρ : Env N 5 := ⟨fun i => [e p.c, e p.b, e p.A, H, f].get i, fun _ => f⟩
  let φ : UnarySchema 5 := { body := set[6] ⟪∀ h z,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 6)⌝ₛ, h, ⌜(.bound 4 : Term 6)⌝ₛ) →
    ⌜tg_digits_m⌝ₚ(⌜(.bound 1 : Term 6)⌝ₛ, ⌜(.bound 2 : Term 6)⌝ₛ, ⌜(.newest : Term 6)⌝ₛ, ⌜(.bound 3 : Term 6)⌝ₛ, h, z) →
    ⌜(Formula.isRestriction kpair_convention_l)⌝ₚ(z, ⌜(.bound 5 : Term 6)⌝ₛ, ⌜(.newest : Term 6)⌝ₛ)⟫ }
  have sat n : φ.denote ρ n ↔ ∀ h z, Rd_entry_d n h H →
      Tg_digits_d hN (e p.c) (e p.b) n (e p.A) h z → N.IsRestrictionOf J z f n := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hN.1, tg_digits_sat_l hN, Formula.satisfies_isRestriction_iff J, Definitional.Term.eval_weaken]; rfl
  have all : ∀ n, N.mem n (e p.ω) → ∀ h z, Rd_entry_d n h H →
      Tg_digits_d hN (e p.c) (e p.b) n (e p.A) h z → N.IsRestrictionOf J z f n := by
    apply hw.induction
    · obtain ⟨C, sep⟩ := ZF.separation_exists_d hN φ ρ (e p.ω)
      exact ⟨C, fun n => (sep n).trans (and_congr_right fun _ => sat n)⟩
    · intro n hn h z _ digits
      exact ⟨(fn0_function_l (ZF.modelsKP hN) digits.1).1.1, fun i y =>
        ⟨fun iy => (hn i (digits.1.bound_l iy).1).elim, fun iy => (hn i iy.1).elim⟩⟩
    · intro n hn ih m succ t z mt dz
      obtain ⟨h, _, nh⟩ := run.1.2.1 n hn
      obtain ⟨n₀, h₀, en, eh, hh, ready⟩ := setup.generic_states_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run n h nh
      subst n h
      obtain ⟨m₀, sm, hm⟩ := setup.omega.1.2 n₀ ready.1
      have eq := (image_successor_l (hEN := hN.1) e hi he hZ.1 sm).eq hN.1 succ; subst m
      have saved := ready
      obtain ⟨hn₀, r, s, hr, fh, _, digits, _⟩ := saved
      have old := digits.image_l hZ hN e hi he setup.omega hc hn₀
        ⟨setup.omega.members_areOrdinals hZ r hr, (fn0_function_l (ZF.modelsKP hZ) fh).1, (fn0_function_l (ZF.modelsKP hZ) fh).2.1⟩
      have cut := ih (e h₀) (e s) nh old
      obtain ⟨x, q, input, pair, qt⟩ := run.2.2 (e n₀) (e m₀) (e h₀) t succ nh mt
      have hx : N.mem x (e p.A) := input.elim (fun h => (ff.bound_l h.2).2)
        (fun h => h.2.symm ▸ (image_member_l e hi he).mpr ha)
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, z₀, y, endt, hy, event, odd, _⟩ :=
        ready.generic_step_l hZFC hN e hi he setup hd root histories owner control hw c surj hh sm hx pair qt
      obtain ⟨_, _, _, _, _, _, _, _, _, _, e₁, _, _, e₂, _, _, _, e₃⟩ := c.step (e h₀) x q t pair qt
      have sub : N.MemberSubset (e h₀) t := fun v hv => e₃.subset_l J v (e₂.subset_l J v (e₁.subset_l J v hv))
      obtain ⟨_, _, ft⟩ := (c.space t).mp (run.1.bound_l mt).2
      obtain ⟨z', endz, dz'⟩ := old.append_l hN hw oc hn succ sub ft.1 hy event
      have eq := dz'.unique_l hN dz; subst z'
      obtain ⟨v, _, nv⟩ := ff.2.1 (e n₀) hn
      have yv : y = v := by
        by_cases even : Gm_even_d J (e p.ω) (e n₀)
        · have xa : x = e a := input.elim (fun h => (h.1 even).elim) And.right
          exact (cg_scan_answer_prefix_l hN hw (fn0_function_l (ZF.modelsKP hN) c.response).1 fn.1 fn.2.1
            run cut nh (xa ▸ pair) qt endt hy (values (e s) v (follows (e n₀) hn even (e s) cut v nv))).symm
        · exact (odd even).trans (input.elim (fun h => fn.1.2 (e n₀) x v h.2 nv)
            (fun h => (h.1 ⟨even, v, nv⟩).elim))
      exact (ds_restrict_iff_l J (fn0_function_l (ZF.modelsKP hN) dz.1) fn.1).mpr
        (ds_append_sub_l J hN.1 (fn0_function_l (ZF.modelsKP hN) old.1) endz
          ((ds_restrict_iff_l J (fn0_function_l (ZF.modelsKP hN) old.1) fn.1).mp cut) (yv.symm ▸ nv))
  exact fun n h z nh dz => all n (run.1.bound_l nh).1 h z nh dz

end YesMetaZFC.SetTheory.LargeCardinal
