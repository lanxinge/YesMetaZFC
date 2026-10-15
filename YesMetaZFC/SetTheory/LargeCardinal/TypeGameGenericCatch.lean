import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericIndices
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericPlay

/-! # 6.6：稠密条件在指定旧轮之后被实际捕获

先自动界定旧轮和所需实数前缀以前的全部编号。任何达到该稠密要求的泛型
有限条件都在首次越界时被选中；旧事件的保持和实数前缀条件由实际递归推出。
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

theorem Tg_setup_d.capture_threshold_l {p : Tg_params_d M.Domain}
    {X F L G O σ R a ℓ m h₀ a₀ b₀ s t k r β labels : M.Domain} {g K D T f H τ : N.Domain}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (histories : Tg_histories_d hM p X F L) (owner : Tg_owner_d hM p.ω p.c p.a p.b O)
    (control : Cg_control_d I true p.ω p.e X F L G O σ R) (ha : M.mem a p.A)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ff : Fn0_d (e p.ω) (e p.A) f)
    (values : ∀ s y, Rd_entry_d s y τ → Cg_scan_answer_d hN (e p.ω) (e p.A) (e F) T (e p.e) (e a) s y)
    (follows : Gm_follows_d J true (e p.ω) τ f) (run : Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H)
    (hℓ : M.mem ℓ p.ω) (hm : M.SuccessorOf m ℓ) (old : Rd_entry_d (e m) (e h₀) H)
    (event₀ : Tg_event_d I p.c ℓ p.e h₀ a₀) (event₁ : Tg_event_d I p.c ℓ p.a h₀ b₀)
    (hk : M.mem k p.ω) (fs : Fn0_d k p.A s) (cut : N.IsRestrictionOf J (e s) f (e k)) :
    ∃ B, M.mem B p.ω ∧ ∀ q, M.mem q F → Tg_dense_hit_d hM p ℓ s t k r β labels a₀ b₀ B q →
      (∀ j y, Rd_entry_d j y q → Rd_entry_d (e j) (e y) g) →
      ∃ n h a i κ C u, M.mem n p.ω ∧ M.mem ℓ n ∧ Rd_entry_d (e n) (e h) H ∧
        Rd_entry_d (e h) i K ∧ Rd_entry_d i (e a) g ∧ Tg_generic_target_d hM p ℓ s t k r β labels a₀ b₀ κ C a u ∧
        Tg_aux_d hM p n h a := by
  have fn := fn0_function_l (ZF.modelsKP hN) c.enumeration
  have hfn := fn0_function_l (ZF.modelsKP hN) run.1
  obtain ⟨E, inj, er, first⟩ := setup.generic_indices_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run
  -- 界住旧轮及所需前缀以前的全部编号，首达该界的轮次必严格晚于二者。
  have max : ∃ d, M.mem d p.ω ∧ (M.mem ℓ d ∨ ℓ = d) ∧ (M.mem k d ∨ k = d) := by
    rcases (setup.omega.isOrdinal hM).wellOrder.linear.compare ℓ hℓ k hk with eq | lt | gt
    · exact ⟨k, hk, Or.inr (hM.1.eq_of_same_members ℓ k eq), Or.inr rfl⟩
    · exact ⟨k, hk, Or.inl lt, Or.inr rfl⟩
    · exact ⟨ℓ, hℓ, Or.inr rfl, Or.inl gt⟩
  obtain ⟨d, hdω, ld, kd⟩ := max
  obtain ⟨B, hB, bound⟩ := ZF.omega_prefix_bound_l hN hw inj.1 ((image_member_l e hi he).mpr hdω)
  obtain ⟨B₀, hB₀, eq⟩ := (he p.ω B).mp hB; subst B
  refine ⟨B₀, hB₀, fun q hq hit kept => ?_⟩
  obtain ⟨κ, C, a₁, u, i, target, Bi, hiω, ia, before⟩ := hit
  obtain ⟨n, v, hn, nv, cross, prior⟩ := first (e i) ((image_member_l e hi he).mpr hiω)
  have dn : N.mem (e d) n := by
    rcases (hw.isOrdinal hN).wellOrder.linear.compare (e d) ((image_member_l e hi he).mpr hdω) n hn with eq | lt | gt
    · have eq := hN.1.eq_of_same_members (e d) n eq
      exact (cross ((hw.members_areOrdinals hN (e i) ((image_member_l e hi he).mpr hiω)).transitive (e B₀)
        ((image_member_l e hi he).mpr Bi) v (bound n v (Or.inr eq.symm) nv))).elim
    · exact lt
    · exact (cross ((hw.members_areOrdinals hN (e i) ((image_member_l e hi he).mpr hiω)).transitive (e B₀)
        ((image_member_l e hi he).mpr Bi) v (bound n v (Or.inl gt) nv))).elim
  obtain ⟨n₀, m₀, h, t₀, a₂, j, en, _, hn₀, nh, _, _, aux, _, ki, ga, scan, _⟩ :=
    setup.generic_round_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run hn
  subst n
  have dn₀ := (image_member_l e hi he).mp dn
  have on := setup.omega.members_areOrdinals hM n₀ hn₀
  have ln : M.mem ℓ n₀ := ld.elim (fun h => on.transitive d dn₀ ℓ h) (fun eq => eq.symm ▸ dn₀)
  have kn : M.mem k n₀ := kd.elim (fun h => on.transitive d dn₀ k h) (fun eq => eq.symm ▸ dn₀)
  have eqv := inj.1.1.2 (e n₀) v j nv ((er (e n₀) j).mpr ⟨hn, e h, nh, ki⟩); subst v
  obtain ⟨j₀, hj₀, sj⟩ := setup.omega.exists_predecessor_of_mem_of_nonempty hM hn₀ ⟨ℓ, ln⟩
  obtain ⟨j₁, m₁, h₁, t₁, a₃, v, ej, sm, _, jh, mt, _, aux₀, ev, kv, gv, _⟩ :=
    setup.generic_round_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run ((image_member_l e hi he).mpr hj₀)
  have eqj := hi ej; subst j₁
  have eqm := sm.eq hM.1 sj; subst m₁
  have eqt := hi (hfn.1.2 (e n₀) (e t₁) (e h) mt nh); subst t₁
  have vi := prior (e j₀) v ((image_member_l e hi he).mpr sj.predecessor_mem)
    ((er (e j₀) v).mpr ⟨(image_member_l e hi he).mpr hj₀, e h₁, jh, kv⟩)
  obtain ⟨ℓ₀, s₀, κ₀, u₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, data, hκ₀, _⟩ := aux₀
  have hmω := (image_member_l e hi he).mp (run.1.bound_l old).1
  have mn : M.mem m n₀ ∨ m = n₀ := by
    rcases (setup.omega.isOrdinal hM).wellOrder.linear.compare m hmω n₀ hn₀ with eq | lt | gt
    · exact Or.inr (hM.1.eq_of_same_members m n₀ eq)
    · exact Or.inl lt
    · rcases (hm n₀).mp gt with lt | eq
      · exact (KP.mem_irrefl_d (ZF.modelsKP hM) ℓ ((setup.omega.members_areOrdinals hM ℓ hℓ).transitive n₀ lt ℓ ln)).elim
      · have eq := hM.1.eq_of_same_members n₀ ℓ eq
        exact (KP.mem_irrefl_d (ZF.modelsKP hM) ℓ (eq ▸ ln)).elim
  have sub := (image_subset_iff_l e hi he).mp (c.history_mono_l hN hw run (e m) (e n₀) (e h₀) (e h)
    (mn.elim (fun h => Or.inl ((image_member_l e hi he).mpr h)) (fun eq => Or.inr (congrArg e eq))) old nh)
  have keep {b r : M.Domain} (ev : Tg_event_d I p.c ℓ r h₀ b) : Tg_event_d I p.c ℓ r h b := by
    obtain ⟨j, div, z, code, hz⟩ := ev
    exact ⟨j, div, z, code, sub z hz⟩
  -- 历史包含保留旧请求和回答；真实对局一致性给出捕获所需的实数前缀。
  obtain ⟨n', h', en', eh', _, ready⟩ := setup.generic_states_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run (e n₀) (e h) nh
  have eqn := hi en'; subst n'
  have eqh := hi eh'; subst h'
  obtain ⟨_, z₀, z, hz₀, fh, div, digits, _⟩ := ready
  obtain ⟨hc, _⟩ := tg_clock_l hM setup.omega setup.empty setup.one setup.two setup.three hn₀
  have imageDigits := digits.image_l hM hN e hi he setup.omega hc hn₀
    ⟨setup.omega.members_areOrdinals hM z₀ hz₀, (fn0_function_l (ZF.modelsKP hM) fh).1, (fn0_function_l (ZF.modelsKP hM) fh).2.1⟩
  have real := setup.generic_play_l hN e hi he hZFC hd root histories owner control ha hw c surj ff values follows run (e n₀) (e h) (e z) nh imageDigits
  have fs' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he (fn0_function_l (ZF.modelsKP hM) fs)
  have sz := ds_prefix_mono_l J fs' (fn0_function_l (ZF.modelsKP hN) imageDigits.1).1 cut real
    ((hw.members_areOrdinals hN (e n₀) hn).transitive (e k) ((image_member_l e hi he).mpr kn))
  have real₀ := (ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hM) fs) (fn0_function_l (ZF.modelsKP hM) digits.1).1).mpr
    ((image_subset_iff_l e hi he).mp sz)
  obtain ⟨d₀, hd₀, fq⟩ := (histories.1 q).mp hq
  have caught := target.capture_l hM hN e hi he setup.omega hw histories (fn0_of_function_l (ZF.modelsKP hM) fq) hd₀ ia hiω before
    fn.1 kept scan cross gv vi data (setup.limit.1.mem hκ₀) sj ev hn₀ hz₀ fh div digits real₀ ln (keep event₀) (keep event₁)
  have eq := hi (fn.1.2 j (e a₂) (e a₁) ga (caught.1.symm ▸ kept i a₁ ia)); subst a₂
  exact ⟨n₀, h, a₁, j, κ, C, u, hn₀, ln, nh, ki, ga, target, caught.2.2⟩

end YesMetaZFC.SetTheory.LargeCardinal
