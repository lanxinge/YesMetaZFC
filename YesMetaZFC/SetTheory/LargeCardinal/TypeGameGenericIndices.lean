import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericRun
import YesMetaZFC.SetTheory.Ord.FirstCrossing
import YesMetaZFC.SetTheory.RelationChain

/-! # 实际最小请求编号的无界性与首达时刻

所选编号可以回落，但请求的参数域逐轮严格增长，因此编号不能重复。
参数域图在扩张中由真实公式构造；内部 ω 单射不可能有有限上界。
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

theorem Tg_setup_d.generic_indices_l {p : Tg_params_d M.Domain} {X F L G O σ R a : M.Domain}
    {g K D T f H : N.Domain}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (histories : Tg_histories_d hM p X F L) (owner : Tg_owner_d hM p.ω p.c p.a p.b O)
    (control : Cg_control_d I true p.ω p.e X F L G O σ R) (ha : M.mem a p.A)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ff : Fn0_d (e p.ω) (e p.A) f)
    (run : Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H) :
    ∃ E, N.IsSetInjectionFromTo J E (e p.ω) (e p.ω) ∧
      (∀ n i, Rd_entry_d n i E ↔ N.mem n (e p.ω) ∧ ∃ h, Rd_entry_d n h H ∧ Rd_entry_d h i K) ∧
      ∀ i, N.mem i (e p.ω) → ∃ n v, N.mem n (e p.ω) ∧ Rd_entry_d n v E ∧ ¬ N.mem v i ∧
        ∀ m w, N.mem m n → Rd_entry_d m w E → N.mem w i := by
  have hf := fn0_function_l (ZF.modelsKP hN) run.1
  have gf := fn0_function_l (ZF.modelsKP hN) c.enumeration
  obtain ⟨E, ef, er⟩ := ZF.exists_compositionFunction hN J hf (fn0_function_l (ZF.modelsKP hN) c.indices)
  have stage (n : N.Domain) (hn : N.mem n (e p.ω)) :
      ∃ n₀ m₀ h₀ t₀ a₀ i ℓ s κ u B, e n₀ = n ∧ M.SuccessorOf m₀ n₀ ∧ M.mem n₀ p.ω ∧
        Rd_entry_d n (e h₀) H ∧ Rd_entry_d (e m₀) (e t₀) H ∧ M.IsSetFunction I h₀ ∧
        Tg_aux_data_d a₀ ℓ s κ u ∧ M.mem κ p.δ ∧ Tg_growth_d hM p.e p.c p.A n₀ h₀ κ B ∧
        Tg_event_d I p.c n₀ p.e t₀ a₀ ∧ Rd_entry_d n i E ∧ Rd_entry_d i (e a₀) g := by
    obtain ⟨n₀, m₀, h₀, t₀, a₀, i, en, succ, hn₀, nh, mt, fh₀, aux, event, ki, ga, _⟩ :=
      setup.generic_round_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run hn
    obtain ⟨ℓ, s, κ, u, _, _, _, _, _, B, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      data, hκ, _, _, _, _, _, _, _, _, _, _, _, growth, _⟩ := aux
    exact ⟨n₀, m₀, h₀, t₀, a₀, i, ℓ, s, κ, u, B, en, succ, hn₀, nh, mt, fh₀, data, hκ, growth,
      event, (er n i).mpr ⟨hn, e h₀, nh, ki⟩, ga⟩
  let ρ : Env N 2 := ⟨fun i => [E, g].get i, fun _ => g⟩
  let φ : BinarySchema 2 := { body := set[4] ⟪∃ i a ℓ s u,
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ, i, ⌜(.bound 2 : Term 4)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(i, a, ⌜(.bound 3 : Term 4)⌝ₛ) ∧ ⌜tg_aux_data_m⌝ₚ(a, ℓ, s, ⌜(.newest : Term 4)⌝ₛ, u)⟫ }
  have sat n κ : φ.denote ρ n κ ↔ ∃ i a ℓ s u, Rd_entry_d n i E ∧ Rd_entry_d i a g ∧ Tg_aux_data_d a ℓ s κ u := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hN.1, tg_aux_data_sat_l hN.1, Definitional.Term.eval_weaken]; rfl
  have align {n κ κ' i b ℓ s u : N.Domain} (ni : Rd_entry_d n i E) (ib : Rd_entry_d i b g)
      (data : Tg_aux_data_d b ℓ s κ' u) (value : φ.denote ρ n κ) : κ = κ' := by
    obtain ⟨j, b', ℓ', s', u', nj, jb, other⟩ := (sat n κ).mp value
    have eq := ef.1.2 n j i nj ni; subst j
    have eq := gf.1.2 i b' b jb ib; subst b'
    exact (other.unique_l data).2.2.1
  obtain ⟨P, pf, pr⟩ := ZF.exists_setFunctionFromTo_of_denote hN J φ ρ (source := e p.ω) (target := e p.δ) (by
    intro n hn
    obtain ⟨_, _, _, _, b, i, ℓ, s, κ, u, _, _, _, _, _, _, _, data, _, _, _, ni, ib⟩ := stage n hn
    exact ⟨e κ, (sat n (e κ)).mpr ⟨i, e b, e ℓ, e s, e u, ni, ib, data.image_l e he⟩⟩) (by
    intro n _ κ ν hκ hν
    obtain ⟨i, b, ℓ, s, u, ni, ib, data⟩ := (sat n ν).mp hν
    exact align ni ib data hκ) (by
    intro n κ hn val
    obtain ⟨_, _, _, _, b, i, ℓ, s, κ₀, u, _, _, _, _, _, _, _, data, hκ₀, _, _, ni, ib⟩ := stage n hn
    exact (align ni ib (data.image_l e he) val).symm ▸ (image_member_l e hi he).mpr hκ₀)
  have next {n m κ ν : N.Domain} (succ : N.SuccessorOf m n) (nk : Rd_entry_d n κ P) (ml : Rd_entry_d m ν P) : N.mem κ ν := by
    obtain ⟨n₀, m₀, h₀, t₀, b₀, i₀, ℓ₀, s₀, κ₀, u₀, B₀, en, sm, hn₀, nh, mt, _, data₀, _, _, ev₀, ni₀, ib₀⟩ :=
      stage n (pf.input_mem_of_pairMember nk)
    obtain ⟨n₁, m₁, h₁, t₁, b₁, i₁, ℓ₁, s₁, κ₁, u₁, B₁, em, _, _, mh, _, fh₁, data₁, _, growth, _, mi₁, ib₁⟩ :=
      stage m (pf.input_mem_of_pairMember ml)
    have ek := align ni₀ ib₀ (data₀.image_l e he) ((pr n κ).mp nk).2
    have el := align mi₁ ib₁ (data₁.image_l e he) ((pr m ν).mp ml).2
    subst n m
    have eq := hi ((image_successor_l (hEN := hN.1) e hi he hM.1 sm).eq hN.1 succ); subst n₁
    have eq := hi (hf.1.2 (e m₀) (e t₀) (e h₁) mt mh); subst h₁
    have lt : M.mem κ₀ κ₁ := by
      rcases growth with ⟨eq, _⟩ | ⟨j, b, ℓ, s, τ, u, sj, ev, data, below⟩
      · exact (setup.empty n₀ (eq ▸ sm.predecessor_mem)).elim
      · have eq := sm.predecessor_eq hM.1 (setup.omega.members_areOrdinals hM n₀ hn₀) sj; subst j
        obtain ⟨hc, _⟩ := tg_clock_l hM setup.omega setup.empty setup.one setup.two setup.three hn₀
        have eq := ev.unique_l hM (setup.omega.members_areOrdinals hM p.c hc) fh₁ ev₀; subst b
        exact (data.unique_l data₀).2.2.1 ▸ below
    exact ek.symm ▸ el.symm ▸ (image_member_l e hi he).mpr lt
  let δenv : Env M 1 := ⟨fun _ => p.δ, fun _ => p.δ⟩
  have oδ : N.IsOrdinal (e p.δ) := (KP.ord0_sat_l (ZF.modelsKP hN) (image_env_l e δenv) .newest).mp
    ((delta0_image_l e hi he (KP.ord0_delta_l .newest) δenv).mp
      ((KP.ord0_sat_l (ZF.modelsKP hM) δenv .newest).mpr setup.limit.1))
  let μ : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  have chain := ZF.rel_chain_l J hN μ ⟨Fin.elim0, fun _ => g⟩ hw pf
    (fun x y z _ _ hz xy yz => (oδ.mem hz).transitive y yz x xy) (fun _ _ _ _ succ nk ml => next succ nk ml)
  have inj : N.IsSetInjectionFromTo J E (e p.ω) (e p.ω) := by
    refine ⟨ef, fun n m i ni mi => ?_⟩
    obtain ⟨κ, _, nk⟩ := pf.2.2 n (ef.input_mem_of_pairMember ni)
    obtain ⟨ν, _, ml⟩ := pf.2.2 m (ef.input_mem_of_pairMember mi)
    obtain ⟨j, b, ℓ, s, u, nj, jb, data⟩ := (sat n κ).mp ((pr n κ).mp nk).2
    have eq := ef.1.2 n j i nj ni; subst j
    have eq : ν = κ := align mi jb data ((pr m ν).mp ml).2; subst ν
    rcases (hw.isOrdinal hN).wellOrder.linear.compare n (ef.input_mem_of_pairMember ni) m (ef.input_mem_of_pairMember mi) with eq | lt | gt
    · exact hN.1.eq_of_same_members n m eq
    · exact (KP.mem_irrefl_d (ZF.modelsKP hN) κ (chain n m κ κ lt nk ml)).elim
    · exact (KP.mem_irrefl_d (ZF.modelsKP hN) κ (chain m n κ κ gt ml nk)).elim
  exact ⟨E, inj, er, fun i hi => ZF.omega_first_crossing_l hN hw inj hi⟩

end YesMetaZFC.SetTheory.LargeCardinal
