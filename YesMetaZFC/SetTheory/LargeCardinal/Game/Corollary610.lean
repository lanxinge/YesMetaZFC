import YesMetaZFC.SetTheory.LargeCardinal.Game.OddBranch
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Game.GenericRun
import YesMetaZFC.SetTheory.Ord.FirstCrossing
import YesMetaZFC.SetTheory.RelationChain
import YesMetaZFC.SetTheory.LargeCardinal.Game.DigitsImage
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReturnSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.HullReturn
import YesMetaZFC.SetTheory.LargeCardinal.Game.EvenLimit
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReturnBranch
import YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedProjection
import YesMetaZFC.SetTheory.LargeCardinal.Game.StrategyPlay
import YesMetaZFC.SetTheory.LargeCardinal.Game.TreeStep
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.SetTheory.LargeCardinal.Game.LevelReply
import YesMetaZFC.SetTheory.LargeCardinal.Game.Tracked
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.InaccessibleEnumeration
import YesMetaZFC.Model.Forcing.Collapse.NameCode
import YesMetaZFC.Model.Forcing.Collapse.FiniteRecode
import YesMetaZFC.SetTheory.Descriptive.Game.GameShift

/-! # 实际运行终点提供并树的逐节点呈示 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.models_l {ω c o C γ Z A D H Q : M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D H)
    (column : ∀ x, M.mem x Q ↔ Tg_run_value_d (n := 63) 9 H x) :
    ∀ i d, Rd_entry_d i d Q → It_mem_d I d := by
  rintro i d ⟨p,pair,hp⟩
  obtain ⟨v,k,s,hs,code,hp⟩ := (column p).mp hp
  have state := (h.read_l hZF hs code).1
  have entry : Rd_entry_d i d (v 9) := ⟨p,pair,hp⟩
  have hi := (state.tree.tree.diagram.model_domain i).mpr ⟨d,entry⟩
  exact state.tree.models_before_l hZF state.finite state.node
    ⟨v 0,v 1,state.model,state.source.source.transitive⟩ i d
    (((state.successor i).mp hi).elim Or.inr (fun eq => Or.inl (hZF.1.eq_of_same_members i (v 7) eq))) entry

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际最小请求编号的无界性与首达时刻

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
      · have eq := sm.predecessor_eq hM.1 (setup.omega.members_areOrdinals (ZF.modelsKP hM) n₀ hn₀) sj; subst j
        obtain ⟨hc, _⟩ := tg_clock_l hM setup.omega setup.empty setup.one setup.two setup.three hn₀
        have eq := ev.unique_l hM (setup.omega.members_areOrdinals (ZF.modelsKP hM) p.c hc) fh₁ ev₀; subst b
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
    rcases (hw.isOrdinal (ZF.modelsKP hN)).wellOrder.linear.compare n (ef.input_mem_of_pairMember ni) m (ef.input_mem_of_pairMember mi) with eq | lt | gt
    · exact hN.1.eq_of_same_members n m eq
    · exact (KP.mem_irrefl_d (ZF.modelsKP hN) κ (chain n m κ κ lt nk ml)).elim
    · exact (KP.mem_irrefl_d (ZF.modelsKP hN) κ (chain m n κ κ gt ml nk)).elim
  exact ⟨E, inj, er, fun i hi => ZF.omega_first_crossing_l hN hw inj hi⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 泛型策略的原对局与辅助实数坐标一致

在扩张内部对实际纯公式作 ω 归纳：偶数轮由有限前缀因果性读取所构造的
I 策略，奇数轮读取对手输入。这里仅搬运有限图和算术，不重解释旧完整类型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} (hM : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)

variable {N : Structure.{v}} (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he
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
  have oc := image_ord_l hZ hN e hi he (setup.omega.members_areOrdinals (ZF.modelsKP hZ) p.c hc)
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
        ⟨setup.omega.members_areOrdinals (ZF.modelsKP hZ) r hr, (fn0_function_l (ZF.modelsKP hZ) fh).1, (fn0_function_l (ZF.modelsKP hZ) fh).2.1⟩
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

/-! ## 6.6：稠密条件在指定旧轮之后被实际捕获

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
    rcases (setup.omega.isOrdinal (ZF.modelsKP hM)).wellOrder.linear.compare ℓ hℓ k hk with eq | lt | gt
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
    rcases (hw.isOrdinal (ZF.modelsKP hN)).wellOrder.linear.compare (e d) ((image_member_l e hi he).mpr hdω) n hn with eq | lt | gt
    · have eq := hN.1.eq_of_same_members (e d) n eq
      exact (cross ((hw.members_areOrdinals (ZF.modelsKP hN) (e i) ((image_member_l e hi he).mpr hiω)).transitive (e B₀)
        ((image_member_l e hi he).mpr Bi) v (bound n v (Or.inr eq.symm) nv))).elim
    · exact lt
    · exact (cross ((hw.members_areOrdinals (ZF.modelsKP hN) (e i) ((image_member_l e hi he).mpr hiω)).transitive (e B₀)
        ((image_member_l e hi he).mpr Bi) v (bound n v (Or.inl gt) nv))).elim
  obtain ⟨n₀, m₀, h, t₀, a₂, j, en, _, hn₀, nh, _, _, aux, _, ki, ga, scan, _⟩ :=
    setup.generic_round_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run hn
  subst n
  have dn₀ := (image_member_l e hi he).mp dn
  have on := setup.omega.members_areOrdinals (ZF.modelsKP hM) n₀ hn₀
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
    rcases (setup.omega.isOrdinal (ZF.modelsKP hM)).wellOrder.linear.compare m hmω n₀ hn₀ with eq | lt | gt
    · exact Or.inr (hM.1.eq_of_same_members m n₀ eq)
    · exact Or.inl lt
    · rcases (hm n₀).mp gt with lt | eq
      · exact (KP.mem_irrefl_d (ZF.modelsKP hM) ℓ ((setup.omega.members_areOrdinals (ZF.modelsKP hM) ℓ hℓ).transitive n₀ lt ℓ ln)).elim
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
    ⟨setup.omega.members_areOrdinals (ZF.modelsKP hM) z₀ hz₀, (fn0_function_l (ZF.modelsKP hM) fh).1, (fn0_function_l (ZF.modelsKP hM) fh).2.1⟩
  have real := setup.generic_play_l hN e hi he hZFC hd root histories owner control ha hw c surj ff values follows run (e n₀) (e h) (e z) nh imageDigits
  have fs' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he (fn0_function_l (ZF.modelsKP hM) fs)
  have sz := ds_prefix_mono_l J fs' (fn0_function_l (ZF.modelsKP hN) imageDigits.1).1 cut real
    ((hw.members_areOrdinals (ZF.modelsKP hN) (e n₀) hn).transitive (e k) ((image_member_l e hi he).mpr kn))
  have real₀ := (ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hM) fs) (fn0_function_l (ZF.modelsKP hM) digits.1).1).mpr
    ((image_subset_iff_l e hi he).mp sz)
  obtain ⟨d₀, hd₀, fq⟩ := (histories.1 q).mp hq
  have caught := target.capture_l hM hN e hi he setup.omega hw histories (fn0_of_function_l (ZF.modelsKP hM) fq) hd₀ ia hiω before
    fn.1 kept scan cross gv vi data (setup.limit.1.mem hκ₀) sj ev hn₀ hz₀ fh div digits real₀ ln (keep event₀) (keep event₁)
  have eq := hi (fn.1.2 j (e a₂) (e a₁) ga (caught.1.symm ▸ kept i a₁ ia)); subst a₂
  exact ⟨n₀, h, a₁, j, κ, C, u, hn₀, ln, nh, ki, ga, target, caught.2.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 返回分支上的原恢复图

5.15 的返回构造先回拉完整存档，再取同一返回锥的像。共用的节点、增长
证书及其公式位于 ReturnSyntax，指定良基分支的直接构造使用同一组证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.odd_limit_l {ω c o C γ Z A D f X B b : M.Domain} {U : Fin 6 → M.Domain}
    {k} {v : Fin k → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (archive : M.IsSetFunction I (U 5))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x)
    (back : It_hull_return_d hZF ω o c X (U 0) (U 1) (U 2) (U 3) (U 4) B b
      (Fin.cases (U 5) v)) :
    ∃ π N P, Tg_return_model_d hZF ω o c X (U 0) (U 1) (U 2) b π N P ∧
      Tg_odd_limit_d hZF ω (U 0) (U 2) b (U 5) π N P ∧
      ∀ i, ∃ x, Rd_entry_d x (v i) π := by
  obtain ⟨B₀, Rₐ, a, K, V₀, Rᵤ, u, J, π, c₀, X₀, R₀, π₀, Q₀, G₀, E₀, L₀,
    sb, su, mb, mu, hj, _, mx₀, xt₀, hcc, hXX, restrict, _, small, models, hQ, hG, _, _, ret, _, params⟩ := back
  obtain ⟨H₀, _, hH⟩ := params 0
  obtain ⟨_, _, _, _, _, _, d, N, W, P, σ, branch, _, _, mn, cone, ready, hs, _, root⟩ := ret
  have hw := tree.tree.omega
  obtain ⟨j, hroot, comp, _, _⟩ := root
  have omega := hj.omega_l I hZF hw sb.transitive su.transitive mb mu sb.omega_mem
  have nat := hj.natural_l hZF hw sb.transitive su.transitive mb mu sb.omega_mem
  have ar := h.archive_l hZF hw columns
  have hf : Tg_graph_d I ω H₀ := (hj.tg_graph_l hZF hw sb.transitive su.transitive mb mu omega hH).mpr ⟨archive, ar.1⟩
  obtain ⟨_, sn⟩ := ready
  have actual i c (hc : Rd_entry_d i c Q₀) := (small.tree.sources i c hc).mem_l hZF
    (models i c hc)
  have compatible := it_cone_pull_subset_l hZF hw sb.transitive su.transitive sn.transitive mb mu mn hj
    sb.omega_mem (hj.1.1.input_mem_of_pairMember hQ) hG small.tree.diagram tree.tree.diagram models cone.toIt_embedding_d
  have growth := compatible.odd_l hZF hw tree.tree.diagram ar.2.1 ar.2.2
  suffices nodes : ∀ m i r t₀, M.mem i b → Rd_entry_d m r (U 5) → KPair_d M r i t₀ → ∃ n S s t g,
      M.mem n ω ∧ M.mem S N ∧ M.mem s N ∧ M.mem t N ∧ M.mem g N ∧
      Tg_node_d I n S s t g ∧ Tg_return_node_d ω (U 5) π P m i n S s t g by
    refine ⟨π, N, P, ⟨B₀, Rₐ, a, V₀, Rᵤ, u, Q₀, G₀, c₀, X₀, R₀, π₀, d, W, σ,
      sb.transitive, su.transitive, sb.omega_mem, mb, mu, hj, hQ, hG, mx₀, hcc, hXX, restrict,
      small.tree.diagram, mn, cone.toIt_embedding_d, hs, ⟨j, hroot, comp⟩⟩,
      ⟨sn.transitive, sn.omega_mem, hj.1.2, cone.function, ?_, nodes,
        growth.growth_l hZF hw tree.tree.diagram.order branch archive nodes⟩,
      fun i => (params i.succ).elim fun x h => ⟨x, h.2⟩⟩
    intro i j hij
    obtain ⟨c, X, R, hc, mx⟩ := small.tree.diagram.model_l hZF (branch.subset i ((cone.domain i).mpr ⟨j, hij⟩))
    exact (cone.elementary i j c X R hij hc mx).1.1.1
  intro m i r t₀ hi hr pair
  have hm := (ar.1 m).mpr ⟨r, hr⟩
  obtain ⟨r₀, hr₀⟩ := (hf.2 m).mp hm
  have hrB := (rd_entry_transitive_l sb.transitive (hj.1.1.input_mem_of_pairMember hH) hr₀).2
  obtain ⟨r', _, hrr⟩ := hj.1.1.2.2 r₀ hrB
  have eq := archive.2 m r' r ((hj.entry_l hZF hw sb.transitive su.transitive mb mu (nat m hm) hrr hH).mp hr₀) hr
  subst r'
  obtain ⟨p, pr, hp⟩ := hr
  obtain ⟨v, k, z, hz, code, hp⟩ := (columns 5 p).mp hp
  obtain ⟨i', Y, R, μ, K, η, C, L, V, q, cell, sy, saved, _⟩ := (h.read_l hZF hz code).1.past.rows m r ⟨p, pr, hp⟩
  have eq : i' = i := (kpair_injective_l M cell.choose_spec.1 pair).1
  subst i'
  have row : Tg_past_at_d (U 5) m i Y R μ K η C L V q :=
    ⟨r, ⟨p, pr, (columns 5 p).mpr ⟨v, k, z, hz, code, hp⟩⟩, cell⟩
  obtain ⟨w, _, images⟩ := hj.tuple_preimage_l hZF hw sb.transitive su.transitive mb mu hrr cell
  obtain ⟨cY, modelY⟩ := sy.source.code
  obtain ⟨ρ, cq, _, _, _⟩ := saved.membership_l I hZF.1 modelY (sy.source.transitive C saved.context.member)
    ⟨⟨ω, saved.context.omega_l ⟨cY, modelY⟩⟩⟩
  -- 外层回拉确实作用于隶属模型中的同一记录；仅在这里作字面元组解释。
  have tuple : Rt_tuple_d (Fin.cases ω (Fin.cases V (fun i => (ρ.bound i).val))) q := by
    obtain ⟨mem, valid⟩ := ((tg_saved_code_read_l I hZF.1).mp cq).2
    let ny : Nonempty {x // M.mem x Y} := ⟨⟨q, mem 0⟩⟩
    let v : Fin 56 → (rt_model_l Y ny).Domain := fun i =>
      ⟨(Fin.cases ω (Fin.cases V (fun i => (ρ.bound i).val)) : Fin 56 → M.Domain) i, mem i.succ⟩
    let q₀ : (rt_model_l Y ny).Domain := ⟨q, mem 0⟩
    let ε : Env (rt_model_l Y ny) 57 := ⟨Fin.cases q₀ v, fun _ => q₀⟩
    have valid : Formula.satisfies ε (rt_tuple_m (fun i : Fin 56 => .bound i.succ) .newest) :=
      (smem_formula_l I modelY ny _ ε).mpr ((Formula.closed_env_l _
        (rt_tuple_closed_l _ _ (fun _ => rfl) rfl) (funext (Fin.cases rfl (fun _ => rfl)))).mp valid)
    exact (rt_tuple_source_l hZF.1 sy.source.transitive ny v q₀).mp
      ((rt_tuple_sat_l (rt_model_ext_l hZF.1 sy.source.transitive ny) ε (fun i : Fin 56 => .bound i.succ) .newest).mp valid)
  obtain ⟨s, _, values⟩ := hj.tuple_preimage_l hZF hw sb.transitive su.transitive mb mu (images 9) tuple
  obtain ⟨hn, member, node⟩ := saved.node_l hZF hw modelY sy.source.transitive cq
  let n := (ρ.bound 22).val
  have hiω := branch.subset i hi
  obtain ⟨a₀, ha₀⟩ := (small.tree.diagram.model_domain i).mp hiω
  have yt := sy.source.transitive
  obtain ⟨Y₀, R', K', my, sy⟩ := actual i a₀ ha₀
  have haB := (rd_entry_transitive_l sb.transitive (hj.1.1.input_mem_of_pairMember hQ) ha₀).2
  obtain ⟨a', _, haa⟩ := hj.1.1.2.2 a₀ haB
  have ha := (hj.entry_l hZF hw sb.transitive su.transitive mb mu (nat i hiω) haa hQ).mp ha₀
  obtain ⟨a'', ha', my'⟩ := ar.2.1 m i Y R μ K η C L V q row
  have eq := tree.tree.diagram.model_function.2 i a' a'' ha ha'
  subst a''
  obtain ⟨Y', R'', _, orig, source⟩ := (tree.tree.sources i a' ha).mem_l hZF ⟨Y, R, my', yt⟩
  obtain ⟨eY, eR⟩ := smdl_unique_l I orig.1 my'.1
  subst Y' R''
  obtain ⟨Y', R'', _, _, my'', _, imageY, _⟩ := ep_set_source_pull_l hZF sb su mb mu hj haa my' source
  obtain ⟨eY, eR⟩ := smdl_unique_l I my''.1 my.1
  subst Y' R''
  have smallMember (a : Fin 54) : M.mem (s a.succ.succ) Y₀ :=
    (hj.member_l I hZF hw mb mu (values a.succ.succ) imageY).mpr (member a)
  let x : Fin 5 → M.Domain := fun a => [n, s 21, s 42, s 43, s 44].get a
  let y : Fin 5 → M.Domain := fun a => [n, (ρ.bound 19).val, (ρ.bound 40).val, (ρ.bound 41).val, (ρ.bound 42).val].get a
  have xy : ∀ a, Rd_entry_d (x a) (y a) π :=
    Fin.cases (nat n hn) (Fin.cases (values 21) (Fin.cases (values 42)
      (Fin.cases (values 43) (Fin.cases (values 44) (fun a => Fin.elim0 a)))))
  have smallNode := (hj.tg_node_l hZF hw sb.transitive su.transitive mb mu xy).mpr node
  obtain ⟨j, hjP⟩ := (cone.domain i).mp hi
  have leg := cone.elementary i j a₀ Y₀ R' hjP ha₀ my.1
  obtain ⟨S, hS, iS⟩ := leg.1.1.2.2 (s 21) (smallMember 19)
  obtain ⟨s', hs', is⟩ := leg.1.1.2.2 (s 42) (smallMember 40)
  obtain ⟨t', ht', it⟩ := leg.1.1.2.2 (s 43) (smallMember 41)
  obtain ⟨g, hg, ig⟩ := leg.1.1.2.2 (s 44) (smallMember 42)
  have fixed := leg.natural_l hZF hw sy.transitive sn.transitive my mn sy.omega_mem n hn
  let y' : Fin 5 → M.Domain := fun a => [n, S, s', t', g].get a
  have image : ∀ a, Rd_entry_d (x a) (y' a) j :=
    Fin.cases fixed (Fin.cases iS (Fin.cases is (Fin.cases it (Fin.cases ig (fun a => Fin.elim0 a)))))
  exact ⟨n, S, s', t', g, hn, hS, hs', ht', hg,
    (leg.tg_node_l hZF hw sy.transitive sn.transitive my mn image).mp smallNode,
    Y, R, μ, K, η, C, L, V, q, (fun a => (ρ.bound a).val), row, cq, rfl,
    s 21, s 42, s 43, s 44, j, values 21, values 42, values 43, values 44, hjP, iS, is, it, ig⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意原对局的统一历史返回原树分支

有限树取并产生共尾偶数不良基枝；回拉实际下降见证后得到不再重置的奇数尾枝。
三张坐标图在同一返回极限中取并。根图保留原树，固定锚点保留原实局前缀，
因此返回分支的第一坐标恰好是输入对局。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.branch_l {ω c o C γ Z A D H θ X R S x Y F : M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D H) (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o)
    (rank : V_d I θ X) (model : Smem_d I c X R) (memS : M.mem S X)
    (names : ∀ i r, Rd_entry_d i r H → Tg_run_name_d S r)
    (played : ∀ i r, Rd_entry_d i r H → ∃ n s, M.SuccessorOf n i ∧ Tg_run_real_d I A n r s ∧ M.IsRestrictionOf I s x n)
    (input : Fn0_d ω A x) (space : Fseq_space_d I ω Y F) (closed : Tree_d F S) :
    ∃ q t u, Fn0_d ω Y q ∧ Branch_d F S q ∧ Tg_graph_d I ω t ∧ Tg_graph_d I ω u ∧ Tg_join_d I ω x t u q := by
  obtain ⟨U,tree,archive,columns⟩ := h.union_l hZF hw
  have root := tree.tree.root o ho
  have rootTree := h.root_tree_l hZF columns names
  have plays := h.archive_play_l hZF tree columns root model played
  obtain ⟨B,branch,bs⟩ := h.even_branch_l hZF tree.tree columns
  have ill := h.even_limit_l hZF tree columns branch bs
  obtain ⟨b,back⟩ := it_hull_return_l hZFC tree (h.models_l hZF (columns 1)) model rank ho ill
    (Fin.cases (U 5) (Fin.cases H (fun _ : Fin 1 => S)))
  obtain ⟨odd,different⟩ := back.branch_l hZF
  obtain ⟨_,tail⟩ := h.odd_tail_l hZF tree columns branch bs odd different
  obtain ⟨π,N,P,returnedModel,limit,params⟩ := h.odd_limit_l hZF tree archive columns back
  obtain ⟨D',J,F',returned⟩ := h.return_sequence_l hZF tree archive columns odd tail limit
  obtain ⟨g₀,union₀⟩ := returned.union_l hZF 0
  obtain ⟨g₁,union₁⟩ := returned.union_l hZF 1
  obtain ⟨g₂,union₂⟩ := returned.union_l hZF 2
  let g : Fin 3 → M.Domain := Fin.cases g₀ (Fin.cases g₁ (fun _ => g₂))
  have unions : ∀ a, Tg_return_union_d hZF ω N F' a (g a) :=
    Fin.cases union₀ (Fin.cases union₁ (Fin.cases union₂ (fun a => Fin.elim0 a)))
  obtain ⟨S',σ,origin⟩ := returnedModel.tree_l hZF hw ho tree.tree.diagram root memS (params 1) rootTree plays
  obtain ⟨Y',q,t,u,cofinal,ft,fu,join⟩ := returned.image_l hZF (v_transitive_l I rank) model origin input unions
  have full := cofinal.branch_l hZF hw space closed
  exact ⟨q,t,u,full.1,full.2,ft,fu,join⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## Neeman 5.15：辅助博弈 II 策略到原博弈 II 策略

原收益集合是三坐标树体第一投影的补集。响应表在原对局开始前统一选择，
有限前缀确定策略；任意服从该策略的对局由同一递归、奇数返回及三图取并
得到第一坐标恰为该对局的原树分支。因此它不属于 I 的收益集合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}
section Transfer
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 统一构造原有限局面空间、偶数时序、无限对局空间、原收益集合及 II 获胜策略。 -/
theorem Tg_game_d.transfer_l {p : Tg_params_d M.Domain} {X₀ F₀ L₀ G₀ J₀ B₀ W₀ O Z g σ a Y T : M.Domain}
    (game : Tg_game_d hZFC p X₀ F₀ L₀ G₀ J₀ B₀ W₀ O Z g)
    (woodin : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I false p.ω X₀ F₀ J₀ B₀ W₀ σ)
    (ha : M.mem a p.A) (space : Fseq_space_d I p.ω Y T)
    (tree : Tree_d T p.S) : ∃ F J B W τ,
      Fseq_space_d I p.ω p.A F ∧
      M.IsFunctionSpace I B p.ω p.A ∧
      (∀ n, M.mem n J ↔ M.mem n p.ω ∧ Gm_even_d I p.ω n) ∧
      (∀ x, M.mem x W ↔ M.mem x B ∧ ¬ Tg_projection_d hZF p.ω Y T p.S x) ∧
      Cg_win_d I false p.ω p.A F J B W τ := by
  have hw := game.setup.omega
  have ho := game.setup.empty
  obtain ⟨θ,X,R,c,C,γ,V,_,rank,model,limit,hwV,hAV,memS,v,u,run,num,image⟩ := game.run_start_l hZFC woodin root win
  let q : Fin 64 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) v u
  obtain ⟨r,code⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) q
  have initial : Tg_run_code_d hZF p.ω c p.e C γ V p.A p.e r := by
    refine ⟨q,code,?_,num⟩
    simpa only [q,Fin.addCases_left,Fin.addCases_right] using run
  obtain ⟨D,E,K,machine⟩ := initial.choice_l hZFC hw ho limit hwV hAV ⟨q,code,image⟩
  obtain ⟨F,J,B,W,finite,bs,turns,payoff⟩ := tg_projection_game_l hZF hw p.A Y T p.S
  obtain ⟨τ,strategy,values⟩ := machine.strategy_l hZF hw ho ha finite
  refine ⟨F,J,B,W,τ,finite,bs,turns,payoff,strategy,?_⟩
  intro x hx follows bad
  have input := fn0_of_function_l (ZF.modelsKP hZF) ((bs x).mp hx)
  have play : Gm_follows_d I false p.ω τ x := fun n hn odd s cut y ny =>
    follows n hn (fun nj => odd ((turns n).mp nj).2) s cut y ny
  obtain ⟨H,sequence,names,played⟩ := machine.sequence_l hZF hw ho ha finite strategy values input play
  obtain ⟨q,t,u,fn,branch,ft,fu,join⟩ := sequence.branch_l hZFC hw ho rank model memS names played input space tree
  exact ((payoff x).mp bad).2 ⟨q,t,u,fn,branch,ft,fu,join⟩

/-! 将 5.15 的完整转移直接包装为投影博弈获胜证书。
该出口只复用同一 `transfer_l` 的五个对象和同一收益谓词，
不重新读取字母表，也不经过 image producer 的识别接口。 -/
theorem Tg_game_d.transfer_projection_win_l
    {p : Tg_params_d M.Domain} {X₀ F₀ L₀ G₀ J₀ B₀ W₀ O Z g σ a Y T : M.Domain}
    (game : Tg_game_d hZFC p X₀ F₀ L₀ G₀ J₀ B₀ W₀ O Z g)
    (woodin : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I false p.ω X₀ F₀ J₀ B₀ W₀ σ)
    (ha : M.mem a p.A) (space : Fseq_space_d I p.ω Y T)
    (tree : Tree_d T p.S) :
    Tg_projection_win_d hZF false p.ω p.A Y T p.S := by
  obtain ⟨F, J, B, W, τ, finite, functions, turns, payoff, win⟩ :=
    game.transfer_l hZFC woodin root win ha space tree
  exact ⟨F, J, B, W, τ, finite, functions, turns, payoff, win⟩

end Transfer
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 扩张反例分支的真实地有限节点

树的第二坐标为原 ω。先按原三元字母表读出两条支撑列，再逐个内部长度
回收三张旧前缀及同一个旧树节点；无限分支本身不要求属于地模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} (hM : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)

theorem tg_join_targets_l {ω A B C P Y f t g q : M.Domain}
    (prod : M.IsCartesianProduct I P B C) (letters : M.IsCartesianProduct I Y A P)
    (fq : M.IsSetFunctionFromTo I q ω Y) (ft : Tg_graph_d I ω t) (fg : Tg_graph_d I ω g)
    (join : Tg_join_d I ω f t g q) : M.IsSetFunctionFromTo I t ω B ∧ M.IsSetFunctionFromTo I g ω C := by
  have vals i (hi : M.mem i ω) : ∃ y z, M.mem y B ∧ M.mem z C ∧ Rd_entry_d i y t ∧ Rd_entry_d i z g := by
    obtain ⟨x, y, z, v, p, _, iy, iz, cv, cp, ip⟩ := join.2 i hi
    obtain ⟨x', _, v', hv, cp'⟩ := (letters p).mp (fq.output_mem_of_pairMember ip)
    obtain ⟨rfl, rfl⟩ := (I).injective cp cp'
    obtain ⟨y', hy, z', hz, cv'⟩ := (prod v).mp hv
    obtain ⟨rfl, rfl⟩ := (I).injective cv cv'
    exact ⟨y, z, hy, hz, iy, iz⟩
  exact ⟨⟨ft.1, ft.2, fun i hi => (vals i hi).elim fun y h => h.elim fun z h => ⟨y, h.1, h.2.2.1⟩⟩,
    fg.1, fg.2, fun i hi => (vals i hi).elim fun y h => h.elim fun z h => ⟨z, h.2.1, h.2.2.2⟩⟩

variable {N : Structure.{v}} (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Tg_projection_d.ground_nodes_l {ω A Γ P Y T S : M.Domain} {f : N.Domain}
    (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω)) (space : Fseq_space_d I ω Y T)
    (prod : M.IsCartesianProduct I P ω Γ) (letters : M.IsCartesianProduct I Y A P)
    (ff : N.IsSetFunctionFromTo J f (e ω) (e A)) (branch : Tg_projection_d hN (e ω) (e Y) (e T) (e S) f) :
    ∃ t g, N.IsSetFunctionFromTo J t (e ω) (e ω) ∧ N.IsSetFunctionFromTo J g (e ω) (e Γ) ∧
      ∀ k, M.mem k ω → ∃ s t₀ g₀, Fn0_d k A s ∧ Fn0_d k ω t₀ ∧ Fn0_d k Γ g₀ ∧ Tg_node_d I k S s t₀ g₀ ∧
        N.IsRestrictionOf J (e s) f (e k) ∧ N.IsRestrictionOf J (e t₀) t (e k) ∧ N.IsRestrictionOf J (e g₀) g (e k) := by
  obtain ⟨q, t, g, fq, tree, ft, fg, join⟩ := branch
  have fq := fn0_function_l (ZF.modelsKP hN) fq
  obtain ⟨ft, fg⟩ := tg_join_targets_l hN (image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he prod)
    (image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he letters) fq ft fg join
  refine ⟨t, g, ft, fg, fun k hk => ?_⟩
  obtain ⟨s, fs, rs⟩ := ground_prefix_l hM hN e hi he hw hw' ff hk
  obtain ⟨t₀, ft₀, rt⟩ := ground_prefix_l hM hN e hi he hw hw' ft hk
  obtain ⟨g₀, fg₀, rg⟩ := ground_prefix_l hM hN e hi he hw hw' fg hk
  obtain ⟨q₀, fq₀, rq⟩ := ground_prefix_l hM hN e hi he hw hw' fq hk
  have fq₀' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fq₀
  have hqS := (image_member_l e hi he).mp (tree (e q₀)
    ((image_member_l e hi he).mpr ((space q₀).mpr ⟨k, hk, fq₀⟩)) ((ds_restrict_iff_l J fq₀' fq.1).mp rq))
  refine ⟨s, t₀, g₀, fn0_of_function_l (ZF.modelsKP hM) fs, fn0_of_function_l (ZF.modelsKP hM) ft₀,
    fn0_of_function_l (ZF.modelsKP hM) fg₀, ⟨⟨fs.1, fs.2.1⟩, ⟨ft₀.1, ft₀.2.1⟩, ⟨fg₀.1, fg₀.2.1⟩,
      q₀, hqS, ⟨fq₀.1, fq₀.2.1⟩, fun i hik => ?_⟩, rs, rt, rg⟩
  obtain ⟨x, _, ix⟩ := fs.2.2 i hik
  obtain ⟨y, _, iy⟩ := ft₀.2.2 i hik
  obtain ⟨z, _, iz⟩ := fg₀.2.2 i hik
  have ix' := ((rs.2 (e i) (e x)).mp ((image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i x s).mp ix)).2
  have iy' := ((rt.2 (e i) (e y)).mp ((image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i y t₀).mp iy)).2
  have iz' := ((rg.2 (e i) (e z)).mp ((image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i z g₀).mp iz)).2
  obtain ⟨x', y', z', v', p', jx, jy, jz, cv', cp', ip⟩ := join.2 (e i)
    ((image_member_l e hi he).mpr (hw.transitive (ZF.modelsKP hM) k hk i hik))
  have eq := ff.1.2 (e i) x' (e x) jx ix'; subst x'
  have eq := ft.1.2 (e i) y' (e y) jy iy'; subst y'
  have eq := fg.1.2 (e i) z' (e z) jz iz'; subst z'
  obtain ⟨v, cv⟩ := (I).total y z
  obtain ⟨p, cp⟩ := (I).total x v
  have eq := (J).unique cv' (image_kpair_l e he cv); subst v'
  have eq := (J).unique cp' (image_kpair_l e he cp); subst p'
  exact ⟨x, y, z, v, p, ix, iy, iz, cv, cp,
    (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i p q₀).mpr
      ((rq.2 (e i) (e p)).mpr ⟨(image_member_l e hi he).mpr hik, ip⟩)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 6.1 泛型 I 方向的严格高度矛盾

反例分支给出真实地有限节点。旧实现关系中的已捕获高度有内部最小元；
原回答严格降低它，原稠密集与 6.6 又捕获同一分支的下一请求，从而矛盾。
整个下降使用原 subtype、exceeds 和固定查询表，目标模型只需 ZF。
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

theorem Tg_setup_d.generic_no_branch_l {p : Tg_params_d M.Domain}
    {X F L G O σ R a Γ P Y S Q : M.Domain} {U : M.Domain → Prop} {g K D T f H τ : N.Domain}
    (setup : Tg_setup_d hZFC p X) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (histories : Tg_histories_d hM p X F L) (owner : Tg_owner_d hM p.ω p.c p.a p.b O)
    (control : Cg_control_d I true p.ω p.e X F L G O σ R) (ha : M.mem a p.A)
    (hw : N.IsOmega (e p.ω)) (c : Cg_scanner_d hN (e p.ω) (e p.A) (e X) (e F) (e L) (e O) (e σ) g K D T)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (ff : Fn0_d (e p.ω) (e p.A) f)
    (values : ∀ s y, Rd_entry_d s y τ → Cg_scan_answer_d hN (e p.ω) (e p.A) (e F) T (e p.e) (e a) s y)
    (follows : Gm_follows_d J true (e p.ω) τ f) (run : Gi_d hN false (e p.ω) (e F) T (e p.e) (e a) f H)
    (space : Fseq_space_d I p.ω Y S) (prod : M.IsCartesianProduct I P p.ω Γ) (letters : M.IsCartesianProduct I Y p.A P)
    (order : ∀ q r, Entry_d M q r Q ↔ M.mem q F ∧ M.mem r F ∧ M.MemberSubset r q)
    (generic : Generic_d M F Q F U)
    (origin : ∀ q, U q → ∀ j y, Rd_entry_d j y q → Rd_entry_d (e j) (e y) g) :
    ¬ Tg_projection_d hN (e p.ω) (e Y) (e S) (e p.S) f := by
  intro bad
  -- 反例分支的每个内部有限前缀都来自地模型；实现高度则始终读取旧实现表。
  obtain ⟨t, G', ft, fg, nodes⟩ := bad.ground_nodes_l hM hN e hi he setup.omega hw space prod letters
    (fn0_function_l (ZF.modelsKP hN) ff)
  have heω := num_mem_l hM.1 setup.omega (show Num_d 0 p.e from setup.empty)
  obtain ⟨one, so, hone⟩ := setup.omega.1.2 p.e heω
  have eq := so.eq hM.1 setup.one; subst one
  obtain ⟨_, _, _, _, _, _, node₁, _⟩ := nodes p.a hone
  have notOrd := node₁.not_ordinal_l hM.1 (KP.exists_pair (ZF.modelsKP hM)) (KP.mem_irrefl_d (ZF.modelsKP hM)) setup.one.predecessor_mem
  obtain ⟨_, Z, rank, treeRank⟩ := setup.low.read_l hM setup.limit.1
  obtain ⟨V, table⟩ := tg_level_table_l hM p X Z
  have empty : ∀ y, ¬ N.mem y (e p.e) := fun y hy => (he p.e y).mp hy |>.elim fun x hx => setup.empty x hx.1
  have emptyCut (v : N.Domain) : N.IsRestrictionOf J (e p.e) v (e p.e) :=
    ⟨(tg_graph_empty_l J empty).1.1, fun i y => iff_of_false (fun ⟨q, _, hq⟩ => empty q hq) (fun h => empty i h.1)⟩
  have enumFn := fn0_function_l (ZF.modelsKP hN) c.enumeration
  have histFn := fn0_function_l (ZF.modelsKP hN) run.1
  have indexFn := fn0_function_l (ZF.modelsKP hN) c.indices
  have hwX := ZF.v_ordinal_mem_l I hM setup.rank setup.above
  have heX := v_transitive_l I setup.rank p.ω hwX p.e heω
  have initial : Tg_tracked_d hN (e p.ω) H K g (e V) t G' (e p.ν) := by
    obtain ⟨n, m, h, h', v, i, en, _, hn, nh, _, _, aux, _, ki, iv, _⟩ :=
      setup.generic_round_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run ((image_member_l e hi he).mpr heω)
    have eq := hi en; subst n
    have saved := aux
    obtain ⟨ℓ, t₀, κ, u, k, l, n, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      data, hκ, f₀, sl, _, _, _, _, _, _, _, _, _, _, branch⟩ := saved
    have te : t₀ = p.e := branch.elim And.left (fun h => (setup.empty ℓ h.2.1).elim); subst t₀
    have ke : k = p.e := hM.1.eq_of_same_members k p.e (fun i => iff_of_false
      (fun hi => (f₀.2.1 i hi).elim fun y hy => hy.2.elim fun z hz => setup.empty z hz.2) (setup.empty i)); subst k
    have key : Tg_level_key_d hM p X Z v p.e p.e p.e p.ν :=
      ⟨(image_member_l e hi he).mp (c.enumeration.bound_l iv).2, heω, heX, fun x hx => (setup.empty x hx).elim,
        Or.inr rfl, ℓ, κ, u, p.a, data, hκ, f₀, setup.one, setup.level_reset_l hZFC aux data⟩
    exact table.track_l hM hN e hi he heω nh ki iv key (emptyCut t) (emptyCut G')
  -- 初始重置给出高度 ν，故已捕获高度非空。对实际原公式取内部最小元 α。
  obtain ⟨α, _, tracked, least⟩ := tg_tracked_min_l hN (image_ord_l hM hN e hi he (v_ordinal_l I rank)) initial
  obtain ⟨n, h, v, k, t₀, g₀, α₀, i, eα, hn, nh, ki, iv, key, rt, rg⟩ := table.read_tracked_l hM hN e he run.1 tracked
  subst α
  obtain ⟨hvX, hk, htX, hgZ, hαν, ℓ, κ, u, l, data, hκ, f₀, sl, level⟩ := key
  obtain ⟨n', m, h', hNext, v', i', en, sm, _, nh', mh, _, aux, ev, ki', iv', _, h₁, b, fh₁, answer, ae, be⟩ :=
    setup.generic_round_l hZFC hN e hi he hd root histories owner control ha hw c surj ff run ((image_member_l e hi he).mpr hn)
  have eq := hi en; subst n'
  have eq := hi (histFn.1.2 (e n) (e h') (e h) nh' nh); subst h'
  have eq := indexFn.1.2 (e h) i' i ki' ki; subst i'
  have eq := hi (enumFn.1.2 i (e v') (e v) iv' iv); subst v'
  obtain ⟨s₀, t₁, g₁, fs₀, _, fg₀, node₀, _, rt₁, rg₁⟩ := nodes k hk
  have eq := hi (rt₁.eq hN.1 rt); subst t₁
  have eq := hi (rg₁.eq hN.1 rg); subst g₁
  -- 原回答的 subtype／exceeds 约束给出同一树、同一标签图上的 β<α。
  obtain ⟨τ₀, B₀, U₀, D₀, w, N₀, q₀, η, A, d, R₀, r, β, pair, hτ, sN, language, hA, model, full,
    first, last, labels, bound, height, below⟩ := setup.level_reply_l hZFC hn fh₁ ae aux answer data f₀ sl level root notOrd
      (fn0_function_l (ZF.modelsKP hM) fg₀).1.1
  obtain ⟨l', sl', hl'⟩ := setup.omega.1.2 k hk
  have hl := sl'.eq hM.1 sl ▸ hl'
  obtain ⟨s₁, t₁, g₁, fs₁, ft₁, fg₁, node, rs₁, rt₁, rg₁⟩ := nodes l hl
  have pull {A k l s t : M.Domain} {f : N.Domain} (fs : Fn0_d k A s) (ft : Fn0_d l A t)
      (rs : N.IsRestrictionOf J (e s) f (e k)) (rt : N.IsRestrictionOf J (e t) f (e l)) (kl : M.MemberSubset k l) : M.IsRestrictionOf I s t k := by
    have fs' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he (fn0_function_l (ZF.modelsKP hM) fs)
    have ft' := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he (fn0_function_l (ZF.modelsKP hM) ft)
    exact (ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hM) fs) (fn0_function_l (ZF.modelsKP hM) ft).1).mpr
      ((image_subset_iff_l e hi he).mp (ds_prefix_mono_l J fs' ft'.1 rs rt ((image_subset_iff_l e hi he).mpr kl)))
  have kl : M.MemberSubset k l := fun x hx => (sl x).mpr (Or.inl hx)
  have cut := pull f₀ ft₁ rt rt₁ kl
  have gcut := pull fg₀ fg₁ rg rg₁ kl
  obtain ⟨z, gz, add⟩ := tg_graph_extend_l hM.1 (KP.exists_pair (ZF.modelsKP hM)) sl
    node₀.2.2.1 node.2.2.1 ((ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hM) fg₀)
      (fn0_function_l (ZF.modelsKP hM) fg₁).1).mp gcut)
  obtain ⟨x, cx, _⟩ := gz
  have extend y : M.mem y g₁ ↔ M.mem y g₀ ∨ y = x := (add y).trans
    ⟨fun h => h.elim Or.inl (fun cy => Or.inr (kpair_unique_l M hM.1 cy cx)),
      fun h => h.elim Or.inl (fun eq => Or.inr (eq.symm ▸ cx))⟩
  have small {A v : M.Domain} (sub : M.MemberSubset A X) (fv : Fn0_d l A v) : M.mem v X := by
    obtain ⟨_, _, _, hv⟩ := ZF.v_finite_function_l hM setup.omega setup.limit setup.rank hwX hl
      ((fn0_function_l (ZF.modelsKP hM) fv).mono_target_l I sub)
    exact hv
  have hsX := small (v_transitive_l I setup.rank p.A setup.letters) fs₁
  have htX' := small (v_transitive_l I setup.rank p.ω hwX) ft₁
  -- 用同一反例分支的下一标签构造地稠密集；6.6 将其捕获成更低的实际请求。
  obtain ⟨B, hB, capture⟩ := setup.capture_threshold_l hZFC hN e hi he (r := N₀) (β := β) (labels := g₁)
    hd root histories owner control ha hw c surj ff values follows run hn sm mh ev be hl fs₁ rs₁
  obtain ⟨q, hq, hit⟩ := setup.generic_meet_l hZFC hd hn data pair f₀ sl sN ft₁ cut language hA model full first last labels
    bound height node extend hτ hsX htX' histories.1 order generic hB
  obtain ⟨n₁, h₁, a₁, i₁, κ₁, C₁, u₁, hn₁, _, nh₁, ki₁, ia₁, target, _⟩ := capture q (generic.proper q hq).1 hit (origin q hq)
  have hβν : M.mem β p.ν := hαν.elim (fun h => (v_ordinal_l I rank).transitive α₀ h β below) (fun eq => eq ▸ below)
  have nextKey : Tg_level_key_d hM p X Z a₁ l t₁ g₁ β :=
    ⟨(image_member_l e hi he).mp (c.enumeration.bound_l ia₁).2, hl, htX', node.labels_rank_l hM rank treeRank,
      Or.inl hβν, n, κ₁, u₁, N₀, target.2.2.1, target.1, ft₁, sN, target.level_l hM⟩
  exact least (e β) ((image_member_l e hi he).mpr below)
    (table.track_l hM hN e hi he hn₁ nh₁ ki₁ ia₁ nextKey rt₁ rg₁)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 6.1 的实际两侧获胜策略

原博弈的 I 收益为三坐标树第一投影的补集。II 分支使用已完成的 5.15；
I 分支构造泛型最小请求策略，并由严格高度矛盾证明每个服从对局属于该补集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

variable (hZFC : M.Models ZFC) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Tg_game_d.generic_transfer_l {p : Tg_params_d M.Domain}
    {X F L G O B W C Z v σ a Γ P Y S Q : M.Domain} {U : M.Domain → Prop} {g : N.Domain}
    (game : Tg_game_d hZFC p X F L G O B W C Z v) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I true p.ω X F O B W σ) (ha : M.mem a p.A) (hw : N.IsOmega (e p.ω))
    (fg : Fn0_d (e p.ω) (e X) g) (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X))
    (space : Fseq_space_d I p.ω Y S) (prod : M.IsCartesianProduct I P p.ω Γ) (letters : M.IsCartesianProduct I Y p.A P)
    (order : ∀ q r, Entry_d M q r Q ↔ M.mem q F ∧ M.mem r F ∧ M.MemberSubset r q)
    (generic : Generic_d M F Q F U)
    (origin : ∀ q, U q → ∀ j y, Rd_entry_d j y q → Rd_entry_d (e j) (e y) g) :
    Tg_projection_win_d hN true (e p.ω) (e p.A) (e Y) (e S) (e p.S) := by
  obtain ⟨F', O', B', W', finite, bs, turns, payoff⟩ := tg_projection_game_l hN hw (e p.A) (e Y) (e S) (e p.S)
  obtain ⟨R, K, D, T, τ, control, scan, strategy, values, runs⟩ :=
    game.generic_strategy_l hZFC hN e hi he hd root win ha hw fg surj finite
  refine ⟨F', O', B', W', τ, finite, bs, turns, payoff, strategy, fun f hf follow => (payoff f).mpr ⟨hf, ?_⟩⟩
  have ff := fn0_of_function_l (ZF.modelsKP hN) ((bs f).mp hf)
  obtain ⟨H, run, _⟩ := runs f ff
  exact game.setup.generic_no_branch_l hZFC hN e hi he hd root game.histories game.owner control ha hw scan surj ff
    (fun s y sy => ((values s y).mp sy).2)
    (fun n hn even s cut y ny => follow n hn ((turns n).mpr ⟨hn, even⟩) s cut y ny)
    run space prod letters order generic origin

/-- 原辅助闭博弈直接给出地 II 或泛型 I 的实际策略，两个收益均为同一树投影。 -/
theorem Tg_game_d.generic_dichotomy_l {p : Tg_params_d M.Domain}
    {X F L G O B W C Z v a Γ P Y S Q : M.Domain} {U : M.Domain → Prop} {g : N.Domain}
    (game : Tg_game_d hZFC p X F L G O B W C Z v) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (ha : M.mem a p.A) (hw : N.IsOmega (e p.ω)) (fg : Fn0_d (e p.ω) (e X) g)
    (surj : N.IsSetSurjectiveOnto J g (e p.ω) (e X)) (space : Fseq_space_d I p.ω Y S) (tree : Tree_d S p.S)
    (prod : M.IsCartesianProduct I P p.ω Γ) (letters : M.IsCartesianProduct I Y p.A P)
    (order : ∀ q r, Entry_d M q r Q ↔ M.mem q F ∧ M.mem r F ∧ M.MemberSubset r q)
    (generic : Generic_d M F Q F U)
    (origin : ∀ q, U q → ∀ j y, Rd_entry_d j y q → Rd_entry_d (e j) (e y) g) :
    Tg_projection_win_d hM false p.ω p.A Y S p.S ∨ Tg_projection_win_d hN true (e p.ω) (e p.A) (e Y) (e S) (e p.S) := by
  obtain ⟨b, σ, _, win⟩ := game.determined_l hZFC
  cases b
  · exact Or.inl (game.transfer_l hZFC hd root win ha space tree)
  · exact Or.inr (game.generic_transfer_l hZFC hN e hi he hd root win ha hw fg surj space prod letters order generic origin)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 6.1：地 II 或原 Col(ω,δ) 中的 I

辅助闭博弈先在地模型决定。I 分支通过实际 δ≅Vδ 双射重编码有限条件，
在原 δ 坍缩的名称扩张中调用最小请求策略；不额外假设枚举公平性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

/-- 原有限初段坍缩的每个实际泛型扩张都具有该投影补集的 I 获胜策略。 -/
def Tg_collapse_win_d (hZF : M.Models ZF) (ω δ A Y T S : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∀ C Q, Fseq_space_d I ω δ C →
    (∀ p q, Entry_d M p q Q ↔ M.mem p C ∧ M.mem q C ∧ M.MemberSubset q p) →
    ∀ (O : Cond_order_d M C Q C) U (generic : Generic_d M C Q C U) b, U b →
      let N := extension_l M hZF C Q C U
      ∃ e : M.Domain → N.Domain, Function.Injective e ∧
        (∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y) ∧
        (∀ a t, Check_d M b a t → Qval_d M C Q C U t (e a)) ∧
        Tg_projection_win_d (preserves_zf_l O hZF generic) true (e ω) (e A) (e Y) (e T) (e S)

theorem tg_collapse_no_root_l (hZF : M.Models ZF) {ω δ A Y T S z a : M.Domain}
    (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z) (ha : M.mem a A)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω Y T) (root : ¬ M.mem z S) :
    Tg_collapse_win_d hZF ω δ A Y T S := by
  intro C Q _ _ O U generic b hb
  let N := extension_l M hZF C Q C U
  have hN : N.Models ZF := preserves_zf_l O hZF generic
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hZF generic hb
  have hw' := image_omega_l (hEN := hN.1) e hi he hZF (internal_foundation_l O hZF generic) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (e ω))
  exact ⟨e, hi, he, hv, tg_projection_no_root_l hN hw'
    (fun y hy => (he z y).mp hy |>.elim fun x hx => hz x hx.1)
    ((image_member_l e hi he).mpr ha) (image_fseq_l hZF hN e hi he hw hw' space)
    (fun hzS => root ((image_member_l e hi he).mp hzS))⟩

variable (hZFC : M.Models ZFC)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)

theorem Tg_game_d.collapse_transfer_l {p : Tg_params_d M.Domain}
    {X F L G J B W O Z v σ a Γ P Y T : M.Domain}
    (game : Tg_game_d hZFC p X F L G J B W O Z v) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I true p.ω X F J B W σ) (ha : M.mem a p.A)
    (space : Fseq_space_d I p.ω Y T) (prod : M.IsCartesianProduct I P p.ω Γ)
    (letters : M.IsCartesianProduct I Y p.A P) : Tg_collapse_win_d hM p.ω p.δ p.A Y T p.S := by
  have inaccessible := hd
  obtain ⟨_, _, _, _, regular, strong, _⟩ := inaccessible
  obtain ⟨ρ, bij⟩ := ZFC.inaccessible_enumeration_l I hZFC game.setup.omega game.setup.above regular strong game.setup.rank
  obtain ⟨r, inverse, _⟩ := ZF.exists_inverseBijectionWithPairs hM I bij
  obtain ⟨R, order, source, _⟩ := subset_order_l M hM F
  intro C Q collapse ord target U generic b hb
  let N := extension_l M hM C Q C U
  have hN : N.Models ZF := preserves_zf_l target hM generic
  obtain ⟨e, hv, he, hi⟩ := check_map_l target hM generic hb
  have hw := image_omega_l (hEN := hN.1) e hi he hM (internal_foundation_l target hM generic) game.setup.omega
    (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (e p.ω))
  obtain ⟨g, fg, onto, graph⟩ := fseq_generic_surjection_l hM game.setup.omega collapse ord generic target
    ⟨p.ω, game.setup.above⟩ hb e hi he hv
  obtain ⟨V, h, gen, fn, surj, origin⟩ := fseq_recode_generic_l hM hN e hi he game.setup.omega game.histories.1
    collapse inverse source order ord generic fg onto
    (fun q hq i y iy => (graph (e i) (e y)).mpr ⟨q, hq, i, y, iy, rfl, rfl⟩)
  exact ⟨e, hi, he, hv, game.generic_transfer_l hZFC hN e hi he hd root win ha hw
    (fn0_of_function_l (ZF.modelsKP hN) fn) surj space prod letters order gen origin⟩

/-- 从原树、非空实落子字母表及一个 Woodin 基数自动闭合 6.1 的二择一。 -/
theorem tg_lemma61_l {ω δ A X Γ P Y T S a : M.Domain} (hw : M.IsOmega ω) (hd : Woodin_d I δ)
    (rank : V_d I δ X) (hA : M.mem A X) (ha : M.mem a A) (space : Fseq_space_d I ω Y T)
    (tree : Tree_d T S) (prod : M.IsCartesianProduct I P ω Γ) (letters : M.IsCartesianProduct I Y A P) :
    Tg_projection_win_d hM false ω A Y T S ∨ Tg_collapse_win_d hM ω δ A Y T S := by
  classical
  have inaccessible := hd
  obtain ⟨w, _, hw₀, hwd, regular, _⟩ := inaccessible
  have eq : w = ω := hM.1.eq_of_same_members w ω fun x => ⟨hw₀.2 ω hw.1 x, hw.2 w hw₀.1 x⟩
  subst w
  obtain ⟨p, F, L, G, J, B, W, O, Z, v, pw, pd, pa, ps, game⟩ :=
    tg_game_l hZFC (S := S) hw regular.isLimitOrdinal hwd rank hA
  subst ω; subst δ; subst A; subst S
  by_cases root : M.mem p.e p.S
  · obtain ⟨b, σ, _, win⟩ := game.determined_l hZFC
    cases b
    · exact Or.inl (game.transfer_l hZFC hd root win ha space tree)
    · exact Or.inr (game.collapse_transfer_l hZFC hd root win ha space prod letters)
  · exact Or.inr (tg_collapse_no_root_l hM game.setup.omega game.setup.empty ha space root)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 6.7：二坐标树投影的地面／坍缩二择一

自动构造 S={(s,t,g) : (s,g)∈T} 并应用 6.1。地面与实际泛型扩张分别证明
两个投影相同；原策略和实数落子完全保留，不把地面投影等同于扩张投影。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}}

/-- positive 指定 I 的收益为投影还是其补；b 指定实际获胜玩家。 -/
def Tp_win_d (hZF : M.Models ZF) (b positive : Bool) (ω A Y F T : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ H J B W σ, Fseq_space_d I ω A H ∧ M.IsFunctionSpace I B ω A ∧
    (∀ n, M.mem n J ↔ M.mem n ω ∧ Gm_even_d I ω n) ∧
    (∀ x, M.mem x W ↔ M.mem x B ∧ (if positive then Tp_projection_d I ω A Y F T x else ¬ Tp_projection_d I ω A Y F T x)) ∧
    Cg_win_d I b ω A H J B W σ

def Tp_collapse_win_d (hZF : M.Models ZF) (b positive : Bool) (ω δ A Y F T : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∀ C Q, Fseq_space_d I ω δ C →
    (∀ p q, Entry_d M p q Q ↔ M.mem p C ∧ M.mem q C ∧ M.MemberSubset q p) →
    ∀ (O : Cond_order_d M C Q C) U (generic : Generic_d M C Q C U) p, U p →
      let N := extension_l M hZF C Q C U
      ∃ e : M.Domain → N.Domain, Function.Injective e ∧
        (∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y) ∧
        (∀ a t, Check_d M p a t → Qval_d M C Q C U t (e a)) ∧
        Tp_win_d (preserves_zf_l O hZF generic) b positive (e ω) (e A) (e Y) (e F) (e T)

section Transfer
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_projection_win_d.vacuous_l {ω A Γ P Y Z F G T S d : M.Domain} {b : Bool}
    (hw : M.IsOmega ω) (prod : M.IsCartesianProduct I P ω Γ) (letters : M.IsCartesianProduct I Y A P)
    (pair : M.IsCartesianProduct I Z A Γ) (space : Fseq_space_d I ω Y F) (target : Fseq_space_d I ω Z G)
    (drop : Tv_drop_d I Y Z d) (pull : Tr_pull_d I d F T S) (win : Tg_projection_win_d hZF b ω A Y F S) :
    Tp_win_d hZF b false ω A Z G T := by
  obtain ⟨H, J, B, W, σ, finite, bs, turns, payoff, win⟩ := win
  exact ⟨H, J, B, W, σ, finite, bs, turns, fun x => (payoff x).trans (and_congr_right fun hx =>
    not_congr (tv_projection_l hZF hw prod letters pair space target drop pull ((bs x).mp hx))), win⟩

end Transfer
section Image
variable {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Tv_drop_d.image_l {Y Z d : M.Domain} (drop : Tv_drop_d I Y Z d) : Tv_drop_d J (e Y) (e Z) (e d) := by
  have value {p q} (h : Tv_drop_value_d I p q) : Tv_drop_value_d J (e p) (e q) := by
    obtain ⟨a, b, c, v, ap, bc, ac⟩ := h
    exact ⟨e a, e b, e c, e v, image_kpair_l e he ap, image_kpair_l e he bc, image_kpair_l e he ac⟩
  refine ⟨image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he drop.1, fun p q => ?_⟩
  constructor
  · intro pq
    obtain ⟨a, b, ab, rfl, rfl⟩ := (image_entries_l e he drop.1.1.1 p q).mp pq
    exact ⟨(image_member_l e hi he).mpr ((drop.2 a b).mp ab).1, value ((drop.2 a b).mp ab).2⟩
  · rintro ⟨hp, pq⟩
    obtain ⟨a, ha, rfl⟩ := (he Y p).mp hp
    obtain ⟨b, _, ab⟩ := drop.1.2.2 a ha
    have eq := pq.unique_l J (value ((drop.2 a b).mp ab).2); subst q
    exact (image_entries_l e he drop.1.1.1 (e a) (e b)).mpr ⟨a, b, ab, rfl, rfl⟩

end Image

variable (hZFC : M.Models ZFC)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)

/-- 6.7：原二坐标树的补投影博弈，地面 II 或每个原坍缩扩张中的 I 获胜。 -/
theorem tg_corollary67_l {ω δ A X Γ Y F T a : M.Domain} (hw : M.IsOmega ω) (hd : Woodin_d I δ)
    (rank : V_d I δ X) (hA : M.mem A X) (ha : M.mem a A) (pair : M.IsCartesianProduct I Y A Γ)
    (space : Fseq_space_d I ω Y F) (tree : Tree_d F T) :
    Tp_win_d hM false false ω A Y F T ∨ Tp_collapse_win_d hM true false ω δ A Y F T := by
  obtain ⟨P, prod⟩ := ZF.exists_cartesianProduct hM I ω Γ
  obtain ⟨Z, letters⟩ := ZF.exists_cartesianProduct hM I A P
  obtain ⟨G, finite⟩ := ZF.fseq_space_exists_l I hM hw Z
  obtain ⟨d, drop⟩ := tv_drop_l I hM prod letters pair
  obtain ⟨S, pull⟩ := tr_pull_exists_l I hM d G T
  have tree' := pull.tree_l I hM drop.1 finite space tree
  rcases tg_lemma61_l hZFC hw hd rank hA ha finite tree' prod letters with win | win
  · exact Or.inl (win.vacuous_l hM hw prod letters pair finite space drop pull)
  · refine Or.inr (fun C Q collapse order O U generic b hb => ?_)
    -- 旧逆像树的像仍是扩张中的逆像树；在扩张内对全部新分支应用同一个投影等价。
    let N := extension_l M hM C Q C U
    have hN : N.Models ZF := preserves_zf_l O hM generic
    obtain ⟨e, hi, he, hv, winning⟩ := win C Q collapse order O U generic b hb
    have hw' := image_omega_l (hEN := hN.1) e hi he hM (internal_foundation_l O hM generic) hw
      (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (e ω))
    exact ⟨e, hi, he, hv, winning.vacuous_l hN hw'
      (image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he prod)
      (image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he letters)
      (image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he pair)
      (image_fseq_l hM hN e hi he hw hw' finite) (image_fseq_l hM hN e hi he hw hw' space)
      (drop.image_l hM hN e hi he) (image_tree_pullback_l hM hN e hi he drop.1 finite pull)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 6.10：换手后的原投影博弈

给二坐标树加任意首项后调用 6.7。首手来自旧 I 策略自身或固定字母；
移位策略和投影的对应把地 II／泛型 I 分别变为原投影的地 I／泛型 II。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

section Transfer
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tp_win_d.shift_l {b : Bool} {ω A Γ Y F T S z a : M.Domain}
    (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z) (ha : M.mem a A)
    (pair : M.IsCartesianProduct I Y A Γ) (space : Fseq_space_d I ω Y F) (subT : M.MemberSubset T F)
    (shift : Tr_shift_d I z F T S) (winning : Tp_win_d hZF b false ω A Y F S) : Tp_win_d hZF (!b) true ω A Y F T := by
  obtain ⟨H, J, B, W, σ, finite, bs, turns, oldPayoff, win⟩ := winning
  have fσ := fn0_function_l (ZF.modelsKP hZF) win.1
  obtain ⟨z', hz', hzω⟩ := hw.1.1
  have eq := hZF.1.eq_of_same_members z' z fun x => iff_of_false (hz' x) (hz x); subst z'
  have hzH := (finite z).mpr ⟨z, hzω, ds_empty_fun_l I hz⟩
  -- 旧 I 的首手必须服从旧策略；旧 II 的对手首手可以固定为任意给定字母。
  have start : ∃ a₀, M.mem a₀ A ∧ (b = true → Rd_entry_d z a₀ σ) := by
    cases b
    · exact ⟨a, ha, fun h => by cases h⟩
    · obtain ⟨a₀, ha₀, za⟩ := fσ.2.2 z hzH
      exact ⟨a₀, ha₀, fun _ => za⟩
  obtain ⟨a₀, ha₀, first⟩ := start
  obtain ⟨τ, fτ, values⟩ := gm_shift_l I hZF hw hz ha₀ finite fσ
  let ρ : Env M 5 := ⟨fun i => [ω, A, Y, F, T].get i, fun _ => ω⟩
  let φ : UnarySchema 5 := { body := tp_projection_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) .newest }
  obtain ⟨V, vs⟩ := ZF.separation_exists_d hZF φ ρ B
  have payoff x : M.mem x V ↔ M.mem x B ∧ Tp_projection_d I ω A Y F T x :=
    (vs x).trans (and_congr_right fun _ => tp_projection_sat_l I hZF.1 ..)
  have follows (c : Bool) (r f : M.Domain) : Cg_follows_d I c ω J r f ↔ Gm_follows_d I c ω r f := by
    constructor
    · intro h n hn turn s cut v nv
      apply h n hn ?_ s cut v nv
      cases c
      · exact fun nj => turn ((turns n).mp nj).2
      · exact (turns n).mpr ⟨hn, turn⟩
    · intro h n hn turn s cut v nv
      apply h n hn ?_ s cut v nv
      cases c
      · exact fun even => turn ((turns n).mpr ⟨hn, even⟩)
      · exact ((turns n).mp turn).2
  refine ⟨H, J, B, V, τ, finite, bs, turns, payoff, fn0_of_function_l (ZF.modelsKP hZF) fτ, fun f hf follow => ?_⟩
  have ff := (bs f).mp hf
  -- 对任意新服从对局重建旧服从对局，再在同一模型内使用投影等价。
  obtain ⟨g, fg, cons⟩ := cons_omega_l I hZF hw hz ha₀ ff
  have follow' := gm_shift_follows_l I hZF hw hz ha₀ values first ff fg cons ((follows (!b) τ f).mp follow)
  have hg := (bs g).mpr fg
  have result := win.2 g hg ((follows b σ g).mpr follow')
  have proj := tp_shift_projection_l hZF hw hz ha₀ pair space subT shift ff fg cons
  cases b
  · exact (payoff f).mpr ⟨hf, proj.mp (Classical.byContradiction (fun no => result ((oldPayoff g).mpr ⟨hg, no⟩)))⟩
  · intro yes
    exact ((oldPayoff g).mp result).2 (proj.mpr ((payoff f).mp yes).2)

end Transfer

variable (hZFC : M.Models ZFC)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)

/-- 6.10：原树投影博弈在地面由 I 获胜，或在每个原坍缩扩张中由 II 获胜。 -/
theorem tg_corollary610_l {ω δ A X Γ Y F T a : M.Domain} (hw : M.IsOmega ω) (hd : Woodin_d I δ)
    (rank : V_d I δ X) (hA : M.mem A X) (ha : M.mem a A) (pair : M.IsCartesianProduct I Y A Γ)
    (space : Fseq_space_d I ω Y F) (tree : Tree_d F T) :
    Tp_win_d hM true true ω A Y F T ∨ Tp_collapse_win_d hM false true ω δ A Y F T := by
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hM)
  obtain ⟨S, shift⟩ := tr_shift_exists_l I hM z F T
  have tree' := shift.tree_l I hM hw hz space tree
  rcases tg_corollary67_l hZFC hw hd rank hA ha pair space tree' with win | win
  · exact Or.inl (win.shift_l hM hw hz ha pair space tree.1 shift)
  · refine Or.inr (fun C Q collapse order O U generic b hb => ?_)
    let N := extension_l M hM C Q C U
    have hN : N.Models ZF := preserves_zf_l O hM generic
    obtain ⟨e, hi, he, hv, winning⟩ := win C Q collapse order O U generic b hb
    have hw' := image_omega_l (hEN := hN.1) e hi he hM (internal_foundation_l O hM generic) hw
      (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (e ω))
    have hz' y (hy : N.mem y (e z)) : False := (he z y).mp hy |>.elim fun x hx => hz x hx.1
    -- 移位树的规范像仍满足原图方程，目标证明覆盖扩张中的全部新对局。
    exact ⟨e, hi, he, hv, winning.shift_l hN hw' hz' ((image_member_l e hi he).mpr ha)
      (image_product_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he pair)
      (image_fseq_l hM hN e hi he hw hw' space) ((image_subset_iff_l e hi he).mpr tree.1)
      (image_tree_shift_l hM hN e hi he hw hw' hz space tree.1 shift)⟩

end YesMetaZFC.SetTheory.LargeCardinal
