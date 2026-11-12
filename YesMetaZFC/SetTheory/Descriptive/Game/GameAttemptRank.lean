import YesMetaZFC.SetTheory.Descriptive.Game.ClosedDeterminacy
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeWellFounded

/-! # 获胜策略在合法有限历史上的实际后继

有限追加保持任一方原策略的服从关系及续局获胜性。若获胜策略在合法位置
首次违规，实际无限延拓会被收益判给对手，与该续局获胜性矛盾。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 一项追加的任意严格有限前缀已经包含于旧历史。 -/
theorem ds_before_end_l {ω X F n s t a q : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n X)
    (endt : Fseq_end_d I ω t s a) (hq : M.mem q F) (qt : M.MemberSubset q t)
    (proper : ¬ M.MemberSubset t q) : M.MemberSubset q s := by
  obtain ⟨m, n', d⟩ := endt
  have eq := d.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
  subst n'
  obtain ⟨k, hk, fq⟩ := (space q).mp hq
  have rq := (ds_restrict_iff_l I fq d.source.2.2.1).mpr qt
  have rs := d.prefix_restriction
  rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare k hk n hn with eq | lt | gt
  · exact ds_prefix_mono_l I fq fs.1 rq rs (fun x hx => (eq x).mp hx)
  · exact ds_prefix_mono_l I fq fs.1 rq rs ((hω.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive k lt)
  · have sq := ds_prefix_mono_l I fs fq.1 rs rq ((hω.members_areOrdinals (ZF.modelsKP hZF) k hk).transitive n gt)
    have last := (rq.2 n a).mpr ⟨gt, d.last_value⟩
    exact (proper (ds_append_sub_l I hZF.1 fs ⟨m, n, d⟩ sq last)).elim

theorem Cg_legal_d.extend_l {ω X F L G n s t a : M.Domain} (legal : Cg_legal_d (M := M) F L G)
    (hω : M.IsOmega ω) (space : Fseq_space_d I ω X F) (hn : M.mem n ω)
    (fs : M.IsSetFunctionFromTo I s n X) (hs : M.mem s G)
    (endt : Fseq_end_d I ω t s a) (ht : M.mem t F) (check : M.mem t L) : M.mem t G := by
  classical
  refine (legal t).mpr ⟨ht, fun q hq qt => ?_⟩
  by_cases tq : M.MemberSubset t q
  · have eq := hZF.1.eq_of_same_members q t (fun x => ⟨qt x, tq x⟩)
    exact eq.symm ▸ check
  · exact ((legal s).mp hs).2 q hq (ds_before_end_l hZF hω space hn fs endt hq qt tq)

theorem Cg_follows_d.extend_l {ι : Bool} {ω X J σ n s t a : M.Domain} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n X)
    (follows : Cg_follows_d I ι ω J σ s) (endt : Fseq_end_d I ω t s a)
    (move : (if ι then M.mem n J else ¬ M.mem n J) → Rd_entry_d s a σ) : Cg_follows_d I ι ω J σ t := by
  obtain ⟨m, n', d⟩ := endt
  have eq := d.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
  subst n'
  intro i hi turn h hr v hv
  have him := (d.source.2.2.2 i).mpr ⟨v, hv⟩
  rcases (d.length_successor i).mp him with hin | eq
  · exact follows i hi turn h (d.prefix_restriction.trans hr ((hω.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive i hin))
      v ((d.prefix_restriction.2 i v).mpr ⟨hin, hv⟩)
  · have eq := hZF.1.eq_of_same_members i n eq
    subst i
    have eh := hr.eq hZF.1 d.prefix_restriction
    have ev := d.source.2.2.1.2 n v a hv d.last_value
    exact eh.symm ▸ ev.symm ▸ move turn

/-- 原策略负责的时刻使用其原值，其余时刻允许任意对手落子。 -/
theorem Cg_tail_win_d.extend_l {ι : Bool} {ω X F J B W σ n s t a : M.Domain}
    (win : Cg_tail_win_d I ι ω X F J B W s σ) (hω : M.IsOmega ω)
    (runs : M.IsFunctionSpace I B ω X) (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n X)
    (endt : Fseq_end_d I ω t s a) (move : (if ι then M.mem n J else ¬ M.mem n J) → Rd_entry_d s a σ) :
    Cg_tail_win_d I ι ω X F J B W t σ := by
  obtain ⟨m, n', d⟩ := endt
  have eq := d.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
  subst n'
  have st := (ds_restrict_iff_l I fs d.source.2.2.1).mp d.prefix_restriction
  refine ⟨win.1, fun f hf tf follows => win.2 f hf (fun p hp => tf p (st p hp)) ?_⟩
  have ff := (runs f).mp hf
  have sf := (ds_restrict_iff_l I fs ff.1).mpr (fun p hp => tf p (st p hp))
  have last : Rd_entry_d n a f := d.last_value.elim fun p hp => ⟨p, hp.1, tf p hp.2⟩
  intro i hi turn h hr sh v hv
  rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare i hi n hn with eq | lt | gt
  · have eq := hZF.1.eq_of_same_members i n eq
    subst i
    have eh := hr.eq hZF.1 sf
    have ev := ff.1.2 n v a hv last
    exact eh.symm ▸ ev.symm ▸ move turn
  · obtain ⟨x, _, hsx⟩ := fs.2.2 i lt
    have hhx : Rd_entry_d i x h := hsx.elim fun p hp => ⟨p, hp.1, sh p hp.2⟩
    exact (KP.mem_irrefl_d (ZF.modelsKP hZF) i ((hr.2 i x).mp hhx).1).elim
  · have th : M.MemberSubset t h := ds_append_sub_l I hZF.1 fs ⟨m, n, d⟩ sh ((hr.2 n a).mpr ⟨gt, last⟩)
    exact follows i hi turn h hr th v hv

/-- 沿原策略到达的有限位置，其后继续使用同一策略仍获胜。 -/
theorem Cg_win_d.tail_l {ι : Bool} {ω X F J B W σ n s : M.Domain}
    (win : Cg_win_d I ι ω X F J B W σ) (hω : M.IsOmega ω)
    (runs : M.IsFunctionSpace I B ω X) (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n X)
    (played : Cg_follows_d I ι ω J σ s) : Cg_tail_win_d I ι ω X F J B W s σ := by
  classical
  refine ⟨win.1, fun f hf sf follows => win.2 f hf ?_⟩
  have ff := (runs f).mp hf
  have sr := (ds_restrict_iff_l I fs ff.1).mpr sf
  intro i hi turn h hr v hv
  rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare i hi n hn with eq | lt | gt
  · have ni : M.MemberSubset n i := fun x hx => (eq x).mpr hx
    exact follows i hi turn h hr (ds_prefix_mono_l I fs (hr.isSetFunction ff.1) sr hr ni) v hv
  · exact played i hi turn h (sr.trans hr ((hω.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive i lt))
      v ((sr.2 i v).mpr ⟨lt, hv⟩)
  · exact follows i hi turn h hr
      (ds_prefix_mono_l I fs (hr.isSetFunction ff.1) sr hr ((hω.members_areOrdinals (ZF.modelsKP hZF) i hi).transitive n gt)) v hv

/-- 获胜策略不会从合法位置作出首次违规的走法。 -/
theorem Cg_tail_win_d.legal_step_l {ι : Bool} {ω X F L G J B W σ n s t a : M.Domain}
    (win : Cg_tail_win_d I ι ω X F J B W s σ) (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (runs : M.IsFunctionSpace I B ω X)
    (legal : Cg_legal_d (M := M) F L G) (payoff : Cg_payoff_d ω X F L J B W)
    (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n X) (hs : M.mem s G)
    (ha : M.mem a X) (turn : if ι then M.mem n J else ¬ M.mem n J) (value : Rd_entry_d s a σ)
    (endt : Fseq_end_d I ω t s a) (ht : M.mem t F) : M.mem t G := by
  apply legal.extend_l hZF hω space hn fs hs endt ht
  apply Classical.byContradiction
  intro bad
  have next := win.extend_l hZF hω runs hn fs endt (fun _ => value)
  obtain ⟨m, hm, ft⟩ := (space t).mp ht
  obtain ⟨f, ff, tf, follows⟩ := cg_tail_play_l hZF (ι := ι) hω space win.1 hm ft ha
  have winf := next.2 f ((runs f).mpr ff) tf follows
  obtain ⟨m', n', d⟩ := endt
  have en := d.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
  have em := d.source.2.2.2.eq hZF.1 ft.2.1
  subst n' m'
  have first : Cg_first_d ω X F L n t :=
    ⟨m, hm, fn0_of_function_l (ZF.modelsKP hZF) ft, d.length_successor, bad,
      fun q hq qt tq => ((legal s).mp hs).2 q hq (ds_before_end_l hZF hω space hn fs ⟨m, n, d⟩ hq qt tq)⟩
  cases ι with
  | false => exact winf (payoff.ii_first_l (ZF.modelsKP hZF) (hω.isOrdinal (ZF.modelsKP hZF)) ff.1 ((runs f).mpr ff) ht tf first turn)
  | true => exact ((payoff.read_l ((runs f).mpr ff)).mpr ⟨t, n, ht, tf, turn, first⟩) winf

end YesMetaZFC.SetTheory.Descriptive

/-! ## 原获胜策略的有限历史控制集合

R 由原策略和实际合法历史树分离得到。对手作出合法回答，或本方使用原策略值，
都会得到 R 中的下一位置。整项性质是一条原一阶公式，可随同参数反射和搬运。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Cg_control_d (b : Bool) (ω e X F L G J σ R : M.Domain) : Prop where
  space : Fseq_space_d I ω X F
  strategy : Fn0_d F X σ
  legal : Cg_legal_d (M := M) F L G
  root : M.mem e R
  positions : ∀ h, M.mem h R ↔ M.mem h G ∧ Cg_follows_d I b ω J σ h
  step : ∀ n h a t, M.mem n ω → M.mem h R → M.mem a X → Fn0_d n X h →
    Fseq_end_d I ω t h a → (((if b then ¬ M.mem n J else M.mem n J) ∧ M.mem t L) ∨
      ((if b then M.mem n J else ¬ M.mem n J) ∧ Rd_entry_d h a σ)) → M.mem t R

def cg_control_m (b : Bool) {d} (ω e X F L G J σ R : Term d) : Formula 1 d :=
  let own {d} (n J : Term d) := if b then (.mem n J : Formula 1 d) else .neg (.mem n J)
  let opp {d} (n J : Term d) := if b then (.neg (.mem n J) : Formula 1 d) else .mem n J
  set[d] ⟪
  ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜F⌝ₛ) ∧ ⌜fn0_m⌝ₚ(⌜F⌝ₛ, ⌜X⌝ₛ, ⌜σ⌝ₛ) ∧
  ⌜cg_legal_m⌝ₚ(⌜F⌝ₛ, ⌜L⌝ₛ, ⌜G⌝ₛ) ∧ ⌜e⌝ₛ ∈ ⌜R⌝ₛ ∧
  (∀ h, h ∈ ⌜R⌝ₛ ↔ h ∈ ⌜G⌝ₛ ∧ ⌜(cg_follows_m b)⌝ₚ(⌜ω⌝ₛ, ⌜J⌝ₛ, ⌜σ⌝ₛ, h)) ∧
  (∀ n ∈ ⌜ω⌝ₛ, ∀ h ∈ ⌜R⌝ₛ, ∀ a ∈ ⌜X⌝ₛ, ∀ t,
    ⌜fn0_m⌝ₚ(n, ⌜X⌝ₛ, h) → ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, t, h, a) →
    ((⌜opp⌝ₚ(n, ⌜J⌝ₛ) ∧ t ∈ ⌜L⌝ₛ) ∨ (⌜own⌝ₚ(n, ⌜J⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(h, a, ⌜σ⌝ₛ))) → t ∈ ⌜R⌝ₛ)⟫

@[simp] theorem cg_control_closed_l (b : Bool) {d} (ω e X F L G J σ R : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (hX : X.freeSupport = [])
    (hF : F.freeSupport = []) (hL : L.freeSupport = []) (hG : G.freeSupport = [])
    (hJ : J.freeSupport = []) (hs : σ.freeSupport = []) (hR : R.freeSupport = []) :
    (cg_control_m b ω e X F L G J σ R).FreeClosed := by
  cases b <;> simp -implicitDefEqProofs [cg_control_m, Definitional.Formula.FreeClosed, hw, he, hX, hF, hL, hG, hJ, hs, hR]

theorem cg_control_sat_l (hE : Extensional M) (b : Bool) {d} (ρ : Env M d) (ω e X F L G J σ R : Term d) :
    Formula.satisfies ρ (cg_control_m b ω e X F L G J σ R) ↔ Cg_control_d I b
      (ω.eval ρ) (e.eval ρ) (X.eval ρ) (F.eval ρ) (L.eval ρ) (G.eval ρ) (J.eval ρ) (σ.eval ρ) (R.eval ρ) := by
  cases b <;> simp only [cg_control_m, Bool.false_eq_true, ↓reduceIte, Formula.satisfies_conj_iff, fseq_space_sat_l I hE, fn0_sat_l hE,
    cg_legal_sat_l, Formula.satisfies_mem_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    cg_follows_sat_l I hE, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    fseq_end_sat_l I hE, Formula.satisfies_disj_iff, Formula.satisfies_neg_iff,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken] <;>
  exact ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, fun n h a t hn hh ha => f n hn h hh a ha t⟩,
    fun h => ⟨h.space, h.strategy, h.legal, h.root, h.positions,
      fun n hn s hs a ha t => h.step n s a t hn hs ha⟩⟩

theorem cg_control_l (hZF : M.Models ZF) {b : Bool} {ω e X F L G J B W σ : M.Domain}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω X F)
    (legal : Cg_legal_d (M := M) F L G) (root : M.mem e G)
    (runs : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) B ω X) (payoff : Cg_payoff_d ω X F L J B W)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP hZF)) b ω X F J B W σ) :
    ∃ R, Cg_control_d (kp_pair_l (ZF.modelsKP hZF)) b ω e X F L G J σ R := by
  let K := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 3 := ⟨Fin.cases σ (Fin.cases J (fun _ => ω)), fun _ => ω⟩
  let φ : UnarySchema 3 := { body := cg_follows_m b (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨R, sep⟩ := ZF.separation_exists_d hZF φ ρ G
  have positions h : M.mem h R ↔ M.mem h G ∧ Cg_follows_d K b ω J σ h :=
    (sep h).trans (and_congr Iff.rfl (cg_follows_sat_l K hZF.1 ..))
  refine ⟨R, space, win.1, legal, (positions e).mpr ⟨root, ?_⟩, positions, ?_⟩
  · intro i _ _ h _ v hv
    exact (hv.elim fun p hp => he p hp.2).elim
  · intro n h a t hn hh ha fh endt rule
    obtain ⟨hg, follows⟩ := (positions h).mp hh
    have fh := fn0_function_l (ZF.modelsKP hZF) fh
    obtain ⟨m, t', hm, ft, endt'⟩ := ZF.fseq_end_exists_l K hZF hω hn fh ha
    have eq := fseq_end_rebuild_l K hZF.1 endt' endt
    subst t'
    have ht := (space t).mpr ⟨m, hm, ft⟩
    have move : (if b then M.mem n J else ¬ M.mem n J) → Rd_entry_d h a σ := by
      intro own
      rcases rule with ⟨opp, _⟩ | ⟨_, value⟩
      · cases b <;> exact (by simp_all)
      · exact value
    have next := follows.extend_l hZF hω hn fh endt move
    refine (positions t).mpr ⟨?_, next⟩
    rcases rule with ⟨_, check⟩ | ⟨turn, value⟩
    · exact legal.extend_l hZF hω space hn fh hg endt ht check
    · exact (win.tail_l hZF hω runs hn fh follows).legal_step_l hZF hω space runs legal payoff hn fh hg ha turn value endt ht

end YesMetaZFC.SetTheory.Descriptive

/-! ## II 获胜策略的合法尝试树有实际序数秩

控制树的一条无限枝同时是合法对局和服从原 II 策略的对局，矛盾。
ZF＋DC 将这一无枝性转为内部良基性，再由原良基递归构造秩函数。
最终证书只检查实际函数图与有界子边，可在后继传递模型中读取。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Cg_control_d.tree_l {b : Bool} {ω e X F L G J σ R : M.Domain} (hω : M.IsOmega ω)
    (control : Cg_control_d I b ω e X F L G J σ R) : Tree_d F R := by
  refine ⟨fun s hs => ((control.legal s).mp ((control.positions s).mp hs).1).1, ?_⟩
  intro s hs t ht sub
  obtain ⟨legal, follows⟩ := (control.positions s).mp hs
  obtain ⟨n, hn, ft⟩ := (control.space t).mp ht
  obtain ⟨_, _, fs⟩ := (control.space s).mp ((control.legal s).mp legal).1
  have res := (ds_restrict_iff_l I ft fs.1).mpr sub
  refine (control.positions t).mpr ⟨control.legal.prefix_l legal ht sub, ?_⟩
  intro i hi turn h rh v hv
  have hin := ft.input_mem_of_pairMember hv
  have rs : M.IsRestrictionOf I h s i := ⟨rh.1, fun k a => (rh.2 k a).trans
    ⟨fun ⟨hk, ht⟩ => ⟨hk, (res.2 k a).mp ht |>.2⟩,
      fun ⟨hk, hs⟩ => ⟨hk, (res.2 k a).mpr ⟨(hω.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive i hin k hk, hs⟩⟩⟩⟩
  exact follows i hi turn h rs v
    (hv.elim fun p hp => ⟨p, hp.1, sub p hp.2⟩)

theorem Cg_control_d.no_branch_l {ω e X F L G J B W σ R f : M.Domain} (hω : M.IsOmega ω)
    (control : Cg_control_d I false ω e X F L G J σ R) (runs : M.IsFunctionSpace I B ω X)
    (payoff : Cg_payoff_d (M := M) ω X F L J B W) (win : Cg_win_d I false ω X F J B W σ)
    (ff : M.IsSetFunctionFromTo I f ω X) : ¬ Branch_d F R f := by
  intro branch
  have hf := (runs f).mpr ff
  have legal := payoff.all_legal_l hf (fun s hs sf =>
    control.legal.current_l ((control.positions s).mp (branch s hs sf)).1)
  apply win.2 f hf ?_ legal
  intro i hi turn h rh v hv
  obtain ⟨j, succ, hj⟩ := hω.1.2 i hi
  obtain ⟨t, ft, rt, _⟩ := ds_prefix_l I hZF hω ff hj
  have tf := (ds_restrict_iff_l I ft ff.1).mp rt
  have ht := branch t ((control.space t).mpr ⟨j, hj, ft⟩) tf
  have fh := rh.isSetFunctionFromTo ff (hω.transitive (ZF.modelsKP hZF) i hi)
  have ht' := ds_prefix_mono_l I fh ft.1 rh rt (fun x hx => (succ x).mpr (Or.inl hx))
  exact ((control.positions t).mp ht).2 i hi turn h ((ds_restrict_iff_l I fh ft.1).mpr ht')
    v ((rt.2 i v).mpr ⟨succ.predecessor_mem, hv⟩)

theorem Cg_control_d.rank_l {ω e X F L G J B W σ R : M.Domain} (hω : M.IsOmega ω) (dc : Dc_d I ω)
    (control : Cg_control_d I false ω e X F L G J σ R) (runs : M.IsFunctionSpace I B ω X)
    (payoff : Cg_payoff_d (M := M) ω X F L J B W) (win : Cg_win_d I false ω X F J B W σ) :
    ∃ α H, Cg_rank_d ω X R α H := by
  exact tree_rank_l hZF hω dc control.space (control.tree_l hZF hω)
    (fun _ ff => control.no_branch_l hZF hω runs payoff win ff)

end YesMetaZFC.SetTheory.Descriptive
