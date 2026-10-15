import YesMetaZFC.SetTheory.Descriptive.GameLegalStep

/-! # 原获胜策略的有限历史控制集合

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
