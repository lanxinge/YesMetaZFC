import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControl
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameResetControl
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlAnswer
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlDigit
import YesMetaZFC.SetTheory.Descriptive.GameAttemptRank

/-! # 原策略自动产生下一辅助走法

对全部内部有限历史，原策略的实际值仍在控制集合中，并满足原辅助走法规则。
此存在性质也进入控制记录，故反射层可直接取得实际下一走法。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

theorem Tg_rules_d.aux_l (hZF : M.Models ZF) {p : Tg_params_d M.Domain} {X F L G J σ R i n h : M.Domain}
    (rules : Tg_rules_d hZF p X F L J) (control : Cg_control_d (kp_pair_l (ZF.modelsKP hZF)) p.ω p.e X F L G J σ R)
    (hi : M.mem i p.ω) (hn : M.mem n p.ω) (hh : M.mem h R) (fh : Fn0_d i X h)
    (div : M.IsOrdinalDivision (kp_pair_l (ZF.modelsKP hZF)) i p.c n p.e) :
    ∃ a t j, M.mem a X ∧ Rd_entry_d h a σ ∧ Fseq_end_d (kp_pair_l (ZF.modelsKP hZF)) p.ω t h a ∧
      M.mem j p.ω ∧ M.SuccessorOf j i ∧ Fn0_d j X t ∧ M.mem t R ∧
      M.IsOrdinalDivision (kp_pair_l (ZF.modelsKP hZF)) j p.c n p.a ∧ Tg_aux_d hZF p n h a ∧
      Tg_event_d (kp_pair_l (ZF.modelsKP hZF)) p.c n p.e t a := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨hc, _⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three hi
  have oc := rules.omega.members_areOrdinals hZF p.c hc
  have ne₁ : p.e ≠ p.a := fun eq => rules.empty p.e (eq.symm ▸ rules.one.predecessor_mem)
  have ne₂ : p.e ≠ p.b := fun eq => rules.empty p.a (eq.symm ▸ rules.two.predecessor_mem)
  have turn : ¬ M.mem i J := fun h => ((rules.owner.read_l hZF (rules.omega.isOrdinal hZF)
    oc ⟨p.b, rules.three.predecessor_mem⟩ hi hn div).mp h).elim ne₁ (fun h => ne₂ h.1)
  have hG := ((control.positions h).mp hh).1
  obtain ⟨a, ha, value⟩ := control.strategy.2.1 h ((control.legal h).mp hG).1
  obtain ⟨j, t, hj, ft, endt⟩ := ZF.fseq_end_exists_l I hZF rules.omega hi (fn0_function_l (ZF.modelsKP hZF) fh) ha
  have next := control.step i h a t hi hh ha fh endt (Or.inr ⟨turn, value⟩)
  have check := ((rules.checks t).mp (control.legal.current_l ((control.positions t).mp next).1)).2
  have step := (tg_step_read_l hZF (rules.omega.members_areOrdinals hZF i hi)
    oc ⟨p.b, rules.three.predecessor_mem⟩ hn div).mp (check.end_l hZF fh endt)
  have aux := step.elim And.right (fun h => h.elim (fun h => (ne₁ h.1).elim) (fun h => (ne₂ h.1).elim))
  obtain ⟨m, k, d⟩ := endt
  have ej := d.source.2.2.2.eq hZF.1 ft.2.1
  have ei := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  have succ : M.SuccessorOf j i := ej ▸ ei ▸ d.length_successor
  exact ⟨a, t, j, ha, value, ⟨m, k, d⟩, hj, succ,
    fn0_of_function_l (ZF.modelsKP hZF) ft, next,
    tg_division_next_l hZF oc div rules.one succ (oc.transitive p.b rules.three.predecessor_mem p.a rules.two.predecessor_mem),
    aux, i, div, ei ▸ d.last_value⟩

def tg_aux_control_m {d} (p : Tg_params_d (Term d)) (X σ R : Term d) : Formula 1 d :=
  let q := p.map_l (fun t => t.weaken.weaken.weaken.weaken.weaken.weaken)
  set[d] ⟪∀ i ∈ ⌜p.ω⌝ₛ, ∀ n ∈ ⌜p.ω⌝ₛ, ∀ h ∈ ⌜R⌝ₛ,
    ⌜fn0_m⌝ₚ(i, ⌜X⌝ₛ, h) → ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(i, ⌜p.c⌝ₛ, n, ⌜p.e⌝ₛ) →
    ∃ a t j, a ∈ ⌜X⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(h, a, ⌜σ⌝ₛ) ∧
      ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p.ω⌝ₛ, t, h, a) ∧ j ∈ ⌜p.ω⌝ₛ ∧
      ⌜Formula.isSuccessor⌝ₚ(j, i) ∧ ⌜fn0_m⌝ₚ(j, ⌜X⌝ₛ, t) ∧ t ∈ ⌜R⌝ₛ ∧
      ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(j, ⌜p.c⌝ₛ, n, ⌜p.a⌝ₛ) ∧
      ⌜fun n h a => tg_aux_m q n h a⌝ₚ(n, h, a) ∧ ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ, n, ⌜p.e⌝ₛ, t, a)⟫

@[simp] theorem tg_aux_control_closed_l {d} (p : Tg_params_d (Term d)) (X σ R : Term d)
    (hp : p.closed_l) (hX : X.freeSupport = []) (hσ : σ.freeSupport = []) (hR : R.freeSupport = []) :
    (tg_aux_control_m p X σ R).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken.weaken.weaken.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using hp
  have hc := tg_aux_closed_l _ (.bound 4) (.bound 3) (.bound 2) hp' rfl rfl rfl
  rcases hp with ⟨hw, he, h₁, _, h₃, _⟩
  simp -implicitDefEqProofs [tg_aux_control_m, Definitional.Formula.FreeClosed, hw, he, h₁, h₃, hX, hσ, hR]
  exact hc

theorem tg_aux_control_l (hZF : M.Models ZF) {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X F L G J σ R : Term d)
    (rules : Tg_rules_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (F.eval ρ) (L.eval ρ) (J.eval ρ))
    (control : Cg_control_d (kp_pair_l (ZF.modelsKP hZF)) (p.ω.eval ρ) (p.e.eval ρ)
      (X.eval ρ) (F.eval ρ) (L.eval ρ) (G.eval ρ) (J.eval ρ) (σ.eval ρ) (R.eval ρ)) :
    Formula.satisfies ρ (tg_aux_control_m p X σ R) := by
  simp only [tg_aux_control_m, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    fn0_sat_l hZF.1, Formula.satisfies_isOrdinalDivision_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    rd_entry0_sat_l hZF.1, fseq_end_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Formula.satisfies_isSuccessor_iff, tg_aux_sat_l hZF, tg_event_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Tg_params_d.map_l, Definitional.Term.eval_weaken]
  intro i hi n hn h hh fn div
  exact rules.aux_l hZF control hi hn hh fn div

/-- 零轮不可能引用较早轮，因此原策略的首个合法辅助走法必为重置。 -/
theorem Tg_rules_d.start_l (hZF : M.Models ZF) {p : Tg_params_d M.Domain} {X F L G J σ R : M.Domain}
    (rules : Tg_rules_d hZF p X F L J) (control : Cg_control_d (kp_pair_l (ZF.modelsKP hZF)) p.ω p.e X F L G J σ R) :
    ∃ a h j, M.mem a X ∧ Rd_entry_d p.e a σ ∧ Fseq_end_d (kp_pair_l (ZF.modelsKP hZF)) p.ω h p.e a ∧
      M.mem j p.ω ∧ M.SuccessorOf j p.e ∧ Fn0_d j X h ∧ M.mem h R ∧
      M.IsOrdinalDivision (kp_pair_l (ZF.modelsKP hZF)) j p.c p.e p.a ∧ Tg_aux_d hZF p p.e p.e a ∧
      Tg_event_d (kp_pair_l (ZF.modelsKP hZF)) p.c p.e p.e h a ∧
      ∃ ℓ κ u, Tg_aux_data_d a ℓ p.e κ u := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have he := num_mem_l hZF.1 rules.omega (show Num_d 0 p.e from rules.empty)
  obtain ⟨hc, _⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three he
  have oc := rules.omega.members_areOrdinals hZF p.c hc
  have ec := oc.transitive p.b rules.three.predecessor_mem p.e
    ((oc.mem rules.three.predecessor_mem).transitive p.a rules.two.predecessor_mem p.e rules.one.predecessor_mem)
  have div : M.IsOrdinalDivision I p.e p.c p.e p.e :=
    ⟨rules.omega.members_areOrdinals hZF p.e he, ec, p.e,
      (ZF.ordinalMultiplication_zero_iff hZF I oc rules.empty).mpr rules.empty,
      (ZF.ordinalAddition_zero_iff hZF I rules.empty).mpr rfl⟩
  have fe : Fn0_d p.e X p.e := ⟨fun x hx => (rules.empty x hx).elim,
    fun x hx => (rules.empty x hx).elim, fun x hx => (rules.empty x hx).elim⟩
  obtain ⟨a, h, j, ha, value, endt, hj, succ, fn, next, clock, aux, event⟩ := rules.aux_l hZF control he he control.root fe div
  refine ⟨a, h, j, ha, value, endt, hj, succ, fn, next, clock, aux, event, ?_⟩
  obtain ⟨ℓ, t, κ, u, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    data, _, _, _, _, _, _, _, _, _, _, _, _, _, branch⟩ := aux
  rcases branch with ⟨eq, _⟩ | ⟨_, old⟩
  · exact ⟨ℓ, κ, u, eq ▸ data⟩
  · exact (rules.empty ℓ old.1).elim

def tg_start_control_m {d} (p : Tg_params_d (Term d)) (X σ R : Term d) : Formula 1 d :=
  let q := p.map_l (fun t => t.weaken.weaken.weaken)
  set[d] ⟪∃ a h j, a ∈ ⌜X⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(⌜p.e⌝ₛ, a, ⌜σ⌝ₛ) ∧
    ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p.ω⌝ₛ, h, ⌜p.e⌝ₛ, a) ∧ j ∈ ⌜p.ω⌝ₛ ∧
    ⌜Formula.isSuccessor⌝ₚ(j, ⌜p.e⌝ₛ) ∧ ⌜fn0_m⌝ₚ(j, ⌜X⌝ₛ, h) ∧ h ∈ ⌜R⌝ₛ ∧
    ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(j, ⌜p.c⌝ₛ, ⌜p.e⌝ₛ, ⌜p.a⌝ₛ) ∧
    ⌜fun e a => tg_aux_m q e e a⌝ₚ(⌜p.e⌝ₛ, a) ∧
    ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ, ⌜p.e⌝ₛ, ⌜p.e⌝ₛ, h, a) ∧
    ⌜tg_reset_result_m⌝ₚ(⌜p.ω⌝ₛ, ⌜p.e⌝ₛ, ⌜p.δ⌝ₛ, ⌜p.S⌝ₛ, ⌜p.ν⌝ₛ, ⌜p.E⌝ₛ, ⌜p.P⌝ₛ, a, ⌜p.e⌝ₛ, ⌜p.A⌝ₛ)⟫

theorem tg_start_control_closed_l {d} (p : Tg_params_d (Term d)) (X σ R : Term d)
    (hp : p.closed_l) (hX : X.freeSupport = []) (hσ : σ.freeSupport = []) (hR : R.freeSupport = []) :
    (tg_start_control_m p X σ R).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using hp
  have he : p.e.weaken.weaken.weaken.freeSupport = [] := by simpa using hp.2.1
  rcases hp with ⟨hw, h₀, h₁, _, h₃, hd, hA, hS, hν, hE, hP, _⟩
  simp -implicitDefEqProofs [tg_start_control_m, Definitional.Formula.FreeClosed, hw, h₀, h₁, h₃, hX, hσ, hR, hd, hA, hS, hν, hE, hP]
  exact tg_aux_closed_l _ _ _ _ hp' he he rfl

theorem tg_start_control_l (hZFC : M.Models ZFC) {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X F L G J σ R : Term d)
    (setup : Tg_setup_d hZFC (p.map_l (fun t => t.eval ρ)) (X.eval ρ))
    (rules : Tg_rules_d (ZFC.models_zf_l hZFC) (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (F.eval ρ) (L.eval ρ) (J.eval ρ))
    (control : Cg_control_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (p.ω.eval ρ) (p.e.eval ρ)
      (X.eval ρ) (F.eval ρ) (L.eval ρ) (G.eval ρ) (J.eval ρ) (σ.eval ρ) (R.eval ρ)) :
    Formula.satisfies ρ (tg_start_control_m p X σ R) := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [tg_start_control_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    rd_entry0_sat_l hZF.1, fseq_end_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    Formula.satisfies_isSuccessor_iff, fn0_sat_l hZF.1, tg_aux_sat_l hZF,
    Formula.satisfies_isOrdinalDivision_iff (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    tg_event_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1,
    tg_reset_result_m, Formula.satisfies_bind, Tg_params_d.map_l, Definitional.Term.eval_weaken]
  obtain ⟨a, h, j, ha, value, endt, hj, succ, fn, next, clock, aux, event, ℓ, κ, u, data⟩ := rules.start_l hZF control
  refine ⟨a, h, j, ha, value, endt, hj, succ, fn, next, clock, aux, event, ?_⟩
  have result := setup.reset_result_l hZFC rules.woodin rules.root aux data
  refine (Formula.closed_env_l tg_reset_result0_m tg_reset_result0_closed_l
    (ρ := ⟨fun i => [p.ω.eval ρ, p.e.eval ρ, p.δ.eval ρ, p.S.eval ρ, p.ν.eval ρ, p.E.eval ρ, p.P.eval ρ, a, p.e.eval ρ, p.A.eval ρ].get i,
      fun _ => p.ω.eval ρ⟩) (η := _) ?_).mp result
  have eval (t : Term d) : t.eval ρ = t.weaken.weaken.weaken.eval (((ρ.push a).push h).push j) := by
    simp only [Definitional.Term.eval_weaken]
  funext i
  exact Fin.cases (eval p.ω) (Fin.cases (eval p.e) (Fin.cases (eval p.δ) (Fin.cases (eval p.S)
    (Fin.cases (eval p.ν) (Fin.cases (eval p.E) (Fin.cases (eval p.P) (Fin.cases rfl (Fin.cases (eval p.e)
      (Fin.cases (eval p.A) (fun k => Fin.elim0 k)))))))))) i

def tg_control0_m : Formula 1 19 :=
  let v : Fin 19 → Term 19 := Term.bound
  let p := tg_control_params_d v
  .conj (tg_tables_m p.ω p.e p.δ p.E p.P p.Q) (.conj
    (cg_control_m p.ω p.e (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18))
    (.conj (tg_rules_m p (v 12) (v 13) (v 14) (v 16))
      (.conj (tg_aux_control_m p (v 12) (v 17) (v 18))
        (.conj (tg_reset_control_m p) (.conj (tg_start_control_m p (v 12) (v 17) (v 18))
          (.conj (tg_answer_control_m p (v 12) (v 18))
            (.conj (tg_digit_control_m p (v 12) (v 17) (v 18)) (cg_rank_m p.ω (v 12) (v 18)))))))))

theorem tg_control0_closed_l : tg_control0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_control0_m, tg_control_params_d, Definitional.Formula.FreeClosed]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply tg_rules_closed_l <;> simp [Tg_params_d.closed_l]
  · apply tg_aux_control_closed_l <;> simp [Tg_params_d.closed_l]
  · apply tg_reset_control_closed_l
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · apply tg_start_control_closed_l <;> try rfl
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · apply tg_answer_control_closed_l <;> simp [Tg_params_d.closed_l]
  · apply tg_digit_control_closed_l <;> simp [Tg_params_d.closed_l]

theorem Tg_game_d.control_l (hZFC : M.Models ZFC)
    {p : Tg_params_d M.Domain} {X F L G J B W O Z g σ : M.Domain}
    (game : Tg_game_d hZFC p X F L G J B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) false p.ω X F J B W σ) :
    ∃ R r, let v : Fin 19 → M.Domain := fun i =>
      [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, X, F, L, G, J, σ, R].get i
      Rt_tuple_d v r ∧ Formula.satisfies (⟨v, fun _ => p.ω⟩ : Env M 19) tg_control0_m ∧
        Formula.satisfies ((⟨Fin.elim0, fun _ => p.ω⟩ : Env M 0).push r) (rt_record_m tg_control0_m .newest) := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨R, control⟩ := cg_control_l hZF game.setup.omega game.setup.empty game.histories.1 game.legal
    (game.empty_l hZFC) game.runs game.payoff win
  let v : Fin 19 → M.Domain := fun i =>
    [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, X, F, L, G, J, σ, R].get i
  let ρ : Env M 19 := ⟨v, fun _ => p.ω⟩
  obtain ⟨r, tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) v
  obtain ⟨α, H, rank⟩ := control.rank_l hZF game.setup.omega (ZFC.dc_l I hZFC game.setup.omega)
    game.runs game.payoff win
  have ranked : Formula.satisfies ρ (cg_rank_m (.bound 0) (.bound 12) (.bound 18)) := by
    simp only [cg_rank_m, Formula.satisfies_exists_iff]
    exact ⟨α, H, (cg_rank0_sat_l (ZF.modelsKP hZF) ..).mpr rank⟩
  have valid : Formula.satisfies ρ tg_control0_m := by
    apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨game.setup.tables_l hZFC ρ (.bound 0) (.bound 1) (.bound 5) (.bound 9) (.bound 10) (.bound 11)
      rfl rfl rfl rfl rfl rfl, ?_⟩
    apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨(cg_control_sat_l I hZF.1 ..).mpr control, ?_⟩
    have rules : Tg_rules_d hZF p X F L J :=
      ⟨game.setup.omega, game.setup.empty, game.setup.one, game.setup.two, game.setup.three,
        woodin, game.setup.rank, game.setup.letters, root, game.setup.low, game.histories.2, game.owner⟩
    exact (Formula.satisfies_conj_iff ..).mpr ⟨(tg_rules_sat_l hZF ..).mpr rules,
      (Formula.satisfies_conj_iff ..).mpr
        ⟨tg_aux_control_l hZF ρ _ _ (.bound 13) (.bound 14) (.bound 15) (.bound 16) _ _ rules control,
          (Formula.satisfies_conj_iff ..).mpr ⟨tg_reset_control_l hZFC ρ _ game.setup woodin root,
            (Formula.satisfies_conj_iff ..).mpr
              ⟨tg_start_control_l hZFC ρ _ _ (.bound 13) (.bound 14) (.bound 15) (.bound 16) _ _ game.setup rules control,
                (Formula.satisfies_conj_iff ..).mpr
                  ⟨tg_answer_control_l hZFC ρ _ _ (.bound 13) (.bound 14) (.bound 15) (.bound 16) (.bound 17) _ game.setup rules control,
                    (Formula.satisfies_conj_iff ..).mpr
                      ⟨tg_digit_control_l hZF ρ _ _ (.bound 13) (.bound 14) (.bound 15) (.bound 16) _ _ rules control,
                        ranked⟩⟩⟩⟩⟩⟩
  exact ⟨R, r, tuple, valid, (rt_record_sat_l hZF.1 _ _ _ tg_control0_closed_l).mpr ⟨v, tuple, valid⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
