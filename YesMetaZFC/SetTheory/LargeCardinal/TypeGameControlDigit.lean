import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControl

/-! # 原实数落子与下一轮的控制位置

偶数轮保留玩家 I 给出的任意原字母，奇数轮使用 II 的原策略值。
两种情况都追加一项内部历史，并回到下一轮的辅助阶段。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_digit_end_d (p : Tg_params_d M.Domain) (X R i n h v : M.Domain) : Prop :=
  ∃ t j m, Fseq_end_d I p.ω t h v ∧ M.mem j p.ω ∧ M.mem m p.ω ∧ M.SuccessorOf j i ∧
    M.SuccessorOf m n ∧ Fn0_d j X t ∧ M.mem t R ∧ M.IsOrdinalDivision I j p.c m p.e ∧
    Tg_event_d I p.c n p.b t v

theorem Tg_rules_d.digit_l {p : Tg_params_d M.Domain} {X F L G J σ R i n h v : M.Domain}
    (rules : Tg_rules_d hZF p X F L J) (control : Cg_control_d I false p.ω p.e X F L G J σ R)
    (hi : M.mem i p.ω) (hn : M.mem n p.ω) (hh : M.mem h R) (fh : Fn0_d i X h)
    (div : M.IsOrdinalDivision I i p.c n p.b) (even : Gm_even_d I p.ω n) (hv : M.mem v p.A) :
    Tg_digit_end_d hZF p X R i n h v := by
  have hvX := ZF.v_transitive_l I hZF rules.rank p.A rules.letters v hv
  obtain ⟨hc, _⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three hi
  have oc := rules.omega.members_areOrdinals hZF p.c hc
  obtain ⟨j, t, hj, ft, endt⟩ := ZF.fseq_end_exists_l I hZF rules.omega hi (fn0_function_l (ZF.modelsKP hZF) fh) hvX
  have fn := fn0_of_function_l (ZF.modelsKP hZF) ft
  obtain ⟨a, b, d⟩ := endt
  have ej := d.source.2.2.2.eq hZF.1 ft.2.1
  have ei := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  have succ : M.SuccessorOf j i := ej ▸ ei ▸ d.length_successor
  have endt : Fseq_end_d I p.ω t h v := ⟨a, b, d⟩
  have check := tg_check_end_l hZF hj succ fn fh endt ⟨n, p.b, hn, div, Or.inr (Or.inr ⟨rfl, hv⟩)⟩
  have legal := (rules.checks t).mpr ⟨(control.space t).mpr ⟨j, hj, ft⟩, check⟩
  have turn := (rules.owner.read_l hZF (rules.omega.isOrdinal hZF) oc ⟨p.b, rules.three.predecessor_mem⟩ hi hn div).mpr
    (Or.inr ⟨rfl, even⟩)
  obtain ⟨m, next, hm⟩ := rules.omega.1.2 n hn
  exact ⟨t, j, m, endt, hj, hm, succ, next, fn, control.step i h v t hi hh hvX fh endt (Or.inl ⟨turn, legal⟩),
    tg_division_cycle_l hZF oc div rules.three next succ rules.empty, i, div, ei ▸ d.last_value⟩

theorem Tg_rules_d.digit_strategy_l {p : Tg_params_d M.Domain} {X F L G J σ R i n h : M.Domain}
    (rules : Tg_rules_d hZF p X F L J) (control : Cg_control_d I false p.ω p.e X F L G J σ R)
    (hi : M.mem i p.ω) (hn : M.mem n p.ω) (hh : M.mem h R) (fh : Fn0_d i X h)
    (div : M.IsOrdinalDivision I i p.c n p.b) (odd : ¬ Gm_even_d I p.ω n) :
    ∃ v, M.mem v p.A ∧ Rd_entry_d h v σ ∧ Tg_digit_end_d hZF p X R i n h v := by
  obtain ⟨hc, _⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three hi
  have oc := rules.omega.members_areOrdinals hZF p.c hc
  have ne₀ : p.b ≠ p.e := fun eq => rules.empty p.a (eq ▸ rules.two.predecessor_mem)
  have ne₁ : p.b ≠ p.a := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) p.a (eq ▸ rules.two.predecessor_mem)
  have turn : ¬ M.mem i J := fun h => ((rules.owner.read_l hZF (rules.omega.isOrdinal hZF)
    oc ⟨p.b, rules.three.predecessor_mem⟩ hi hn div).mp h).elim ne₁ (fun h => odd h.2)
  obtain ⟨v, hvX, value⟩ := control.strategy.2.1 h ((control.legal h).mp ((control.positions h).mp hh).1).1
  obtain ⟨j, t, hj, ft, endt⟩ := ZF.fseq_end_exists_l I hZF rules.omega hi (fn0_function_l (ZF.modelsKP hZF) fh) hvX
  have position := control.step i h v t hi hh hvX fh endt (Or.inr ⟨turn, value⟩)
  have check := ((rules.checks t).mp (control.legal.current_l ((control.positions t).mp position).1)).2
  have step := (tg_step_read_l hZF (rules.omega.members_areOrdinals hZF i hi)
    oc ⟨p.b, rules.three.predecessor_mem⟩ hn div).mp (check.end_l hZF fh endt)
  have hv := step.elim (fun h => (ne₀ h.1).elim) (fun h => h.elim (fun h => (ne₁ h.1).elim) And.right)
  obtain ⟨a, b, d⟩ := endt
  have ej := d.source.2.2.2.eq hZF.1 ft.2.1
  have ei := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  have succ : M.SuccessorOf j i := ej ▸ ei ▸ d.length_successor
  obtain ⟨m, next, hm⟩ := rules.omega.1.2 n hn
  exact ⟨v, hv, value, t, j, m, ⟨a, b, d⟩, hj, hm, succ, next, fn0_of_function_l (ZF.modelsKP hZF) ft, position,
    tg_division_cycle_l hZF oc div rules.three next succ rules.empty, i, div, ei ▸ d.last_value⟩

def tg_digit_end_m {d} (ω e b c X R i n h v : Term d) : Formula 1 d := set[d] ⟪∃ t j m,
  ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, t, ⌜h⌝ₛ, ⌜v⌝ₛ) ∧ j ∈ ⌜ω⌝ₛ ∧ m ∈ ⌜ω⌝ₛ ∧
  ⌜Formula.isSuccessor⌝ₚ(j, ⌜i⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(m, ⌜n⌝ₛ) ∧ ⌜fn0_m⌝ₚ(j, ⌜X⌝ₛ, t) ∧ t ∈ ⌜R⌝ₛ ∧
  ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(j, ⌜c⌝ₛ, m, ⌜e⌝ₛ) ∧ ⌜tg_event_m⌝ₚ(⌜c⌝ₛ, ⌜n⌝ₛ, ⌜b⌝ₛ, t, ⌜v⌝ₛ)⟫
derive_free_closed tg_digit_end_m

def tg_digit_control_m {d} (p : Tg_params_d (Term d)) (X σ R : Term d) : Formula 1 d := set[d] ⟪
  ∀ i ∈ ⌜p.ω⌝ₛ, ∀ n ∈ ⌜p.ω⌝ₛ, ∀ h ∈ ⌜R⌝ₛ,
    ⌜fn0_m⌝ₚ(i, ⌜X⌝ₛ, h) → ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(i, ⌜p.c⌝ₛ, n, ⌜p.b⌝ₛ) →
    ((⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p.ω⌝ₛ, n) → ∀ v ∈ ⌜p.A⌝ₛ,
      ⌜tg_digit_end_m⌝ₚ(⌜p.ω⌝ₛ, ⌜p.e⌝ₛ, ⌜p.b⌝ₛ, ⌜p.c⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, i, n, h, v)) ∧
    (¬ ⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p.ω⌝ₛ, n) → ∃ v, v ∈ ⌜p.A⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(h, v, ⌜σ⌝ₛ) ∧
      ⌜tg_digit_end_m⌝ₚ(⌜p.ω⌝ₛ, ⌜p.e⌝ₛ, ⌜p.b⌝ₛ, ⌜p.c⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, i, n, h, v)))⟫

@[simp] theorem tg_digit_control_closed_l {d} (p : Tg_params_d (Term d)) (X σ R : Term d)
    (hp : p.closed_l) (hX : X.freeSupport = []) (hσ : σ.freeSupport = []) (hR : R.freeSupport = []) :
    (tg_digit_control_m p X σ R).FreeClosed := by
  rcases hp with ⟨hw, he, _, hb, hc, _, hA, _⟩
  simp -implicitDefEqProofs [tg_digit_control_m, Definitional.Formula.FreeClosed, hw, he, hb, hc, hA, hX, hσ, hR]

theorem tg_digit_control_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X F L G J σ R : Term d)
    (rules : Tg_rules_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (F.eval ρ) (L.eval ρ) (J.eval ρ))
    (control : Cg_control_d I false (p.ω.eval ρ) (p.e.eval ρ) (X.eval ρ) (F.eval ρ) (L.eval ρ) (G.eval ρ)
      (J.eval ρ) (σ.eval ρ) (R.eval ρ)) : Formula.satisfies ρ (tg_digit_control_m p X σ R) := by
  simp only [tg_digit_control_m, tg_digit_end_m, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_conj_iff, fn0_sat_l hZF.1,
    Formula.satisfies_isOrdinalDivision_iff I hZF.1, gm_even_sat_l I hZF.1, Formula.satisfies_neg_iff,
    Formula.satisfies_exists_iff, fseq_end_sat_l I hZF.1, Formula.satisfies_mem_iff,
    Formula.satisfies_isSuccessor_iff, tg_event_sat_l I hZF.1, rd_entry0_sat_l hZF.1,
    Definitional.Term.eval_weaken]
  intro i hi n hn h hh fn div
  exact ⟨fun even v hv => rules.digit_l hZF control hi hn hh fn div even hv,
    fun odd => rules.digit_strategy_l hZF control hi hn hh fn div odd⟩

end YesMetaZFC.SetTheory.LargeCardinal
