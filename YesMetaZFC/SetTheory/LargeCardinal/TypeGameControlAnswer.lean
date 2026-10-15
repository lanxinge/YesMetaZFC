import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControl

/-! # 原规则 (7) 自动延伸策略控制历史

合法回答的两个坐标及其配对均在原走法域内。追加这个回答后检查的正是
原游戏的最后一步，控制集合随即给出仍相容的下一位置及下一阶段时钟。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_setup_d.answer_member_l {p : Tg_params_d M.Domain} {X n h v : M.Domain}
    (setup : Tg_setup_d hZFC p X) (answer : Tg_answer_d hZF p n h v) : M.mem v X := by
  obtain ⟨a, ℓ, t, κ, u, τ, w, k, l, N, B, U, D, g₀, g₁, g₂, g₃, C, V, W, r, m, q, f, j, b, z,
    s₀, s₁, s₂, s₃, s₄, s₅, s₆, _, _, pair, _, _, _, _, below, request, query, _, reply⟩ := answer
  obtain ⟨l', n', _, _, language, _⟩ := setup.queries.read_l hZFC below request query
  have hV := tt_constants_rank_l hZF setup.rank setup.limit below language.rank language.constants
  have hW := language.pool.rank_mem_l hZF setup.omega setup.rank setup.limit
    (ZF.v_ordinal_mem_l I hZF setup.rank setup.above) language.finite hV
  have hw := ZF.v_subset_mem_l I hZF setup.rank hW reply.1
  obtain ⟨v', hv, pair'⟩ := (sc_v_algebra_l hZFC setup.limit setup.rank).kpair_l
    (ZF.v_ordinal_mem_l I hZF setup.rank below) hw
  exact kpair_unique_l M hZF.1 pair' pair ▸ hv

theorem Tg_rules_d.answer_l {p : Tg_params_d M.Domain} {X F L G J σ R i n h v : M.Domain}
    (setup : Tg_setup_d hZFC p X) (rules : Tg_rules_d hZF p X F L J)
    (control : Cg_control_d I false p.ω p.e X F L G J σ R)
    (hi : M.mem i p.ω) (hn : M.mem n p.ω) (hh : M.mem h R) (fh : Fn0_d i X h)
    (div : M.IsOrdinalDivision I i p.c n p.a) (answer : Tg_answer_d hZF p n h v) :
    ∃ t j, Fseq_end_d I p.ω t h v ∧ M.mem j p.ω ∧ M.SuccessorOf j i ∧ Fn0_d j X t ∧ M.mem t R ∧
      M.IsOrdinalDivision I j p.c n p.b ∧ Tg_event_d I p.c n p.a t v := by
  have hv := setup.answer_member_l hZFC answer
  obtain ⟨hc, _⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three hi
  have oc := rules.omega.members_areOrdinals hZF p.c hc
  obtain ⟨j, t, hj, ft, endt⟩ := ZF.fseq_end_exists_l I hZF rules.omega hi (fn0_function_l (ZF.modelsKP hZF) fh) hv
  have fn := fn0_of_function_l (ZF.modelsKP hZF) ft
  obtain ⟨m, k, d⟩ := endt
  have ej := d.source.2.2.2.eq hZF.1 ft.2.1
  have ei := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  have succ : M.SuccessorOf j i := ej ▸ ei ▸ d.length_successor
  have endt : Fseq_end_d I p.ω t h v := ⟨m, k, d⟩
  have check := tg_check_end_l hZF hj succ fn fh endt ⟨n, p.a, hn, div, Or.inr (Or.inl ⟨rfl, answer⟩)⟩
  have legal := (rules.checks t).mpr ⟨(control.space t).mpr ⟨j, hj, ft⟩, check⟩
  have turn := (rules.owner.read_l hZF (rules.omega.isOrdinal hZF) oc ⟨p.b, rules.three.predecessor_mem⟩ hi hn div).mpr (Or.inl rfl)
  exact ⟨t, j, endt, hj, succ, fn, control.step i h v t hi hh hv fh endt (Or.inl ⟨turn, legal⟩),
    tg_division_next_l hZF oc div rules.two succ rules.three.predecessor_mem, i, div, ei ▸ d.last_value⟩

def tg_answer_control_m {d} (p : Tg_params_d (Term d)) (X R : Term d) : Formula 1 d :=
  let q := p.map_l (fun t => t.weaken.weaken.weaken.weaken)
  set[d] ⟪∀ i ∈ ⌜p.ω⌝ₛ, ∀ n ∈ ⌜p.ω⌝ₛ, ∀ h ∈ ⌜R⌝ₛ, ∀ v,
    ⌜fn0_m⌝ₚ(i, ⌜X⌝ₛ, h) → ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(i, ⌜p.c⌝ₛ, n, ⌜p.a⌝ₛ) →
    ⌜fun n h v => tg_answer_m q n h v⌝ₚ(n, h, v) → ∃ t j,
      ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p.ω⌝ₛ, t, h, v) ∧ j ∈ ⌜p.ω⌝ₛ ∧
      ⌜Formula.isSuccessor⌝ₚ(j, i) ∧ ⌜fn0_m⌝ₚ(j, ⌜X⌝ₛ, t) ∧ t ∈ ⌜R⌝ₛ ∧
      ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(j, ⌜p.c⌝ₛ, n, ⌜p.b⌝ₛ) ∧
      ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ, n, ⌜p.a⌝ₛ, t, v)⟫

@[simp] theorem tg_answer_control_closed_l {d} (p : Tg_params_d (Term d)) (X R : Term d)
    (hp : p.closed_l) (hX : X.freeSupport = []) (hR : R.freeSupport = []) :
    (tg_answer_control_m p X R).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using hp
  have closed := tg_answer_closed_l _ (.bound 2) (.bound 1) (.bound 0) hp' rfl rfl rfl
  rcases hp with ⟨hw, _, ha, hb, hc, _⟩
  simp -implicitDefEqProofs [tg_answer_control_m, Definitional.Formula.FreeClosed, hw, ha, hb, hc, hX, hR]
  exact closed

theorem tg_answer_control_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X F L G J σ R : Term d)
    (setup : Tg_setup_d hZFC (p.map_l (fun t => t.eval ρ)) (X.eval ρ))
    (rules : Tg_rules_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (F.eval ρ) (L.eval ρ) (J.eval ρ))
    (control : Cg_control_d I false (p.ω.eval ρ) (p.e.eval ρ) (X.eval ρ) (F.eval ρ) (L.eval ρ) (G.eval ρ)
      (J.eval ρ) (σ.eval ρ) (R.eval ρ)) : Formula.satisfies ρ (tg_answer_control_m p X R) := by
  simp only [tg_answer_control_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, fn0_sat_l hZF.1, Formula.satisfies_isOrdinalDivision_iff I hZF.1,
    tg_answer_sat_l hZF, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fseq_end_sat_l I hZF.1, Formula.satisfies_mem_iff, Formula.satisfies_isSuccessor_iff,
    tg_event_sat_l I hZF.1, Tg_params_d.map_l, Definitional.Term.eval_weaken]
  intro i hi n hn h hh v fn div answer
  exact rules.answer_l hZFC setup control hi hn hh fn div answer

end YesMetaZFC.SetTheory.LargeCardinal
