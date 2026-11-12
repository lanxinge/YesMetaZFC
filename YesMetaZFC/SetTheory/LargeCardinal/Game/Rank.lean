import YesMetaZFC.SetTheory.LargeCardinal.Game.Control
import YesMetaZFC.SetTheory.Descriptive.Game.GameAttemptRank
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence

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
  have hW := language.pool.rank_mem_l (ZF.modelsKP hZF) setup.omega setup.rank setup.limit
    (ZF.v_ordinal_mem_l I hZF setup.rank setup.above) language.finite hV
  have hw := v_subset_mem_l I setup.rank hW reply.1
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
  have oc := rules.omega.members_areOrdinals (ZF.modelsKP hZF) p.c hc
  obtain ⟨j, t, hj, ft, endt⟩ := ZF.fseq_end_exists_l I hZF rules.omega hi (fn0_function_l (ZF.modelsKP hZF) fh) hv
  have fn := fn0_of_function_l (ZF.modelsKP hZF) ft
  obtain ⟨m, k, d⟩ := endt
  have ej := d.source.2.2.2.eq hZF.1 ft.2.1
  have ei := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  have succ : M.SuccessorOf j i := ej ▸ ei ▸ d.length_successor
  have endt : Fseq_end_d I p.ω t h v := ⟨m, k, d⟩
  have check := tg_check_end_l hZF hj succ fn fh endt ⟨n, p.a, hn, div, Or.inr (Or.inl ⟨rfl, answer⟩)⟩
  have legal := (rules.checks t).mpr ⟨(control.space t).mpr ⟨j, hj, ft⟩, check⟩
  have turn := (rules.owner.read_l hZF (rules.omega.isOrdinal (ZF.modelsKP hZF)) oc ⟨p.b, rules.three.predecessor_mem⟩ hi hn div).mpr (Or.inl rfl)
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

/-! ## 原实数落子与下一轮的控制位置

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
  have hvX := v_transitive_l I rules.rank p.A rules.letters v hv
  obtain ⟨hc, _⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three hi
  have oc := rules.omega.members_areOrdinals (ZF.modelsKP hZF) p.c hc
  obtain ⟨j, t, hj, ft, endt⟩ := ZF.fseq_end_exists_l I hZF rules.omega hi (fn0_function_l (ZF.modelsKP hZF) fh) hvX
  have fn := fn0_of_function_l (ZF.modelsKP hZF) ft
  obtain ⟨a, b, d⟩ := endt
  have ej := d.source.2.2.2.eq hZF.1 ft.2.1
  have ei := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  have succ : M.SuccessorOf j i := ej ▸ ei ▸ d.length_successor
  have endt : Fseq_end_d I p.ω t h v := ⟨a, b, d⟩
  have check := tg_check_end_l hZF hj succ fn fh endt ⟨n, p.b, hn, div, Or.inr (Or.inr ⟨rfl, hv⟩)⟩
  have legal := (rules.checks t).mpr ⟨(control.space t).mpr ⟨j, hj, ft⟩, check⟩
  have turn := (rules.owner.read_l hZF (rules.omega.isOrdinal (ZF.modelsKP hZF)) oc ⟨p.b, rules.three.predecessor_mem⟩ hi hn div).mpr
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
  have oc := rules.omega.members_areOrdinals (ZF.modelsKP hZF) p.c hc
  have ne₀ : p.b ≠ p.e := fun eq => rules.empty p.a (eq ▸ rules.two.predecessor_mem)
  have ne₁ : p.b ≠ p.a := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) p.a (eq ▸ rules.two.predecessor_mem)
  have turn : ¬ M.mem i J := fun h => ((rules.owner.read_l hZF (rules.omega.isOrdinal (ZF.modelsKP hZF))
    oc ⟨p.b, rules.three.predecessor_mem⟩ hi hn div).mp h).elim ne₁ (fun h => odd h.2)
  obtain ⟨v, hvX, value⟩ := control.strategy.2.1 h ((control.legal h).mp ((control.positions h).mp hh).1).1
  obtain ⟨j, t, hj, ft, endt⟩ := ZF.fseq_end_exists_l I hZF rules.omega hi (fn0_function_l (ZF.modelsKP hZF) fh) hvX
  have position := control.step i h v t hi hh hvX fh endt (Or.inr ⟨turn, value⟩)
  have check := ((rules.checks t).mp (control.legal.current_l ((control.positions t).mp position).1)).2
  have step := (tg_step_read_l hZF (rules.omega.members_areOrdinals (ZF.modelsKP hZF) i hi)
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

/-! ## 原重置走法自动成为更新输入

空标签列强制元数为零。固定两张语言表识别同一 Vκ 及其常量域，原完整
重置类型与原 dcp 弹性随即给出更新输入；程序从开局时的实际表中读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_setup_d.reset_input_l {p : Tg_params_d M.Domain} {X n h a ℓ κ u : M.Domain}
    (setup : Tg_setup_d hZFC p X) (woodin : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (aux : Tg_aux_d hZF p n h a) (data : Tg_aux_data_d a ℓ p.e κ u) :
    ∃ v : Fin 38 → M.Domain,
      Formula.satisfies (⟨v, fun _ => p.ω⟩ : Env M 38) tg_seed0_m ∧
      (∀ i : Fin 5, v (i.castAdd 33) = [p.ω, p.e, p.δ, p.S, p.ν].get i) ∧
      v 6 = p.e ∧ v 23 = v 5 ∧ v 24 = p.e ∧ v 25 = p.e ∧ v 26 = p.e ∧
      Tg_aux_data_d a ℓ (v 25) (v 5) (v 18) ∧
      Tg_ee_data_d p.E (v 5) (v 7) (v 14) (v 15) (v 16) ⟨v 27, v 28, v 29, v 30⟩ ∧
      Tg_program_data_d p.P (v 7) (v 20) (v 22) (Fin.cases (v 31) (Fin.cases (v 32) (Fin.cases (v 33)
        (Fin.cases (v 34) (Fin.cases (v 35) (Fin.cases (v 36) (fun _ => v 37))))))) ∧
      (n = p.e → M.mem p.A (v 14)) := by
  obtain ⟨ℓ₀, t, κ₀, u₀, k, l, N, x, s, B, U, D, r₀, m, b₀, q, f, C, V, W, g₀, g₁, g₂, g₃,
    parsed, hk, ft, hl, hN, _, _, request, query, _, ee, elastic, _, growth, branch⟩ := aux
  obtain ⟨rfl, rfl, rfl, rfl⟩ := parsed.unique_l data
  have ke : k = p.e := hZF.1.eq_of_same_members k p.e (fun i => iff_of_false
    (fun hi => (ft.2.1 i hi).elim fun y hy => hy.2.elim fun z hz => setup.empty z hz.2) (setup.empty i))
  subst k
  obtain ⟨α, Y, c, R, r, height, rank, model, type, first, last⟩ :=
    branch.elim And.right (fun no => (no.1 rfl).elim)
  obtain ⟨l', N', hl', hN', target, _, _, _⟩ := setup.queries.read_l hZFC hk request query
  have el := hl'.eq hZF.1 hl
  subst l'
  have eN := hN'.eq hZF.1 hN
  subst N'
  have hlω := setup.omega.transitive (ZF.modelsKP hZF) N target.finite l hN.predecessor_mem
  have language := setup.elastic.elim fun _ table => table.read_l hZFC hk hlω request.1 ee
  have eB := ZF.v_unique_l I hZF target.rank language.rank
  subst C
  have eU := hZF.1.eq_of_same_members U V (fun z => (target.constants z).trans (language.constants z).symm)
  subst V
  obtain ⟨v, drop, elastic⟩ := elastic
  obtain ⟨H, _, programs, _⟩ := setup.programs
  obtain ⟨b, z, σ, program, pdata, prog⟩ := programs.get_l hZFC hlω
  have set : Sg_set_d I p.e l r p.e := by
    intro x
    refine iff_of_false (setup.empty x) ?_
    rintro ⟨i, hi, ne, _⟩
    exact ((hl i).mp hi).elim (setup.empty i) (fun eq => ne (hZF.1.eq_of_same_members i p.e eq))
  have node := (tg_node_empty_l I hZF.1 setup.empty).mpr root
  let v' : Fin 38 → M.Domain := fun i =>
    [p.ω, p.e, p.δ, p.S, p.ν, κ₀, p.e, l, N, α, Y, c, R, r, B, U, W, D, u₀, v,
      b, program, z, κ₀, p.e, p.e, p.e, g₀, g₁, g₂, g₃, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i
  have slots : (Fin.cases (σ 0) (Fin.cases (σ 1) (Fin.cases (σ 2) (Fin.cases (σ 3)
      (Fin.cases (σ 4) (Fin.cases (σ 5) (fun _ => σ 6))))))) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have valid : Formula.satisfies (⟨v', fun _ => p.ω⟩ : Env M 38) tg_seed0_m := by
    simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff,
      Formula.satisfies_isOmega_iff, Formula.satisfies_isEmpty_iff, Formula.satisfies_mem_iff,
      woodin_sat_l I hZF.1, tg_low_sat_l hZF, Formula.satisfies_isSuccessor_iff, v_sat_l I hZF.1,
      smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF), ee_language_sat_l hZFC,
      td_dcp_sat_l I hZF.1, ee_elastic_sat_l, rd_entry0_sat_l hZF.1, sg_set_sat_l I hZF.1,
      tg_node_sat_l I hZF.1, ts_program_sat_l hZF, tt_eval_cases_l, tg_bound_raw_sat_l I hZF.1, fn0_sat_l hZF.1]
    obtain ⟨hδν, Y₀, rank₀, hS⟩ := setup.low.read_l hZF setup.limit.1
    exact ⟨setup.omega, setup.empty, num_mem_l hZF.1 setup.omega (show Num_d 0 p.e from setup.empty),
      woodin, setup.low, root, hk, hl, hN, height, rank, model, type, language, drop, elastic,
      first, last, set, node, slots.symm ▸ prog, hk, ⟨v_ordinal_l I rank₀, hδν, Y₀, rank₀, hS⟩, ft⟩
  refine ⟨v', valid, ?_, rfl, rfl, rfl, rfl, rfl, data, ee, slots.symm ▸ pdata, ?_⟩
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i
  · intro zero
    rcases growth with ⟨_, hA⟩ | ⟨j, _, _, _, _, _, succ, _⟩
    · exact hA
    · exact (setup.empty j (zero ▸ succ.predecessor_mem)).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 重置输入的原公式总构造

新三十八个坐标全部由存在量词产生，并逐项连接原树、原走法和固定程序表。
此有限公式作为控制记录的一部分反射，后续重置直接得到同一更新输入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- 后十个参数为 ω,e,δ,S,ν,E,P、当前辅助走法、轮号和原字母表。
def tg_reset_body0_m : Formula 1 48 := .conj
  (tg_seed0_m.rename (fun i => ⟨i.val, by omega⟩))
  (let v : Fin 48 → Term 48 := Term.bound
   set[48] ⟪⌜v 0⌝ₛ = ⌜v 38⌝ₛ ∧ ⌜v 1⌝ₛ = ⌜v 39⌝ₛ ∧ ⌜v 2⌝ₛ = ⌜v 40⌝ₛ ∧
    ⌜v 3⌝ₛ = ⌜v 41⌝ₛ ∧ ⌜v 4⌝ₛ = ⌜v 42⌝ₛ ∧ ⌜v 6⌝ₛ = ⌜v 39⌝ₛ ∧ ⌜v 23⌝ₛ = ⌜v 5⌝ₛ ∧
    ⌜v 24⌝ₛ = ⌜v 39⌝ₛ ∧ ⌜v 25⌝ₛ = ⌜v 39⌝ₛ ∧ ⌜v 26⌝ₛ = ⌜v 39⌝ₛ ∧
    (∃ ℓ, ⌜tg_aux_data_m⌝ₚ(⌜v 45⌝ₛ, ℓ, ⌜v 25⌝ₛ, ⌜v 5⌝ₛ, ⌜v 18⌝ₛ)) ∧
    ⌜tg_ee_data_m⌝ₚ(⌜v 43⌝ₛ, ⌜v 5⌝ₛ, ⌜v 7⌝ₛ, ⌜v 14⌝ₛ, ⌜v 15⌝ₛ, ⌜v 16⌝ₛ,
      ⌜v 27⌝ₛ, ⌜v 28⌝ₛ, ⌜v 29⌝ₛ, ⌜v 30⌝ₛ) ∧
    ⌜fun P n b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_program_data_m P n b z
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜v 44⌝ₛ, ⌜v 7⌝ₛ, ⌜v 20⌝ₛ, ⌜v 22⌝ₛ, ⌜v 31⌝ₛ, ⌜v 32⌝ₛ, ⌜v 33⌝ₛ, ⌜v 34⌝ₛ, ⌜v 35⌝ₛ, ⌜v 36⌝ₛ, ⌜v 37⌝ₛ) ∧
      (⌜v 46⌝ₛ = ⌜v 39⌝ₛ → ⌜v 47⌝ₛ ∈ ⌜v 14⌝ₛ)⟫)

theorem tg_reset_body0_closed_l : tg_reset_body0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_reset_body0_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ]

def tg_reset_result0_m : Formula 1 10 := rt_exists_m 38 tg_reset_body0_m

theorem tg_reset_result0_closed_l : tg_reset_result0_m.FreeClosed :=
  (rt_exists_closed_l _).mpr tg_reset_body0_closed_l

def tg_reset_result_m {d} (ω e δ S ν E P a n A : Term d) : Formula 1 d :=
  tg_reset_result0_m.bind (fun i => [ω, e, δ, S, ν, E, P, a, n, A].get i)

@[simp] theorem tg_reset_result_closed_l {d} (ω e δ S ν E P a n A : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (hd : δ.freeSupport = []) (hS : S.freeSupport = [])
    (hν : ν.freeSupport = []) (hE : E.freeSupport = []) (hP : P.freeSupport = [])
    (ha : a.freeSupport = []) (hn : n.freeSupport = [])
    (hA : A.freeSupport = []) : (tg_reset_result_m ω e δ S ν E P a n A).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_reset_result0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, he, hd, hS, hν, hE, hP, ha, hn, hA, fun i => Fin.elim0 i⟩

theorem Tg_setup_d.reset_result_l (hZFC : M.Models ZFC) {p : Tg_params_d M.Domain} {X n h a ℓ κ u : M.Domain}
    (setup : Tg_setup_d hZFC p X) (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) p.δ)
    (root : M.mem p.e p.S) (aux : Tg_aux_d (ZFC.models_zf_l hZFC) p n h a) (data : Tg_aux_data_d a ℓ p.e κ u) :
    Formula.satisfies (⟨fun i => [p.ω, p.e, p.δ, p.S, p.ν, p.E, p.P, a, n, p.A].get i, fun _ => p.ω⟩ : Env M 10)
      tg_reset_result0_m := by
  let ρ : Env M 10 := ⟨fun i => [p.ω, p.e, p.δ, p.S, p.ν, p.E, p.P, a, n, p.A].get i, fun _ => p.ω⟩
  obtain ⟨v, seed, eq, hk, hb, hs, ht, hg, move, elastic, program, letters⟩ := setup.reset_input_l hZFC woodin root aux data
  apply (rt_exists_sat_l (n := 38) ρ tg_reset_body0_m).mpr
  refine ⟨v, (Formula.satisfies_conj_iff ..).mpr ⟨?_, ?_⟩⟩
  · apply (Formula.satisfies_rename ..).mpr
    exact (Formula.closed_env_l tg_seed0_m tg_seed0_closed_l
      (ρ := ⟨fun i => (rt_push_d ρ 38 v).bound ⟨i.val, by omega⟩, (rt_push_d ρ 38 v).free⟩)
      (η := ⟨v, fun _ => p.ω⟩) (funext (rt_push_new_l ρ v))).mpr seed
  · simp only [Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq (ZFC.models_zf_l hZFC).1,
      Formula.satisfies_exists_iff, tg_aux_data_sat_l (ZFC.models_zf_l hZFC).1, tg_ee_data_sat_l (ZFC.models_zf_l hZFC).1,
      tg_program_data_sat_l (ZFC.models_zf_l hZFC).1, tt_eval_cases_l, Definitional.Term.eval_weaken,
      Formula.satisfies_imp_iff, Formula.satisfies_mem_iff]
    exact ⟨eq 0, eq 1, eq 2, eq 3, eq 4, hk, hb, hs, ht, hg, ⟨ℓ, move⟩, elastic, program, letters⟩

def tg_reset_control_m {d} (p : Tg_params_d (Term d)) : Formula 1 d :=
  let q := p.map_l (fun t => t.weaken.weaken.weaken)
  set[d] ⟪∀ n h a, ⌜fun n h a => tg_aux_m q n h a⌝ₚ(n, h, a) →
    (∃ ℓ κ u, ⌜tg_aux_data_m⌝ₚ(a, ℓ, ⌜p.e⌝ₛ, κ, u)) →
    ⌜tg_reset_result_m⌝ₚ
      (⌜p.ω⌝ₛ, ⌜p.e⌝ₛ, ⌜p.δ⌝ₛ, ⌜p.S⌝ₛ, ⌜p.ν⌝ₛ, ⌜p.E⌝ₛ, ⌜p.P⌝ₛ, a, n, ⌜p.A⌝ₛ)⟫

theorem tg_reset_control_closed_l {d} (p : Tg_params_d (Term d)) (hp : p.closed_l) :
    (tg_reset_control_m p).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using hp
  rcases hp with ⟨hw, he, _, _, _, hd, hA, hS, hν, hE, hP, _⟩
  simp -implicitDefEqProofs [tg_reset_control_m, Definitional.Formula.FreeClosed, hw, he, hd, hA, hS, hν, hE, hP]
  exact tg_aux_closed_l _ _ _ _ hp' rfl rfl rfl

theorem tg_reset_control_l (hZFC : M.Models ZFC) {d} (ρ : Env M d) (p : Tg_params_d (Term d)) {X : M.Domain}
    (setup : Tg_setup_d hZFC (p.map_l (fun t => t.eval ρ)) X)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (p.δ.eval ρ))
    (root : M.mem (p.e.eval ρ) (p.S.eval ρ)) : Formula.satisfies ρ (tg_reset_control_m p) := by
  simp only [tg_reset_control_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, tg_aux_sat_l (ZFC.models_zf_l hZFC), tg_aux_data_sat_l (ZFC.models_zf_l hZFC).1,
    tg_reset_result_m, Formula.satisfies_bind, Tg_params_d.map_l, Definitional.Term.eval_weaken]
  intro n h a aux reset
  obtain ⟨ℓ, κ, u, data⟩ := reset
  have result := setup.reset_result_l hZFC woodin root aux data
  refine (Formula.closed_env_l tg_reset_result0_m tg_reset_result0_closed_l
    (ρ := ⟨fun i => [(p.ω.eval ρ), (p.e.eval ρ), (p.δ.eval ρ), (p.S.eval ρ), (p.ν.eval ρ), (p.E.eval ρ), (p.P.eval ρ), a, n, p.A.eval ρ].get i,
      fun _ => p.ω.eval ρ⟩) (η := _) ?_).mp result
  have eval (t : Term d) : t.eval ρ = t.weaken.weaken.weaken.eval (((ρ.push n).push h).push a) := by
    simp only [Definitional.Term.eval_weaken]
  funext i
  exact Fin.cases (eval p.ω) (Fin.cases (eval p.e) (Fin.cases (eval p.δ) (Fin.cases (eval p.S)
    (Fin.cases (eval p.ν) (Fin.cases (eval p.E) (Fin.cases (eval p.P) (Fin.cases rfl (Fin.cases rfl
      (Fin.cases (eval p.A) (fun j => Fin.elim0 j)))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原策略自动产生下一辅助走法

对全部内部有限历史，原策略的实际值仍在控制集合中，并满足原辅助走法规则。
此存在性质也进入控制记录，故反射层可直接取得实际下一走法。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

theorem Tg_rules_d.aux_l (hZF : M.Models ZF) {p : Tg_params_d M.Domain} {X F L G J σ R i n h : M.Domain}
    (rules : Tg_rules_d hZF p X F L J) (control : Cg_control_d (kp_pair_l (ZF.modelsKP hZF)) false p.ω p.e X F L G J σ R)
    (hi : M.mem i p.ω) (hn : M.mem n p.ω) (hh : M.mem h R) (fh : Fn0_d i X h)
    (div : M.IsOrdinalDivision (kp_pair_l (ZF.modelsKP hZF)) i p.c n p.e) :
    ∃ a t j, M.mem a X ∧ Rd_entry_d h a σ ∧ Fseq_end_d (kp_pair_l (ZF.modelsKP hZF)) p.ω t h a ∧
      M.mem j p.ω ∧ M.SuccessorOf j i ∧ Fn0_d j X t ∧ M.mem t R ∧
      M.IsOrdinalDivision (kp_pair_l (ZF.modelsKP hZF)) j p.c n p.a ∧ Tg_aux_d hZF p n h a ∧
      Tg_event_d (kp_pair_l (ZF.modelsKP hZF)) p.c n p.e t a := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨hc, _⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three hi
  have oc := rules.omega.members_areOrdinals (ZF.modelsKP hZF) p.c hc
  have ne₁ : p.e ≠ p.a := fun eq => rules.empty p.e (eq.symm ▸ rules.one.predecessor_mem)
  have ne₂ : p.e ≠ p.b := fun eq => rules.empty p.a (eq.symm ▸ rules.two.predecessor_mem)
  have turn : ¬ M.mem i J := fun h => ((rules.owner.read_l hZF (rules.omega.isOrdinal (ZF.modelsKP hZF))
    oc ⟨p.b, rules.three.predecessor_mem⟩ hi hn div).mp h).elim ne₁ (fun h => ne₂ h.1)
  have hG := ((control.positions h).mp hh).1
  obtain ⟨a, ha, value⟩ := control.strategy.2.1 h ((control.legal h).mp hG).1
  obtain ⟨j, t, hj, ft, endt⟩ := ZF.fseq_end_exists_l I hZF rules.omega hi (fn0_function_l (ZF.modelsKP hZF) fh) ha
  have next := control.step i h a t hi hh ha fh endt (Or.inr ⟨turn, value⟩)
  have check := ((rules.checks t).mp (control.legal.current_l ((control.positions t).mp next).1)).2
  have step := (tg_step_read_l hZF (rules.omega.members_areOrdinals (ZF.modelsKP hZF) i hi)
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
    (control : Cg_control_d (kp_pair_l (ZF.modelsKP hZF)) false (p.ω.eval ρ) (p.e.eval ρ)
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
    (rules : Tg_rules_d hZF p X F L J) (control : Cg_control_d (kp_pair_l (ZF.modelsKP hZF)) false p.ω p.e X F L G J σ R) :
    ∃ a h j, M.mem a X ∧ Rd_entry_d p.e a σ ∧ Fseq_end_d (kp_pair_l (ZF.modelsKP hZF)) p.ω h p.e a ∧
      M.mem j p.ω ∧ M.SuccessorOf j p.e ∧ Fn0_d j X h ∧ M.mem h R ∧
      M.IsOrdinalDivision (kp_pair_l (ZF.modelsKP hZF)) j p.c p.e p.a ∧ Tg_aux_d hZF p p.e p.e a ∧
      Tg_event_d (kp_pair_l (ZF.modelsKP hZF)) p.c p.e p.e h a ∧
      ∃ ℓ κ u, Tg_aux_data_d a ℓ p.e κ u := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have he := num_mem_l hZF.1 rules.omega (show Num_d 0 p.e from rules.empty)
  obtain ⟨hc, _⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three he
  have oc := rules.omega.members_areOrdinals (ZF.modelsKP hZF) p.c hc
  have ec := oc.transitive p.b rules.three.predecessor_mem p.e
    ((oc.mem rules.three.predecessor_mem).transitive p.a rules.two.predecessor_mem p.e rules.one.predecessor_mem)
  have div : M.IsOrdinalDivision I p.e p.c p.e p.e :=
    ⟨rules.omega.members_areOrdinals (ZF.modelsKP hZF) p.e he, ec, p.e,
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
    (control : Cg_control_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) false (p.ω.eval ρ) (p.e.eval ρ)
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
    (cg_control_m false p.ω p.e (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18))
    (.conj (tg_rules_m p (v 12) (v 13) (v 14) (v 16))
      (.conj (tg_aux_control_m p (v 12) (v 17) (v 18))
        (.conj (tg_reset_control_m p) (.conj (tg_start_control_m p (v 12) (v 17) (v 18))
          (.conj (tg_answer_control_m p (v 12) (v 18))
            (.conj (tg_digit_control_m p (v 12) (v 17) (v 18))
              (.conj (cg_rank_m p.ω (v 12) (v 18)) (tg_index_m p.c)))))))))

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
  have indexed : Formula.satisfies ρ (tg_index_m (.bound 4)) := by
    obtain ⟨hc, _⟩ := tg_clock_l hZF game.setup.omega game.setup.empty game.setup.one game.setup.two
      game.setup.three (num_mem_l hZF.1 game.setup.omega (show Num_d 0 p.e from game.setup.empty))
    exact (tg_index_sat_l I hZF.1 ..).mpr fun _ _ _ _ =>
      tg_index_unique_l hZF (game.setup.omega.members_areOrdinals (ZF.modelsKP hZF) p.c hc)
  have valid : Formula.satisfies ρ tg_control0_m := by
    apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨game.setup.tables_l hZFC ρ (.bound 0) (.bound 1) (.bound 5) (.bound 9) (.bound 10) (.bound 11)
      rfl rfl rfl rfl rfl rfl, ?_⟩
    apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨(cg_control_sat_l I hZF.1 false ..).mpr control, ?_⟩
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
                        (Formula.satisfies_conj_iff ..).mpr ⟨ranked, indexed⟩⟩⟩⟩⟩⟩⟩
  exact ⟨R, r, tuple, valid, (rt_record_sat_l hZF.1 _ _ _ tg_control0_closed_l).mpr ⟨v, tuple, valid⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 在搬运后的原查询表中读取新键

只解包控制记录中已经证明的全域性。返回字面表项和同一组查询证书，
可直接用来检查原规则 (7)；反射层无需满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hE : Extensional M)
include hE

theorem tg_control_query_l (ρ : Env M 19) (ε : Env M 5)
    (valid : Formula.satisfies ρ tg_control0_m) (hw : ε.bound 0 = ρ.bound 0)
    (hk : M.mem (ε.bound 1) (ρ.bound 5)) (request : Formula.satisfies ε tg_query_request0_m) :
    ∃ B U D r m b h q l n,
      Tg_query_data_d (ρ.bound 11) (ε.bound 1) (ε.bound 2) (ε.bound 3) (ε.bound 4) B U D r m b h q ∧
      M.SuccessorOf l (ε.bound 2) ∧ M.SuccessorOf n l ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, l, n, ε.bound 1, B, U, D, r, b, h].get i,
        ρ.free⟩ : Env M 11) tg_reply_language0_m ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, l, n, ε.bound 2, ε.bound 3, ε.bound 4, r, m, b, h, q].get i,
        ρ.free⟩ : Env M 12) tg_query_row0_m := by
  have tables := (Formula.satisfies_conj_iff ..).mp valid |>.1
  have total := (Formula.satisfies_conj_iff ..).mp tables |>.2
  have total := (Formula.satisfies_conj_iff ..).mp total |>.1
  simp only [tg_query_total_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, tg_query_request_m, Formula.satisfies_bind] at total
  have packet := total (ε.bound 1) hk (ε.bound 2) (ε.bound 3) (ε.bound 4) (by
    apply (Formula.closed_env_l tg_query_request0_m tg_query_request0_closed_l (ρ := ε) (η := _) ?_).mp request
    funext i
    exact Fin.cases hw (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i)
  simp only [Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, rd_quad_sat_l hE, rd_entry0_sat_l hE,
    tg_query_packet_m, Formula.satisfies_isSuccessor_iff, kpair0_sat_l hE,
    tg_reply_language_m, tg_query_base_m, Formula.satisfies_bind, Definitional.Term.eval_weaken] at packet
  obtain ⟨x, c, key, entry, l, n, B, U, D, r, m, b, h, q, a, v, hl, hn, row, codes, tail, language, _, _, base⟩ := packet
  refine ⟨B, U, D, r, m, b, h, q, l, n, ⟨x, c, a, v, key, entry, row, codes, tail⟩, hl, hn, ?_, ?_⟩
  · apply (Formula.closed_env_l tg_reply_language0_m tg_reply_language0_closed_l (ρ := _) (η := _) ?_).mp language
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun j => Fin.elim0 j))))))))))) i
  · apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨?_, (Formula.satisfies_conj_iff ..).mpr ⟨hl, hn⟩⟩
    apply (Formula.closed_env_l tg_query_base0_m tg_query_base0_closed_l (ρ := _) (η := _) ?_).mp base
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 已经落下的辅助走法及其原表项

前十九项为控制记录；其后依次为轮号、历史、走法、ℓ、t、κ、u、k、l、N、
B、U、D、四条弹性查询、程序长度与代码、七个程序槽位，末项为当前时刻。
此固定元数记录描述一次内部阶段；历史长度仍由模型自己的函数图给出。
同时保存产生这次走法的原前缀及全部辅助规则，供重置和继续分支共同读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_issued_slots_d {α : Type u} (v : Fin 46 → α) : Fin 7 → α :=
  Fin.cases (v 38) (Fin.cases (v 39) (Fin.cases (v 40)
    (Fin.cases (v 41) (Fin.cases (v 42) (Fin.cases (v 43) (fun _ => v 44))))))

/-- 回答的十九项坐标读取原请求的对应值；原模型使用实际图的原像关系。 -/
def Tg_request_d (r : M.Domain → M.Domain → Prop) (v : Fin 46 → M.Domain) (q : Fin 54 → M.Domain) : Prop :=
  ∀ i : Fin 19, r (q ([16, 17, 22, 23, 24, 36, 38, 47, 48, 49, 50, 51, 52, 53, 21, 31, 32, 34, 41].get i))
    (v ([0, 1, 26, 27, 28, 36, 37, 38, 39, 40, 41, 42, 43, 44, 24, 30, 31, 25, 23].get i))

def tg_issued_aux0_m : Formula 1 46 := .existsE (.conj
  (fseq_end_m (𝒞 := kpair_convention_l) (.bound 1) (.bound 21) .newest (.bound 22))
  (tg_aux_m (tg_control_params_d (fun i => (.bound (i.castAdd 27).succ : Term 47)))
    (.bound 20) .newest (.bound 22)))

theorem tg_issued_aux0_closed_l : tg_issued_aux0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_issued_aux0_m, Definitional.Formula.FreeClosed,
    tg_control_params_d]
  exact tg_aux_closed_l _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl

structure Tg_issued_d (I : kpair_convention_l.Interpretation M) (v : Fin 46 → M.Domain) : Prop where
  control : Formula.satisfies (⟨fun i => v (i.castAdd 27), fun _ => v 0⟩ : Env M 19) tg_control0_m
  round : M.mem (v 19) (v 0)
  time : M.mem (v 45) (v 0)
  history : Fn0_d (v 45) (v 12) (v 20)
  position : M.mem (v 20) (v 18)
  clock : M.IsOrdinalDivision I (v 45) (v 4) (v 19) (v 2)
  event : Tg_event_d I (v 4) (v 19) (v 1) (v 20) (v 21)
  move : Tg_aux_data_d (v 21) (v 22) (v 23) (v 24) (v 25)
  bound : M.mem (v 24) (v 5)
  labels : Fn0_d (v 26) (v 0) (v 23)
  first : M.SuccessorOf (v 27) (v 26)
  last : M.SuccessorOf (v 28) (v 27)
  elastic : Tg_ee_data_d (v 9) (v 24) (v 27) (v 29) (v 30) (v 31) ⟨v 32, v 33, v 34, v 35⟩
  program : Tg_program_data_d (v 10) (v 27) (v 36) (v 37) (tg_issued_slots_d v)
  auxiliary : Formula.satisfies (⟨v, fun _ => v 0⟩ : Env M 46) tg_issued_aux0_m

def tg_issued0_m : Formula 1 46 := .conj
  (tg_control0_m.rename (fun i => i.castAdd 27))
  (.conj (let v : Fin 46 → Term 46 := Term.bound
   set[46] ⟪⌜v 19⌝ₛ ∈ ⌜v 0⌝ₛ ∧ ⌜v 45⌝ₛ ∈ ⌜v 0⌝ₛ ∧ ⌜fn0_m⌝ₚ(⌜v 45⌝ₛ, ⌜v 12⌝ₛ, ⌜v 20⌝ₛ) ∧
    ⌜v 20⌝ₛ ∈ ⌜v 18⌝ₛ ∧ ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(⌜v 45⌝ₛ, ⌜v 4⌝ₛ, ⌜v 19⌝ₛ, ⌜v 2⌝ₛ) ∧
    ⌜tg_event_m⌝ₚ(⌜v 4⌝ₛ, ⌜v 19⌝ₛ, ⌜v 1⌝ₛ, ⌜v 20⌝ₛ, ⌜v 21⌝ₛ) ∧
    ⌜tg_aux_data_m⌝ₚ(⌜v 21⌝ₛ, ⌜v 22⌝ₛ, ⌜v 23⌝ₛ, ⌜v 24⌝ₛ, ⌜v 25⌝ₛ) ∧
    ⌜v 24⌝ₛ ∈ ⌜v 5⌝ₛ ∧
    ⌜fn0_m⌝ₚ(⌜v 26⌝ₛ, ⌜v 0⌝ₛ, ⌜v 23⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜v 27⌝ₛ, ⌜v 26⌝ₛ) ∧
    ⌜Formula.isSuccessor⌝ₚ(⌜v 28⌝ₛ, ⌜v 27⌝ₛ) ∧
    ⌜tg_ee_data_m⌝ₚ(⌜v 9⌝ₛ, ⌜v 24⌝ₛ, ⌜v 27⌝ₛ, ⌜v 29⌝ₛ, ⌜v 30⌝ₛ, ⌜v 31⌝ₛ,
      ⌜v 32⌝ₛ, ⌜v 33⌝ₛ, ⌜v 34⌝ₛ, ⌜v 35⌝ₛ) ∧
    ⌜fun P n b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_program_data_m P n b z
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜v 10⌝ₛ, ⌜v 27⌝ₛ, ⌜v 36⌝ₛ, ⌜v 37⌝ₛ, ⌜v 38⌝ₛ, ⌜v 39⌝ₛ, ⌜v 40⌝ₛ,
        ⌜v 41⌝ₛ, ⌜v 42⌝ₛ, ⌜v 43⌝ₛ, ⌜v 44⌝ₛ)⟫) tg_issued_aux0_m)

theorem tg_issued0_closed_l : tg_issued0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_issued0_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ,
    tg_control0_closed_l, tg_issued_aux0_closed_l]

theorem tg_issued_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) (ρ : Env M 46) :
    Formula.satisfies ρ tg_issued0_m ↔ Tg_issued_d I ρ.bound := by
  simp only [tg_issued0_m, Formula.satisfies_conj_iff, Formula.satisfies_rename,
    Formula.satisfies_mem_iff, fn0_sat_l hE, Formula.satisfies_isOrdinalDivision_iff I hE,
    tg_event_sat_l I hE, tg_aux_data_sat_l hE, Formula.satisfies_isSuccessor_iff,
    tg_ee_data_sat_l hE, tg_program_data_sat_l hE]
  have head := Formula.closed_env_l tg_control0_m tg_control0_closed_l
    (ρ := ρ.reindex (fun i => i.castAdd 27))
    (η := ⟨fun i => ρ.bound (i.castAdd 27), fun _ => ρ.bound 0⟩) rfl
  have aux := Formula.closed_env_l tg_issued_aux0_m tg_issued_aux0_closed_l
    (ρ := ρ) (η := ⟨ρ.bound, fun _ => ρ.bound 0⟩) rfl
  exact ⟨fun ⟨a, ⟨b, c, d, e, f, g, h, i, j, k, l, m, n⟩, o⟩ =>
      ⟨head.mp a, b, c, d, e, f, g, h, i, j, k, l, m, n, aux.mp o⟩,
    fun h => ⟨head.mpr h.control, ⟨h.round, h.time, h.history, h.position, h.clock,
      h.event, h.move, h.bound, h.labels, h.first, h.last, h.elastic, h.program⟩, aux.mpr h.auxiliary⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原首轮直接产生可搬运的阶段记录 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_issued_start_env_d (ρ : Env M 19) (ε : Env M 38) (a h ℓ j : M.Domain) : Env M 46 :=
  ⟨fun i => Fin.addCases (motive := fun _ => M.Domain) ρ.bound (fun i : Fin 27 => [ρ.bound 1, h, a, ℓ, ε.bound 25, ε.bound 5, ε.bound 18,
    ε.bound 6, ε.bound 7, ε.bound 8, ε.bound 14, ε.bound 15, ε.bound 16,
    ε.bound 27, ε.bound 28, ε.bound 29, ε.bound 30, ε.bound 20, ε.bound 22,
    ε.bound 31, ε.bound 32, ε.bound 33, ε.bound 34, ε.bound 35, ε.bound 36, ε.bound 37, j].get i) i, ρ.free⟩

theorem tg_issued_start_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (ρ : Env M 19) (ε : Env M 38) (a h ℓ j : M.Domain)
    (control : Formula.satisfies ρ tg_control0_m) (time : M.mem j (ρ.bound 0))
    (history : Fn0_d j (ρ.bound 12) h) (position : M.mem h (ρ.bound 18))
    (clock : M.IsOrdinalDivision I j (ρ.bound 4) (ρ.bound 1) (ρ.bound 2))
    (event : Tg_event_d I (ρ.bound 4) (ρ.bound 1) (ρ.bound 1) h a)
    (endt : Fseq_end_d I (ρ.bound 0) h (ρ.bound 1) a)
    (aux : Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 2, ρ.bound 3, ρ.bound 4,
      ρ.bound 5, ρ.bound 6, ρ.bound 7, ρ.bound 8, ρ.bound 9, ρ.bound 10, ρ.bound 11,
      ρ.bound 1, ρ.bound 1, a].get i, ρ.free⟩ : Env M 15) tg_aux0_m)
    (seed : Formula.satisfies ε tg_seed0_m) (hw : ε.bound 0 = ρ.bound 0) (he : ε.bound 1 = ρ.bound 1)
    (hd : ε.bound 2 = ρ.bound 5)
    (hk : ε.bound 6 = ρ.bound 1) (ht : ε.bound 25 = ρ.bound 1)
    (move : Tg_aux_data_d a ℓ (ε.bound 25) (ε.bound 5) (ε.bound 18))
    (elastic : Tg_ee_data_d (ρ.bound 9) (ε.bound 5) (ε.bound 7) (ε.bound 14) (ε.bound 15) (ε.bound 16)
      ⟨ε.bound 27, ε.bound 28, ε.bound 29, ε.bound 30⟩)
    (program : Tg_program_data_d (ρ.bound 10) (ε.bound 7) (ε.bound 20) (ε.bound 22)
      (Fin.cases (ε.bound 31) (Fin.cases (ε.bound 32) (Fin.cases (ε.bound 33)
        (Fin.cases (ε.bound 34) (Fin.cases (ε.bound 35) (Fin.cases (ε.bound 36) (fun _ => ε.bound 37)))))))) :
    Formula.satisfies (tg_issued_start_env_d ρ ε a h ℓ j) tg_issued0_m := by
  apply (tg_issued_sat_l I hE _).mpr
  have head : Formula.satisfies
      (⟨fun i => (tg_issued_start_env_d ρ ε a h ℓ j).bound (i.castAdd 27),
        fun _ => (tg_issued_start_env_d ρ ε a h ℓ j).bound 0⟩ : Env M 19) tg_control0_m := by
    apply (Formula.closed_env_l tg_control0_m tg_control0_closed_l (ρ := ρ) (η := _) ?_).mp control
    funext i
    simp only [tg_issued_start_env_d, Fin.addCases_left]
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isSuccessor_iff] at seed
  obtain ⟨_, empty, hn, _, _, _, below, first, last, _⟩ := seed
  have empty : ∀ x, ¬ M.mem x (ρ.bound 1) := he ▸ empty
  have labels : Fn0_d (ε.bound 6) (ρ.bound 0) (ε.bound 25) := by
    have zero : Fn0_d (ρ.bound 1) (ρ.bound 0) (ρ.bound 1) :=
      ⟨fun x hx => (empty x hx).elim, fun x hx => (empty x hx).elim, fun x hx => (empty x hx).elim⟩
    exact hk.symm ▸ ht.symm ▸ zero
  have round : M.mem (ρ.bound 1) (ρ.bound 0) := hw ▸ he ▸ hn
  have bound : M.mem (ε.bound 5) (ρ.bound 5) := hd ▸ below
  refine ⟨head, round, time, history, position, clock, event, move, bound, labels, first, last, elastic, program, ?_⟩
  simp only [tg_issued_aux0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fseq_end_sat_l I hE, tg_aux_m, Formula.satisfies_bind]
  refine ⟨ρ.bound 1, endt, ?_⟩
  apply (Formula.closed_env_l tg_aux0_m tg_aux0_closed_l (ρ := _) (η := _) ?_).mp aux
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从控制记录读取真实首轮输入

只解包同一条有限公式的量词。此处仅需传递层已有的外延性与配对解释，
不对反射层假定 ZF；获胜策略、开局合法性和重置构造均已由原模型给出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
include hE

theorem tg_control_start_l (ρ : Env M 19) (valid : Formula.satisfies ρ tg_control0_m) :
    ∃ a h j, M.mem a (ρ.bound 12) ∧ Rd_entry_d (ρ.bound 1) a (ρ.bound 17) ∧
      Fseq_end_d I (ρ.bound 0) h (ρ.bound 1) a ∧ M.mem j (ρ.bound 0) ∧
      M.SuccessorOf j (ρ.bound 1) ∧ Fn0_d j (ρ.bound 12) h ∧ M.mem h (ρ.bound 18) ∧
      M.IsOrdinalDivision I j (ρ.bound 4) (ρ.bound 1) (ρ.bound 2) ∧
      Tg_event_d I (ρ.bound 4) (ρ.bound 1) (ρ.bound 1) h a ∧
      ∃ v : Fin 38 → M.Domain, Formula.satisfies (⟨v, ρ.free⟩ : Env M 38) tg_seed0_m ∧
        v 0 = ρ.bound 0 ∧ v 1 = ρ.bound 1 ∧ v 2 = ρ.bound 5 ∧ v 3 = ρ.bound 7 ∧ v 4 = ρ.bound 8 ∧
        v 6 = ρ.bound 1 ∧ v 23 = v 5 ∧ v 24 = ρ.bound 1 ∧ v 25 = ρ.bound 1 ∧ v 26 = ρ.bound 1 ∧
        (∃ ℓ, Tg_aux_data_d a ℓ (v 25) (v 5) (v 18)) ∧
        Tg_ee_data_d (ρ.bound 9) (v 5) (v 7) (v 14) (v 15) (v 16) ⟨v 27, v 28, v 29, v 30⟩ ∧
        Tg_program_data_d (ρ.bound 10) (v 7) (v 20) (v 22) (Fin.cases (v 31) (Fin.cases (v 32) (Fin.cases (v 33)
          (Fin.cases (v 34) (Fin.cases (v 35) (Fin.cases (v 36) (fun _ => v 37))))))) ∧
        M.mem (ρ.bound 6) (v 14) ∧ ∃ ℓ,
          Formula.satisfies (tg_issued_start_env_d ρ ⟨v, ρ.free⟩ a h ℓ j) tg_issued0_m := by
  have control := valid
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at valid
  have start := valid.2.2.2.2.2.1
  simp only [tg_start_control_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rd_entry0_sat_l hE, fseq_end_sat_l I hE, Formula.satisfies_isSuccessor_iff,
    Formula.satisfies_isOrdinalDivision_iff I hE,
    fn0_sat_l hE, tg_event_sat_l I hE, tg_reset_result_m, Formula.satisfies_bind, Definitional.Term.eval_weaken] at start
  obtain ⟨a, h, j, ha, value, endt, hj, succ, fn, next, clock, aux, event, prepared⟩ := start
  let ε : Env M 10 := ⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 5, ρ.bound 7, ρ.bound 8, ρ.bound 9, ρ.bound 10,
    a, ρ.bound 1, ρ.bound 6].get i, ρ.free⟩
  have prepared : Formula.satisfies ε tg_reset_result0_m := by
    apply (Formula.closed_env_l tg_reset_result0_m tg_reset_result0_closed_l (ρ := _) (η := ε) ?_).mp prepared
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))))) i
  obtain ⟨v, body⟩ := (rt_exists_sat_l (n := 38) ε tg_reset_body0_m).mp prepared
  obtain ⟨seed, links⟩ := (Formula.satisfies_conj_iff ..).mp body
  have seed : Formula.satisfies (⟨v, ρ.free⟩ : Env M 38) tg_seed0_m :=
    (Formula.closed_env_l tg_seed0_m tg_seed0_closed_l (ρ := _) (η := ⟨v, ρ.free⟩)
      (funext (rt_push_new_l ε v))).mp ((Formula.satisfies_rename ..).mp seed)
  simp only [Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_exists_iff, tg_aux_data_sat_l hE, tg_ee_data_sat_l hE, tg_program_data_sat_l hE, tt_eval_cases_l,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken] at links
  obtain ⟨hw, he, hd, hS, hν, hk, hb, hs, ht, hg, move, elastic, program, letters⟩ := links
  obtain ⟨ℓ, move⟩ := move
  refine ⟨a, h, j, ha, value, endt, hj, succ, fn, next, clock, event, v, seed,
    hw, he, hd, hS, hν, hk, hb, hs, ht, hg, ⟨ℓ, move⟩, elastic, program, letters rfl,
    ℓ, tg_issued_start_l I hE ρ ⟨v, ρ.free⟩ a h ℓ j control hj fn next clock event endt ?_ seed hw he hd hk ht move elastic program⟩
  simp only [tg_aux_m, Formula.satisfies_bind] at aux
  apply (Formula.closed_env_l tg_aux0_m tg_aux0_closed_l (ρ := _) (η := _) ?_).mp aux
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 三阶段控制位置的同一有限记录

前十九项为控制参数，后三项为内部轮号、历史图和时刻。阶段只有固定的
0、1、2 三种语法形状；轮号及历史均取遍模型自己的 ω。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_position_env_d (ρ : Env M 19) (n h i : M.Domain) : Env M 22 :=
  ⟨fun j => Fin.addCases (motive := fun _ => M.Domain) ρ.bound (fun j : Fin 3 => [n, h, i].get j) j, ρ.free⟩

structure Tg_position_d (I : kpair_convention_l.Interpretation M) (r : Fin 3) (v : Fin 22 → M.Domain) : Prop where
  control : Formula.satisfies (⟨fun i => v (i.castAdd 3), fun _ => v 0⟩ : Env M 19) tg_control0_m
  round : M.mem (v 19) (v 0)
  time : M.mem (v 21) (v 0)
  history : Fn0_d (v 21) (v 12) (v 20)
  position : M.mem (v 20) (v 18)
  clock : M.IsOrdinalDivision I (v 21) (v 4) (v 19) (v ([1, 2, 3].get r))

def tg_position0_m (r : Fin 3) : Formula 1 22 := .conj
  (tg_control0_m.rename (fun i => i.castAdd 3))
  (let v : Fin 22 → Term 22 := Term.bound
   set[22] ⟪⌜v 19⌝ₛ ∈ ⌜v 0⌝ₛ ∧ ⌜v 21⌝ₛ ∈ ⌜v 0⌝ₛ ∧ ⌜fn0_m⌝ₚ(⌜v 21⌝ₛ, ⌜v 12⌝ₛ, ⌜v 20⌝ₛ) ∧
     ⌜v 20⌝ₛ ∈ ⌜v 18⌝ₛ ∧
     ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(⌜v 21⌝ₛ, ⌜v 4⌝ₛ, ⌜v 19⌝ₛ, ⌜v ([1, 2, 3].get r)⌝ₛ)⟫)

theorem tg_position0_closed_l (r : Fin 3) : (tg_position0_m r).FreeClosed := by
  simp -implicitDefEqProofs [tg_position0_m, Definitional.Formula.FreeClosed, tg_control0_closed_l]

theorem tg_position_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (r : Fin 3) (ρ : Env M 22) : Formula.satisfies ρ (tg_position0_m r) ↔ Tg_position_d I r ρ.bound := by
  simp only [tg_position0_m, Formula.satisfies_conj_iff, Formula.satisfies_rename,
    Formula.satisfies_mem_iff, fn0_sat_l hE, Formula.satisfies_isOrdinalDivision_iff I hE]
  have head := Formula.closed_env_l tg_control0_m tg_control0_closed_l
    (ρ := ρ.reindex (fun i => i.castAdd 3))
    (η := ⟨fun i => ρ.bound (i.castAdd 3), fun _ => ρ.bound 0⟩) rfl
  exact ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨head.mp a, b, c, d, e, f⟩,
    fun h => ⟨head.mpr h.control, h.round, h.time, h.history, h.position, h.clock⟩⟩

/-- 换入新的轮号、历史和时刻，保留同一整份控制参数。 -/
theorem tg_position_build_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (r : Fin 3) (ρ : Env M 19) (n h i : M.Domain) (control : Formula.satisfies ρ tg_control0_m)
    (round : M.mem n (ρ.bound 0)) (time : M.mem i (ρ.bound 0)) (history : Fn0_d i (ρ.bound 12) h)
    (position : M.mem h (ρ.bound 18))
    (clock : M.IsOrdinalDivision I i (ρ.bound 4) n (ρ.bound ([1, 2, 3].get r))) :
    Formula.satisfies (tg_position_env_d ρ n h i) (tg_position0_m r) := by
  apply (tg_position_sat_l I hE _ _).mpr
  have head : Formula.satisfies
      (⟨fun k => (tg_position_env_d ρ n h i).bound (k.castAdd 3),
        fun _ => (tg_position_env_d ρ n h i).bound 0⟩ : Env M 19) tg_control0_m := by
    apply (Formula.closed_env_l tg_control0_m tg_control0_closed_l (ρ := ρ) (η := _) ?_).mp control
    funext k
    simp only [tg_position_env_d, Fin.addCases_left]
  have phase : (tg_position_env_d ρ n h i).bound ([1, 2, 3].get r) = ρ.bound ([1, 2, 3].get r) := by
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a))) r
  exact ⟨head, round, time, history, position, phase.symm ▸ clock⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意轮的原策略实际给出下一份辅助记录

在阶段零读取同一个策略值，按原规则解包辅助走法，再从原程序表取得对应
内部元数的全部代码。空根与非空继续均由原合法历史检查，不把零轮专用的
重置输入推广成附加前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
include I hE

theorem tg_position_issue_l (ρ : Env M 22) (valid : Formula.satisfies ρ (tg_position0_m 0)) :
    ∃ θ : Env M 46, (∀ i : Fin 19, θ.bound (i.castAdd 27) = ρ.bound (i.castAdd 3)) ∧
      θ.bound 19 = ρ.bound 19 ∧ Formula.satisfies θ tg_issued0_m ∧
      Rd_entry_d (ρ.bound 20) (θ.bound 21) (ρ.bound 17) ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, θ.bound 20, ρ.bound 20, θ.bound 21].get i,
        fun _ => θ.bound 21⟩ : Env M 4)
        (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) := by
  have state := (tg_position_sat_l I hE 0 ρ).mp valid
  have control := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have next := control.2.2.2.1
  simp only [tg_aux_control_m, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    fn0_sat_l hE, Formula.satisfies_isOrdinalDivision_iff I hE,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    rd_entry0_sat_l hE, fseq_end_sat_l I hE, Formula.satisfies_isSuccessor_iff, tg_event_sat_l I hE] at next
  obtain ⟨a, h, j, _, value, endt, hj, _, fn, position, clock, aux, event⟩ :=
    next (ρ.bound 21) state.time (ρ.bound 19) state.round (ρ.bound 20) state.position state.history state.clock
  have original := aux
  simp only [tg_aux_m, Formula.satisfies_bind, tg_aux0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tg_aux_data_sat_l hE, Formula.satisfies_mem_iff, fn0_sat_l hE, Formula.satisfies_isSuccessor_iff,
    tg_ee_data_sat_l hE, Definitional.Term.eval_weaken] at aux
  obtain ⟨ℓ, t, κ, u, k, l, N, _, _, _, _, _, _, _, _, _, _, B, U, D, g₀, g₁, g₂, g₃,
    move, bound, labels, first, last, _, _, request, _, _, elastic, _⟩ := aux
  simp only [tg_query_request_m, Formula.satisfies_bind, tg_query_request0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at request
  have rules := control.2.2.1
  simp only [tg_rules_m, Formula.satisfies_conj_iff] at rules
  have omega : M.IsOmega (ρ.bound 0) := (Formula.satisfies_isOmega_iff ..).mp rules.1
  obtain ⟨l', succ, hl'⟩ := omega.1.2 k request.2.1
  have eq : l = l' := first.eq hE succ
  have hl : M.mem l (ρ.bound 0) := eq.symm ▸ hl'
  have tables := control.1
  simp only [tg_tables_m, Formula.satisfies_conj_iff] at tables
  have program := tables.1.2.2.1
  simp only [Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    tg_program_data_sat_l hE] at program
  obtain ⟨b, z, s₀, s₁, s₂, s₃, s₄, s₅, s₆, program⟩ := program l hl
  let θ : Env M 46 := ⟨fun i => Fin.addCases (motive := fun _ => M.Domain)
    (fun i : Fin 19 => ρ.bound (i.castAdd 3))
    (fun i : Fin 27 => [ρ.bound 19, h, a, ℓ, t, κ, u, k, l, N, B, U, D,
      g₀, g₁, g₂, g₃, b, z, s₀, s₁, s₂, s₃, s₄, s₅, s₆, j].get i) i, ρ.free⟩
  have head : Formula.satisfies
      (⟨fun i => θ.bound (i.castAdd 27), fun _ => θ.bound 0⟩ : Env M 19) tg_control0_m := by
    apply (Formula.closed_env_l tg_control0_m tg_control0_closed_l (ρ := _) (η := _) ?_).mp state.control
    funext i
    simp only [θ, Fin.addCases_left]
  refine ⟨θ, (fun i => by simp only [θ, Fin.addCases_left]), rfl, ?_, value, (fseq_end_sat_l I hE ..).mpr endt⟩
  apply (tg_issued_sat_l I hE θ).mpr
  refine ⟨head, state.round, hj, fn, position, clock, event, move, bound, labels, first, last, elastic, program, ?_⟩
  simp only [tg_issued_aux0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fseq_end_sat_l I hE, tg_aux_m, Formula.satisfies_bind]
  refine ⟨ρ.bound 20, endt, ?_⟩
  simp only [tg_aux_m, Formula.satisfies_bind] at original
  apply (Formula.closed_env_l tg_aux0_m tg_aux0_closed_l (ρ := _) (η := _) ?_).mp original
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意内部轮号上的实数落子与下一轮

偶数轮使用给定的对手字母，奇数轮读取原 II 策略。两种情况都在同一
反射层内追加历史并增加轮号，随后读取原策略的下一辅助走法和原程序表，
返回阶段零位置及下一份完整辅助记录。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
include I hE

theorem tg_position_digit_event_l (ρ : Env M 22) (valid : Formula.satisfies ρ (tg_position0_m 2))
    {t h v a : M.Domain} (digit : Fseq_end_d I (ρ.bound 0) t (ρ.bound 20) v)
    (aux : Fseq_end_d I (ρ.bound 0) h t a) : Tg_event_d I (ρ.bound 4) (ρ.bound 19) (ρ.bound 3) h v := by
  have state := (tg_position_sat_l I hE 2 ρ).mp valid
  obtain ⟨n,m,endt⟩ := digit
  have ent (a b f : M.Domain) : M.PairMember I a b f ↔ Rd_entry_d a b f := by
    apply exists_congr
    intro p
    let η : Env M 3 := ⟨fun i => [p,a,b].get i,fun _ => p⟩
    exact and_congr ((I.realizes η (.bound 0) (.bound 1) (.bound 2)).symm.trans
      (kpair_sat_l M hE η (.bound 0) (.bound 1) (.bound 2))) Iff.rfl
  have domain : M.IsDomainOf I (ρ.bound 21) (ρ.bound 20) := fun i =>
    ⟨fun hi => (state.history.2.1 i hi).imp fun _ h => (ent ..).mpr h.2,
      fun ⟨v,hv⟩ => (state.history.bound_l ((ent ..).mp hv)).1⟩
  have eq := endt.prefix_sequence.2.2.2.eq hE domain
  exact (show Tg_event_d I (ρ.bound 4) (ρ.bound 19) (ρ.bound 3) t v from
    ⟨ρ.bound 21,state.clock,eq ▸ (ent ..).mp endt.last_value⟩).end_l aux

theorem tg_position_next_l (ρ : Env M 22) (valid : Formula.satisfies ρ (tg_position0_m 2))
    (x : M.Domain) (hx : M.mem x (ρ.bound 6)) :
    ∃ v t j n, M.mem v (ρ.bound 6) ∧
      (Formula.satisfies ρ (gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) → v = x) ∧
      (¬ Formula.satisfies ρ (gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) →
        Rd_entry_d (ρ.bound 20) v (ρ.bound 17)) ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, t, ρ.bound 20, v].get i, fun _ => v⟩ : Env M 4)
        (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
      M.SuccessorOf n (ρ.bound 19) ∧
      Formula.satisfies (tg_position_env_d
        ⟨fun i => ρ.bound (i.castAdd 3), fun _ => ρ.bound 0⟩ n t j) (tg_position0_m 0) ∧
      ∃ θ : Env M 46, (∀ i : Fin 19, θ.bound (i.castAdd 27) = ρ.bound (i.castAdd 3)) ∧
        θ.bound 19 = n ∧ Formula.satisfies θ tg_issued0_m ∧ Rd_entry_d t (θ.bound 21) (ρ.bound 17) ∧
        Formula.satisfies (⟨fun i => [ρ.bound 0, θ.bound 20, t, θ.bound 21].get i,
          fun _ => θ.bound 21⟩ : Env M 4)
          (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) := by
  classical
  have state := (tg_position_sat_l I hE 2 ρ).mp valid
  have control := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have digit := control.2.2.2.2.2.2.2.1
  simp only [tg_digit_control_m, tg_digit_end_m, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_conj_iff, fn0_sat_l hE,
    Formula.satisfies_isOrdinalDivision_iff I hE, gm_even_sat_l I hE, Formula.satisfies_neg_iff,
    Formula.satisfies_exists_iff, fseq_end_sat_l I hE, Formula.satisfies_mem_iff,
    Formula.satisfies_isSuccessor_iff, tg_event_sat_l I hE, rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken] at digit
  have step := digit (ρ.bound 21) state.time (ρ.bound 19) state.round (ρ.bound 20)
    state.position state.history state.clock
  let χ : Env M 19 := ⟨fun i => ρ.bound (i.castAdd 3), fun _ => ρ.bound 0⟩
  have issue (n t j : M.Domain) (next : Formula.satisfies (tg_position_env_d χ n t j) (tg_position0_m 0)) :
      ∃ θ : Env M 46, (∀ i : Fin 19, θ.bound (i.castAdd 27) = ρ.bound (i.castAdd 3)) ∧
        θ.bound 19 = n ∧ Formula.satisfies θ tg_issued0_m ∧ Rd_entry_d t (θ.bound 21) (ρ.bound 17) ∧
        Formula.satisfies (⟨fun i => [ρ.bound 0, θ.bound 20, t, θ.bound 21].get i,
          fun _ => θ.bound 21⟩ : Env M 4)
          (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) := by
    obtain ⟨θ, head, num, valid, value, hist⟩ := tg_position_issue_l I hE _ next
    have left (i : Fin 19) : (tg_position_env_d χ n t j).bound (i.castAdd 3) = χ.bound i := by
      simp only [tg_position_env_d, Fin.addCases_left]
    have right (i : Fin 3) : (tg_position_env_d χ n t j).bound (Fin.natAdd 19 i) = [n, t, j].get i := by
      simp only [tg_position_env_d, Fin.addCases_right]
    have e₀ : (tg_position_env_d χ n t j).bound 0 = ρ.bound 0 := left 0
    have e₁₇ : (tg_position_env_d χ n t j).bound 17 = ρ.bound 17 := left 17
    have e₁₉ : (tg_position_env_d χ n t j).bound 19 = n := right 0
    have e₂₀ : (tg_position_env_d χ n t j).bound 20 = t := right 1
    refine ⟨θ, fun i => (head i).trans (left i), num.trans e₁₉, valid, e₂₀ ▸ e₁₇ ▸ value, ?_⟩
    apply (Formula.closed_env_l _ (by simp -implicitDefEqProofs) (ρ := _) (η := _) ?_).mp hist
    funext i
    exact Fin.cases e₀ (Fin.cases rfl (Fin.cases e₂₀ (Fin.cases rfl (fun a => Fin.elim0 a)))) i
  by_cases even : Gm_even_d I (ρ.bound 0) (ρ.bound 19)
  · obtain ⟨t, j, n, endt, hj, hn, _, succ, fn, position, clock, _⟩ := step.1 even x hx
    have next := tg_position_build_l I hE 0 χ n t j state.control hn hj fn position clock
    exact ⟨x, t, j, n, hx, fun _ => rfl, fun no => (no ((gm_even_sat_l I hE ..).mpr even)).elim,
      (fseq_end_sat_l I hE ..).mpr endt, succ,
      next, issue n t j next⟩
  · obtain ⟨v, hv, value, t, j, n, endt, hj, hn, _, succ, fn, position, clock, _⟩ := step.2 even
    have next := tg_position_build_l I hE 0 χ n t j state.control hn hj fn position clock
    exact ⟨v, t, j, n, hv, fun yes => (even ((gm_even_sat_l I hE ..).mp yes)).elim, fun _ => value,
      (fseq_end_sat_l I hE ..).mpr endt, succ,
      next, issue n t j next⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 合法尝试树的秩在传递反射层中绝对读取

原控制记录已经包含实际秩函数的存在性。取出层内见证后，只读取其 Δ₀
图证书，故得到背景中的真秩下降关系，不对反射层附加 ZF 或 DC。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) (hKP : M.Models KP)
variable {C : M.Domain} (trans : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
  (ρ : Env (rt_model_l C nc) 19)
include trans

include hKP in
theorem tg_control_rank_l (valid : Formula.satisfies ρ tg_control0_m) :
    ∃ α F, M.mem α C ∧ M.mem F C ∧ Cg_rank_d (ρ.bound 0).val (ρ.bound 12).val (ρ.bound 18).val α F := by
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at valid
  have rank := valid.2.2.2.2.2.2.2.2.1
  simp only [cg_rank_m, Formula.satisfies_exists_iff] at rank
  obtain ⟨α, F, rank⟩ := rank
  have lifted := (rt_model_delta_l trans nc (cg_rank0_delta_l ..) ((ρ.push α).push F)).mp rank
  exact ⟨α.val, F.val, α.property, F.property, (cg_rank0_sat_l hKP ..).mp lifted⟩

include hZF in
/-- 传递目标中的原控制树不能含背景内部的无限合法延长链。 -/
theorem tg_control_no_chain_l {ω H : M.Domain} (hω : M.IsOmega ω)
    (hw : (ρ.bound 0).val = ω) (valid : Formula.satisfies ρ tg_control0_m)
    (fn : Fn0_d ω (ρ.bound 18).val H) :
    ¬ (∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s H → Rd_entry_d j t H →
      Tb_step_d ω (ρ.bound 12).val s t) := by
  obtain ⟨_, _, _, _, rank⟩ := tg_control_rank_l (ZF.modelsKP hZF) trans nc ρ valid
  exact (hw ▸ rank).no_chain_l hZF hω fn

end YesMetaZFC.SetTheory.LargeCardinal
