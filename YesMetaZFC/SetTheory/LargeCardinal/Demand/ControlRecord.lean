import YesMetaZFC.SetTheory.LargeCardinal.Demand.Setup
import YesMetaZFC.SetTheory.LargeCardinal.Game.CatalogRead
import YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticNumericTransfer
import YesMetaZFC.Model.SetTheory.Types.SubtypeUp
import YesMetaZFC.SetTheory.LargeCardinal.Demand.SeparatedGame
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.SetTheory.Descriptive.Game.GameAttemptRank

/-! # 随 demanding 控制记录搬运的实际三表证书

原第一字母表 A 固定在公式参数中。查询行完整保存双池、精确元数和五条查询，
三张原表的读取、总性与函数性均由开局实际构造产生。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def td_query_total_m {d} (ω e δ A Q : Term d) : Formula 1 d := set[d] ⟪
  ∀ κ ∈ ⌜δ⌝ₛ, ∀ k s, ⌜tg_query_request_m⌝ₚ(⌜ω⌝ₛ,κ,k,s,⌜A⌝ₛ) →
    ∃ x c, ⌜rd_quad_m⌝ₚ(x,κ,k,s,⌜A⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(x,c,⌜Q⌝ₛ) ∧
      ⌜td_query_packet_m⌝ₚ(⌜ω⌝ₛ,⌜e⌝ₛ,κ,k,s,⌜A⌝ₛ,c)⟫
derive_free_closed td_query_total_m

theorem Td_setup_d.query_total_l (hZFC : M.Models ZFC) {p : Tg_params_d M.Domain} {X : M.Domain}
    (setup : Td_setup_d hZFC p X) {d} (ρ : Env M d) (ω e δ A Q : Term d)
    (hw : ω.eval ρ = p.ω) (he : e.eval ρ = p.e) (hd : δ.eval ρ = p.δ)
    (hA : A.eval ρ = p.A) (hQ : Q.eval ρ = p.Q) :
    Formula.satisfies ρ (td_query_total_m ω e δ A Q) := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [td_query_total_m,Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff,Formula.satisfies_exists_iff,tg_query_request_sat_l hZF,
    Formula.satisfies_conj_iff,rd_quad_sat_l hZF.1,rd_entry0_sat_l hZF.1,
    td_query_packet_sat_l hZF,Definitional.Term.eval_weaken,hw,he,hd,hA,hQ]
  intro κ hk k s request
  exact setup.queries.get_l hZFC setup.limit setup.above setup.rank hk request

def td_tables_m {d} (ω e δ A E P Q : Term d) : Formula 1 d := .conj (set[d] ⟪
  (∀ κ ∈ ⌜δ⌝ₛ, ∀ n ∈ ⌜ω⌝ₛ, ∀ B U D g h i z,
    ⌜Formula.isLimitOrdinal⌝ₚ(κ) → ⌜tg_ee_data_m⌝ₚ(⌜E⌝ₛ,κ,n,B,U,D,g,h,i,z) →
    ⌜ee_language_m⌝ₚ(⌜ω⌝ₛ,κ,n,B,U,D,g,h,i,z)) ∧
  (∀ n b z s₀ s₁ s₂ s₃ s₄ s₅ s₆,
    ⌜fun P n b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_program_data_m P n b z
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜P⌝ₛ,n,b,z,s₀,s₁,s₂,s₃,s₄,s₅,s₆) → ∃ a,
    ⌜fun ω n b a z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => ts_program_m ω n b a z
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜ω⌝ₛ,n,b,a,z,s₀,s₁,s₂,s₃,s₄,s₅,s₆)) ∧
  (∀ n ∈ ⌜ω⌝ₛ, ∃ b z s₀ s₁ s₂ s₃ s₄ s₅ s₆,
    ⌜fun P n b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_program_data_m P n b z
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜P⌝ₛ,n,b,z,s₀,s₁,s₂,s₃,s₄,s₅,s₆)) ∧
  (∀ κ ∈ ⌜δ⌝ₛ, ∀ k s B U Du Dw pn pm pp pb ph,
    ⌜tg_query_request_m⌝ₚ(⌜ω⌝ₛ,κ,k,s,⌜A⌝ₛ) →
    ⌜td_query_data_m⌝ₚ(⌜Q⌝ₛ,κ,k,s,⌜A⌝ₛ,B,U,Du,Dw,pn,pm,pp,pb,ph) → ∃ d q n m,
    ⌜td_arity_m⌝ₚ(k,d,q,n,m) ∧ ⌜(v_m kpair_convention_l)⌝ₚ(κ,B) ∧
    ⌜tt_constants0_m⌝ₚ(κ,B,U) ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ,n,U,Du) ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ,m,U,Dw) ∧
    ⌜td_node_query_m⌝ₚ(⌜ω⌝ₛ,⌜e⌝ₛ,n,q,U,Du,s,k,pn) ∧
    ⌜tg_max_query_m⌝ₚ(⌜ω⌝ₛ,q,n,U,Du,pm) ∧
    ⌜td_pending_query_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜e⌝ₛ,m,q,U,Dw,k,pp) ∧
    ⌜tg_bound_query_m⌝ₚ(⌜ω⌝ₛ,⌜e⌝ₛ,n,m,U,Dw,pb) ∧ ⌜tg_height_query_m⌝ₚ(⌜ω⌝ₛ,n,m,U,Dw,ph) ∧
    ⌜td_reply_base_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜e⌝ₛ,k,q,n,m,pp,pb,ph))⟫)
  (.conj (td_query_total_m ω e δ A Q)
    (.conj (set[d] ⟪∀ κ ∈ ⌜δ⌝ₛ, ∀ n ∈ ⌜ω⌝ₛ, ⌜Formula.isLimitOrdinal⌝ₚ(κ) →
      ∃ B U D g h i z, ⌜tg_ee_data_m⌝ₚ(⌜E⌝ₛ,κ,n,B,U,D,g,h,i,z) ∧
        ⌜ee_language_m⌝ₚ(⌜ω⌝ₛ,κ,n,B,U,D,g,h,i,z)⟫)
      (.conj (Formula.isFunction kpair_convention_l E)
        (.conj (Formula.isFunction kpair_convention_l P) (Formula.isFunction kpair_convention_l Q)))))

@[simp] theorem td_tables_closed_l {d} (ω e δ A E P Q : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (hd : δ.freeSupport = [])
    (hA : A.freeSupport = []) (hE : E.freeSupport = []) (hP : P.freeSupport = []) (hQ : Q.freeSupport = []) :
    (td_tables_m ω e δ A E P Q).FreeClosed := by
  simp -implicitDefEqProofs [td_tables_m,Definitional.Formula.FreeClosed,hw,he,hd,hA,hE,hP,hQ,
    Fin.forall_fin_succ]

/-- 每个读取及总性分量均由同一 setup 的原表实际给出。 -/
theorem Td_setup_d.tables_l (hZFC : M.Models ZFC) {p : Tg_params_d M.Domain} {X : M.Domain}
    (setup : Td_setup_d hZFC p X) {d} (ρ : Env M d) (ω e δ A E P Q : Term d)
    (hw : ω.eval ρ = p.ω) (he : e.eval ρ = p.e) (hd : δ.eval ρ = p.δ) (hA : A.eval ρ = p.A)
    (hE : E.eval ρ = p.E) (hP : P.eval ρ = p.P) (hQ : Q.eval ρ = p.Q) :
    Formula.satisfies ρ (td_tables_m ω e δ A E P Q) := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [td_tables_m,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Formula.satisfies_exists_iff,
    Formula.satisfies_isLimitOrdinal_iff,tg_ee_data_sat_l hZF.1,ee_language_sat_l hZFC,
    tg_program_data_sat_l hZF.1,ts_program_sat_l hZF,tg_query_request_sat_l hZF,
    td_query_data_sat_l hZF.1,td_arity_sat_l I hZF.1,v_sat_l I hZF.1,tt_constants0_sat_l hZF.1,
    tt_pool_sat_l I (ZF.modelsKP hZF),td_node_query_sat_l I (ZF.modelsKP hZF),
    tg_max_query_sat_l I (ZF.modelsKP hZF),td_pending_query_sat_l I (ZF.modelsKP hZF),
    tg_bound_query_sat_l I (ZF.modelsKP hZF),tg_height_query_sat_l I (ZF.modelsKP hZF),
    td_reply_base_sat_l I (ZF.modelsKP hZF),
    Formula.satisfies_isFunction_iff I hZF.1,Definitional.Term.eval_weaken,tt_eval_cases_l,
    hw,he,hd,hA,hE,hP,hQ]
  refine ⟨⟨?_,?_,?_,?_⟩,setup.query_total_l hZFC ρ ω e δ A Q hw he hd hA hQ,?_,
    setup.elastic.elim (fun _ h => (fn0_function_l (ZF.modelsKP hZF) h.2.1).1),
    setup.programs.elim (fun _ h => (fn0_function_l (ZF.modelsKP hZF) h.2.1.1).1),
    (fn0_function_l (ZF.modelsKP hZF) setup.queries.1).1⟩
  · intro κ hk n hn B U D g h i z limit row
    exact setup.elastic.elim fun _ table => table.read_l hZFC hk hn limit row
  · intro n b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ row
    obtain ⟨H,_,table,_⟩ := setup.programs
    exact table.read_l hZFC row
  · intro n hn
    obtain ⟨H,_,table,_⟩ := setup.programs
    obtain ⟨b,z,σ,_,row,_⟩ := table.get_l hZFC hn
    have eq : Fin.cases (σ 0) (Fin.cases (σ 1) (Fin.cases (σ 2) (Fin.cases (σ 3)
        (Fin.cases (σ 4) (Fin.cases (σ 5) (fun _ => σ 6)))))) = σ := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
    exact ⟨b,z,σ 0,σ 1,σ 2,σ 3,σ 4,σ 5,σ 6,eq.symm ▸ row⟩
  · intro κ hk k s B U Du Dw pn pm pp pb ph request row
    exact setup.queries.read_l hZFC hk request row
  · intro κ hk n hn limit
    obtain ⟨D,table⟩ := setup.elastic
    obtain ⟨B,U,E,q,row,language⟩ := table.get_l hZFC hk hn limit
    exact ⟨B,U,E,q.largest,q.domain,q.inaccessible,q.stretch,row,language⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 历史中的原实数字母与 II 策略回复

偶数轮保留对手给定的原字母，奇数轮读取同一 II 策略。
数字阶段的结束式与普通类型游戏相同，直接共用；合法性读取真正的 Td_check。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_rules_d.digit_l {p : Tg_params_d M.Domain} {X F L G J σ R i n h v : M.Domain}
    (rules : Td_rules_d hZF p X F L J) (control : Cg_control_d I false p.ω p.e X F L G J σ R)
    (hi : M.mem i p.ω) (hn : M.mem n p.ω) (hh : M.mem h R) (fh : Fn0_d i X h)
    (div : M.IsOrdinalDivision I i p.c n p.b) (even : Gm_even_d I p.ω n) (hv : M.mem v p.A) (letters : M.MemberSubset p.A X) :
    Tg_digit_end_d hZF p X R i n h v := by
  have hvX := letters v hv
  obtain ⟨hc, _⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three hi
  have oc := rules.omega.members_areOrdinals (ZF.modelsKP hZF) p.c hc
  obtain ⟨j, t, hj, ft, endt⟩ := ZF.fseq_end_exists_l I hZF rules.omega hi (fn0_function_l (ZF.modelsKP hZF) fh) hvX
  have fn := fn0_of_function_l (ZF.modelsKP hZF) ft
  obtain ⟨a, b, d⟩ := endt
  have ej := d.source.2.2.2.eq hZF.1 ft.2.1
  have ei := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  have succ : M.SuccessorOf j i := ej ▸ ei ▸ d.length_successor
  have endt : Fseq_end_d I p.ω t h v := ⟨a, b, d⟩
  have check := td_check_end_l hZF hj succ fn fh endt ⟨n, p.b, hn, div, Or.inr (Or.inr ⟨rfl, hv⟩)⟩
  have legal := (rules.checks t).mpr ⟨(control.space t).mpr ⟨j, hj, ft⟩, check⟩
  have turn := (rules.owner.read_l hZF (rules.omega.isOrdinal (ZF.modelsKP hZF)) oc ⟨p.b, rules.three.predecessor_mem⟩ hi hn div).mpr
    (Or.inr ⟨rfl, even⟩)
  obtain ⟨m, next, hm⟩ := rules.omega.1.2 n hn
  exact ⟨t, j, m, endt, hj, hm, succ, next, fn, control.step i h v t hi hh hvX fh endt (Or.inl ⟨turn, legal⟩),
    tg_division_cycle_l hZF oc div rules.three next succ rules.empty, i, div, ei ▸ d.last_value⟩

theorem Td_rules_d.digit_strategy_l {p : Tg_params_d M.Domain} {X F L G J σ R i n h : M.Domain}
    (rules : Td_rules_d hZF p X F L J) (control : Cg_control_d I false p.ω p.e X F L G J σ R)
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
  have step := (td_step_read_l hZF (rules.omega.members_areOrdinals (ZF.modelsKP hZF) i hi)
    oc ⟨p.b, rules.three.predecessor_mem⟩ hn div).mp (check.end_l hZF fh endt)
  have hv := step.elim (fun h => (ne₀ h.1).elim) (fun h => h.elim (fun h => (ne₁ h.1).elim) And.right)
  obtain ⟨a, b, d⟩ := endt
  have ej := d.source.2.2.2.eq hZF.1 ft.2.1
  have ei := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  have succ : M.SuccessorOf j i := ej ▸ ei ▸ d.length_successor
  obtain ⟨m, next, hm⟩ := rules.omega.1.2 n hn
  exact ⟨v, hv, value, t, j, m, ⟨a, b, d⟩, hj, hm, succ, next, fn0_of_function_l (ZF.modelsKP hZF) ft, position,
    tg_division_cycle_l hZF oc div rules.three next succ rules.empty, i, div, ei ▸ d.last_value⟩

theorem td_digit_control_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X F L G J σ R : Term d)
    (rules : Td_rules_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (F.eval ρ) (L.eval ρ) (J.eval ρ))
    (letters : M.MemberSubset (p.A.eval ρ) (X.eval ρ))
    (control : Cg_control_d I false (p.ω.eval ρ) (p.e.eval ρ) (X.eval ρ) (F.eval ρ) (L.eval ρ) (G.eval ρ)
      (J.eval ρ) (σ.eval ρ) (R.eval ρ)) : Formula.satisfies ρ (tg_digit_control_m p X σ R) := by
  simp only [tg_digit_control_m, tg_digit_end_m, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_conj_iff, fn0_sat_l hZF.1,
    Formula.satisfies_isOrdinalDivision_iff I hZF.1, gm_even_sat_l I hZF.1, Formula.satisfies_neg_iff,
    Formula.satisfies_exists_iff, fseq_end_sat_l I hZF.1, Formula.satisfies_mem_iff,
    Formula.satisfies_isSuccessor_iff, tg_event_sat_l I hZF.1, rd_entry0_sat_l hZF.1,
    Definitional.Term.eval_weaken]
  intro i hi n hn h hh fn div
  exact ⟨fun even v hv => rules.digit_l hZF control hi hn hh fn div even hv letters,
    fun odd => rules.digit_strategy_l hZF control hi hn hh fn div odd⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原 II 胜策的完整有限控制记录

同一策略、三张固定表、实际三阶段续步及合法历史下降秩一起编码。
几何条件独立保存，有限历史的各证明不再携带未使用的大基数前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

def td_geometry_m {d} (p : Tg_params_d (Term d)) (X : Term d) : Formula 1 d := set[d] ⟪
  ⌜woodin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p.δ⌝ₛ) ∧ ⌜v_m kpair_convention_l⌝ₚ(⌜p.δ⌝ₛ,⌜X⌝ₛ) ∧
  ⌜p.A⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜p.e⌝ₛ ∈ ⌜p.S⌝ₛ ∧
  ⌜tg_low_m⌝ₚ(⌜p.ω⌝ₛ,⌜p.e⌝ₛ,⌜p.δ⌝ₛ,⌜p.S⌝ₛ,⌜p.ν⌝ₛ)⟫

@[simp] theorem td_geometry_closed_l {d} (p : Tg_params_d (Term d)) (X : Term d)
    (hp : p.closed_l) (hX : X.freeSupport = []) : (td_geometry_m p X).FreeClosed := by
  rcases hp with ⟨hw,he,_,_,_,hd,hA,hS,hν,_⟩
  simp -implicitDefEqProofs [td_geometry_m,Definitional.Formula.FreeClosed,hw,he,hd,hA,hS,hν,hX]

/-- 十二个原参数及 X/F/L/G/J/σ/R，全程保留同一原策略。 -/
def td_control0_m : Formula 1 19 :=
  let v : Fin 19 → Term 19 := Term.bound
  let p := tg_control_params_d v
  .conj (td_tables_m p.ω p.e p.δ p.A p.E p.P p.Q)
    (.conj (cg_control_m false p.ω p.e (v 12) (v 13) (v 14) (v 15) (v 16) (v 17) (v 18))
      (.conj (td_rules_m p (v 12) (v 13) (v 14) (v 16))
        (.conj (td_aux_control_m p (v 12) (v 17) (v 18))
          (.conj (td_start_control_m p (v 12) (v 17) (v 18))
            (.conj (td_answer_control_m p (v 12) (v 18))
              (.conj (tg_digit_control_m p (v 12) (v 17) (v 18))
                (.conj (cg_rank_m p.ω (v 12) (v 18))
                  (.conj (tg_index_m p.c) (td_geometry_m p (v 12))))))))))

theorem td_control0_closed_l : td_control0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_control0_m,tg_control_params_d,Definitional.Formula.FreeClosed]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · apply td_rules_closed_l <;> simp [Tg_params_d.closed_l]
  · apply td_aux_control_closed_l <;> simp [Tg_params_d.closed_l]
  · apply td_start_control_closed_l <;> simp [Tg_params_d.closed_l]
  · apply td_answer_control_closed_l <;> simp [Tg_params_d.closed_l]
  · apply tg_digit_control_closed_l <;> simp [Tg_params_d.closed_l]
  · apply td_geometry_closed_l <;> simp [Tg_params_d.closed_l]

theorem Td_game_d.control_record_l (hZFC : M.Models ZFC)
    {p : Tg_params_d M.Domain} {X F L G J B W O Z g σ : M.Domain}
    (game : Td_game_d hZFC p X F L G J B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) false p.ω X F J B W σ) :
    ∃ R r, let v : Fin 19 → M.Domain := fun i =>
      [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,X,F,L,G,J,σ,R].get i
      Rt_tuple_d v r ∧ Formula.satisfies (⟨v,fun _ => p.ω⟩ : Env M 19) td_control0_m ∧
      Formula.satisfies ((⟨Fin.elim0,fun _ => p.ω⟩ : Env M 0).push r) (rt_record_m td_control0_m .newest) := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨R,control⟩ := game.control_l hZFC win
  let v : Fin 19 → M.Domain := fun i =>
    [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,X,F,L,G,J,σ,R].get i
  let ρ : Env M 19 := ⟨v,fun _ => p.ω⟩
  obtain ⟨r,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) v
  obtain ⟨α,H,rank⟩ := control.rank_l hZF game.setup.omega (ZFC.dc_l I hZFC game.setup.omega)
    game.runs game.payoff win
  have ranked : Formula.satisfies ρ (cg_rank_m (.bound 0) (.bound 12) (.bound 18)) := by
    simp only [cg_rank_m,Formula.satisfies_exists_iff]
    exact ⟨α,H,(cg_rank0_sat_l (ZF.modelsKP hZF) ..).mpr rank⟩
  have indexed : Formula.satisfies ρ (tg_index_m (.bound 4)) := by
    obtain ⟨hc,_⟩ := tg_clock_l hZF game.setup.omega game.setup.empty game.setup.one game.setup.two
      game.setup.three (num_mem_l hZF.1 game.setup.omega (show Num_d 0 p.e from game.setup.empty))
    exact (tg_index_sat_l I hZF.1 ..).mpr fun _ _ _ _ =>
      tg_index_unique_l hZF (game.setup.omega.members_areOrdinals (ZF.modelsKP hZF) p.c hc)
  have rules := game.rules_l hZFC
  have valid : Formula.satisfies ρ td_control0_m := by
    simp only [td_control0_m,Formula.satisfies_conj_iff]
    refine ⟨game.setup.tables_l hZFC ρ (.bound 0) (.bound 1) (.bound 5) (.bound 6) (.bound 9) (.bound 10) (.bound 11)
      rfl rfl rfl rfl rfl rfl rfl,(cg_control_sat_l I hZF.1 false ..).mpr control,
      (td_rules_sat_l hZF ..).mpr rules,
      td_aux_control_l hZF ρ _ _ (.bound 13) (.bound 14) (.bound 15) (.bound 16) _ _ rules control,
      td_start_control_l hZF ρ _ _ (.bound 13) (.bound 14) (.bound 15) (.bound 16) _ _ rules control,
      td_answer_control_l hZFC ρ _ _ (.bound 13) (.bound 14) (.bound 15) (.bound 16) (.bound 17) _ game.setup rules control,
      td_digit_control_l hZF ρ _ _ (.bound 13) (.bound 14) (.bound 15) (.bound 16) _ _ rules
        ((v_transitive_l I game.setup.rank) p.A game.setup.letters) control,ranked,indexed,?_⟩
    simp only [td_geometry_m,Formula.satisfies_conj_iff,woodin_sat_l I hZF.1,v_sat_l I hZF.1,
      Formula.satisfies_mem_iff,tg_low_sat_l hZF]
    exact ⟨woodin,game.setup.rank,game.setup.letters,root,game.setup.low⟩
  exact ⟨R,r,tuple,valid,(rt_record_sat_l hZF.1 _ _ _ td_control0_closed_l).mpr ⟨v,tuple,valid⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
