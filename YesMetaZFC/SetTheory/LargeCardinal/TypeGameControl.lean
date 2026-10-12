import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRenewalSyntax
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameStages
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameQueryTotal
import YesMetaZFC.SetTheory.Descriptive.GameControl
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecord

/-! # 随原策略搬运的有限历史控制记录

三张实际代码表的读取性质、七条走法规则和原策略的合法延伸性质放在同一条
有限公式中。它由已经装配的游戏和 II 的获胜策略构造，不要求新工作模型
满足 ZFC，也不把下一轮的合法性作为递归的额外前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

def tg_tables_m {d} (ω e δ E P Q : Term d) : Formula 1 d := .conj (set[d] ⟪
  (∀ κ ∈ ⌜δ⌝ₛ, ∀ n ∈ ⌜ω⌝ₛ, ∀ B U D g h i z,
    ⌜Formula.isLimitOrdinal⌝ₚ(κ) → ⌜tg_ee_data_m⌝ₚ(⌜E⌝ₛ, κ, n, B, U, D, g, h, i, z) →
    ⌜ee_language_m⌝ₚ(⌜ω⌝ₛ, κ, n, B, U, D, g, h, i, z)) ∧
  (∀ n b z s₀ s₁ s₂ s₃ s₄ s₅ s₆,
    ⌜fun P n b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_program_data_m P n b z
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜P⌝ₛ, n, b, z, s₀, s₁, s₂, s₃, s₄, s₅, s₆) → ∃ a,
    ⌜fun ω n b a z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => ts_program_m ω n b a z
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜ω⌝ₛ, n, b, a, z, s₀, s₁, s₂, s₃, s₄, s₅, s₆)) ∧
  (∀ n ∈ ⌜ω⌝ₛ, ∃ b z s₀ s₁ s₂ s₃ s₄ s₅ s₆,
    ⌜fun P n b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_program_data_m P n b z
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜P⌝ₛ, n, b, z, s₀, s₁, s₂, s₃, s₄, s₅, s₆)) ∧
  (∀ κ ∈ ⌜δ⌝ₛ, ∀ k s t B U D r m b h q,
    ⌜tg_query_request_m⌝ₚ(⌜ω⌝ₛ, κ, k, s, t) →
    ⌜tg_query_data_m⌝ₚ(⌜Q⌝ₛ, κ, k, s, t, B, U, D, r, m, b, h, q) → ∃ l n,
    ⌜Formula.isSuccessor⌝ₚ(l, k) ∧ ⌜Formula.isSuccessor⌝ₚ(n, l) ∧
    ⌜tg_reply_language_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, l, n, κ, B, U, D, r, b, h) ∧
    ⌜tg_max_query_m⌝ₚ(⌜ω⌝ₛ, l, n, U, D, m) ∧
    ⌜tg_node_query_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, n, l, U, D, s, t, k, q) ∧
    ⌜tg_query_base_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, l, n, k, s, t, r, m, b, h, q))⟫) (tg_query_total_m ω e δ Q)
@[simp] theorem tg_tables_closed_l {d} (ω e δ E P Q : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (hd : δ.freeSupport = [])
    (hE : E.freeSupport = []) (hP : P.freeSupport = []) (hQ : Q.freeSupport = []) :
    (tg_tables_m ω e δ E P Q).FreeClosed := by
  simp -implicitDefEqProofs [tg_tables_m, Definitional.Formula.FreeClosed, hw, he, hd, hE, hP, hQ,
    Fin.forall_fin_succ]

theorem Tg_setup_d.tables_l (hZFC : M.Models ZFC) {p : Tg_params_d M.Domain} {X : M.Domain}
    (setup : Tg_setup_d hZFC p X) {d} (ρ : Env M d) (ω e δ E P Q : Term d)
    (hw : ω.eval ρ = p.ω) (he : e.eval ρ = p.e) (hd : δ.eval ρ = p.δ)
    (hE : E.eval ρ = p.E) (hP : P.eval ρ = p.P) (hQ : Q.eval ρ = p.Q) :
    Formula.satisfies ρ (tg_tables_m ω e δ E P Q) := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [tg_tables_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_isLimitOrdinal_iff, Formula.satisfies_isSuccessor_iff,
    tg_ee_data_sat_l hZF.1, ee_language_sat_l hZFC, tg_program_data_sat_l hZF.1,
    ts_program_sat_l hZF, tg_query_request_sat_l hZF, tg_query_data_sat_l hZF.1,
    tg_reply_language_sat_l hZF, tg_max_query_sat_l I (ZF.modelsKP hZF),
    tg_node_query_sat_l I (ZF.modelsKP hZF), tg_query_base_sat_l I (ZF.modelsKP hZF),
    Definitional.Term.eval_weaken, tt_eval_cases_l, hw, he, hd, hE, hP, hQ]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, setup.query_total_l hZFC ρ ω e δ Q hw he hd hQ⟩
  · intro κ hk n hn B U D g h i z limit row
    exact setup.elastic.elim fun _ table => table.read_l hZFC hk hn limit row
  · intro n b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ row
    obtain ⟨H, _, table, _⟩ := setup.programs
    exact table.read_l hZFC row
  · intro n hn
    obtain ⟨H, _, table, _⟩ := setup.programs
    obtain ⟨b, z, σ, _, row, _⟩ := table.get_l hZFC hn
    have eq : Fin.cases (σ 0) (Fin.cases (σ 1) (Fin.cases (σ 2) (Fin.cases (σ 3)
        (Fin.cases (σ 4) (Fin.cases (σ 5) (fun _ => σ 6)))))) = σ := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
    exact ⟨b, z, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6, eq.symm ▸ row⟩
  · intro κ hk k s t B U D r m b h q request row
    obtain ⟨l, n, hl, hn, lang, max, node, base⟩ := setup.queries.read_l hZFC hk request row
    exact ⟨l, n, hl, hn, lang, max, node, ((tg_query_row_sat_l I (ZF.modelsKP hZF) _).mp base).1⟩

/-- 记录依次保存十二个原参数、走法全集及五个控制集合。 -/
def tg_control_params_d {α : Type u} (v : Fin 19 → α) : Tg_params_d α :=
  ⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11⟩

structure Tg_rules_d (hZF : M.Models ZF) (p : Tg_params_d M.Domain) (X F L J : M.Domain) : Prop where
  omega : M.IsOmega p.ω
  empty : ∀ x, ¬ M.mem x p.e
  one : M.SuccessorOf p.a p.e
  two : M.SuccessorOf p.b p.a
  three : M.SuccessorOf p.c p.b
  woodin : Woodin_d (kp_pair_l (ZF.modelsKP hZF)) p.δ
  rank : V_d (kp_pair_l (ZF.modelsKP hZF)) p.δ X
  letters : M.mem p.A X
  root : M.mem p.e p.S
  low : Tg_low_d hZF p.ω p.e p.δ p.S p.ν
  checks : ∀ h, M.mem h L ↔ M.mem h F ∧ Tg_check_d hZF p X h
  owner : Tg_owner_d hZF p.ω p.c p.a p.b J

def tg_rules_m {d} (p : Tg_params_d (Term d)) (X F L J : Term d) : Formula 1 d :=
  set[d] ⟪⌜Formula.isOmega⌝ₚ(⌜p.ω⌝ₛ) ∧ ⌜Formula.isEmpty⌝ₚ(⌜p.e⌝ₛ) ∧
      ⌜Formula.isSuccessor⌝ₚ(⌜p.a⌝ₛ, ⌜p.e⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜p.b⌝ₛ, ⌜p.a⌝ₛ) ∧
      ⌜Formula.isSuccessor⌝ₚ(⌜p.c⌝ₛ, ⌜p.b⌝ₛ) ∧ ⌜woodin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p.δ⌝ₛ) ∧
      ⌜v_m kpair_convention_l⌝ₚ(⌜p.δ⌝ₛ, ⌜X⌝ₛ) ∧ ⌜p.A⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜p.e⌝ₛ ∈ ⌜p.S⌝ₛ ∧
      ⌜tg_low_m⌝ₚ(⌜p.ω⌝ₛ, ⌜p.e⌝ₛ, ⌜p.δ⌝ₛ, ⌜p.S⌝ₛ, ⌜p.ν⌝ₛ) ∧
      (∀ h, h ∈ ⌜L⌝ₛ ↔ h ∈ ⌜F⌝ₛ ∧ ⌜fun h => tg_check_m (p.map_l Term.weaken) X.weaken h⌝ₚ(h)) ∧
      (∀ i, i ∈ ⌜J⌝ₛ ↔ i ∈ ⌜p.ω⌝ₛ ∧ (∃ n r, n ∈ ⌜p.ω⌝ₛ ∧
        ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(i, ⌜p.c⌝ₛ, n, r) ∧
        (r = ⌜p.a⌝ₛ ∨ r = ⌜p.b⌝ₛ ∧ ⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p.ω⌝ₛ, n))))⟫

@[simp] theorem tg_rules_closed_l {d} (p : Tg_params_d (Term d)) (X F L J : Term d)
    (hp : p.closed_l) (hX : X.freeSupport = []) (hF : F.freeSupport = [])
    (hL : L.freeSupport = []) (hJ : J.freeSupport = []) : (tg_rules_m p X F L J).FreeClosed := by
  have hc := tg_check_closed_l (p.map_l Term.weaken) X.weaken .newest (p.weaken_closed_l hp)
    (by simpa using hX) rfl
  rcases hp with ⟨hw, he, ha, hb, hc', hd, hA, hS, hν, hE, hP, hQ⟩
  simp -implicitDefEqProofs [tg_rules_m, Definitional.Formula.FreeClosed, hw, he, ha, hb, hc', hd, hA, hS,
    hν, hX, hF, hL, hJ, hc]

theorem tg_rules_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X F L J : Term d) :
    Formula.satisfies ρ (tg_rules_m p X F L J) ↔ Tg_rules_d hZF (p.map_l (fun t => t.eval ρ))
      (X.eval ρ) (F.eval ρ) (L.eval ρ) (J.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [tg_rules_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_isSuccessor_iff, woodin_sat_l I hZF.1, v_sat_l I hZF.1,
    Formula.satisfies_mem_iff, tg_low_sat_l hZF, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, tg_check_sat_l hZF, Formula.satisfies_exists_iff,
    Formula.satisfies_isOrdinalDivision_iff I hZF.1, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1, gm_even_sat_l I hZF.1,
    Tg_params_d.map_l, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩,
    fun h => ⟨h.omega, h.empty, h.one, h.two, h.three, h.woodin, h.rank, h.letters, h.root, h.low, h.checks, h.owner⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
