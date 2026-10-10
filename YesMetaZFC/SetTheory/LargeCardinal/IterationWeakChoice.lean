import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakAnswerSyntax
import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakBound
import YesMetaZFC.SetTheory.DependentChoice

/-! # 同一集合上的实际应答选择函数

有可用应答时选择真实枝及下一状态；仅在没有应答时取固定初始值。
后续合法博弈的归纳将逐步排除后一个分支。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def Wi_request_d (ω a A S o s₀ r u : M.Domain) : Prop := ∃ α H t B s,
  Rd_triple_d r α H t ∧ KPair_d M u B s ∧ Wi_answer_d hZF ω a A S o s₀ α H t B s
def wi_request_m {d} (ω a A S o s₀ r u : Term d) : Formula 1 d := set[d] ⟪
  ∃ α H t B s, ⌜rd_triple0_m⌝ₚ(⌜r⌝ₛ, α, H, t) ∧ ⌜kpair0_m⌝ₚ(⌜u⌝ₛ, B, s) ∧
    ⌜wi_answer_m⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, ⌜o⌝ₛ, ⌜s₀⌝ₛ, α, H, t, B, s)⟫
derive_free_closed wi_request_m
theorem wi_request_sat_l {d} (η : Env M d) (ω a A S o s₀ r u : Term d) :
    Formula.satisfies η (wi_request_m ω a A S o s₀ r u) ↔ Wi_request_d hZF
      (ω.eval η) (a.eval η) (A.eval η) (S.eval η) (o.eval η) (s₀.eval η) (r.eval η) (u.eval η) := by
  simp only [wi_request_m, Wi_request_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_triple0_sat_l hZF.1, kpair0_sat_l hZF.1, wi_answer_sat_l hZF, Definitional.Term.eval_weaken]; rfl

structure Wi_selector_d (ω a A S o s₀ Z Ψ : M.Domain) : Prop where
  function : Fn0_d Z Z Ψ
  values : ∀ r u, Rd_entry_d r u Ψ → ∃ B s, KPair_d M u B s
  selects : ∀ r u, Rd_entry_d r u Ψ →
    (∃ v, M.mem v Z ∧ Wi_request_d hZF ω a A S o s₀ r v) → Wi_request_d hZF ω a A S o s₀ r u

theorem Wi_selector_d.answer_l {ω a A S o s₀ Z Ψ r u α H t B s : M.Domain}
    (h : Wi_selector_d hZF ω a A S o s₀ Z Ψ) (hr : Rd_triple_d r α H t) (hu : KPair_d M u B s)
    (edge : Rd_entry_d r u Ψ) (available : ∃ v, M.mem v Z ∧ Wi_request_d hZF ω a A S o s₀ r v) :
    Wi_answer_d hZF ω a A S o s₀ α H t B s := by
  obtain ⟨β, H', t', B', s', request, response, answer⟩ := h.selects r u edge available
  obtain ⟨rfl, rfl, rfl⟩ := request.unique_l hr
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M response hu
  exact answer

def wi_select_m {d} (ω a A S o s₀ Z u₀ r u : Term d) : Formula 1 d := set[d] ⟪
  ⌜wi_request_m⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, ⌜o⌝ₛ, ⌜s₀⌝ₛ, ⌜r⌝ₛ, ⌜u⌝ₛ) ∨
  (⌜u⌝ₛ = ⌜u₀⌝ₛ ∧ ¬ (∃ v ∈ ⌜Z⌝ₛ, ⌜wi_request_m⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, ⌜o⌝ₛ, ⌜s₀⌝ₛ, ⌜r⌝ₛ, v)))⟫
derive_free_closed wi_select_m

/-- 原选择公理在实际 Z 上一次选择所有可用应答，不使用元层数据选择。 -/
theorem wi_selector_exists_l (hZFC : M.Models ZFC) {ω a A S o s₀ Z u₀ : M.Domain}
    (hu₀ : M.mem u₀ Z) (pair : KPair_d M u₀ o s₀) :
    ∃ Ψ, Wi_selector_d (ZFC.models_zf_l hZFC) ω a A S o s₀ Z Ψ := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  let η : Env M 8 := (((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push a).push A).push S).push o).push s₀).push Z).push u₀
  let φ : BinarySchema 8 := { body := (wi_select_m (.bound 9) (.bound 8) (.bound 7) (.bound 6)
    (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  have sat r u : φ.denote η r u ↔ Wi_request_d hZF ω a A S o s₀ r u ∨
      (u = u₀ ∧ ¬ ∃ v, M.mem v Z ∧ Wi_request_d hZF ω a A S o s₀ r v) := by
    simp only [φ, BinarySchema.denote, wi_select_m, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_neg_iff, Formula.satisfies_existsMem_iff,
      wi_request_sat_l hZF, Definitional.Term.eval_weaken]; rfl
  obtain ⟨Ψ, hf, selects⟩ := ZFC.uniformize_formula_l I hZFC φ η (X := Z) (Y := Z) (fun r _ => by
    by_cases good : ∃ v, M.mem v Z ∧ Wi_request_d hZF ω a A S o s₀ r v
    · obtain ⟨u, hu, answer⟩ := good
      exact ⟨u, hu, (sat r u).mpr (Or.inl answer)⟩
    · exact ⟨u₀, hu₀, (sat r u₀).mpr (Or.inr ⟨rfl, good⟩)⟩)
  refine ⟨Ψ, fn0_of_function_l (ZF.modelsKP hZF) hf, ?_, ?_⟩
  · intro r u edge
    rcases (sat r u).mp (selects r u edge) with ⟨_, _, _, B, s, _, pu, _⟩ | ⟨eq, _⟩
    · exact ⟨B, s, pu⟩
    · exact ⟨o, s₀, eq.symm ▸ pair⟩
  · intro r u edge available
    exact ((sat r u).mp (selects r u edge)).elim id (fun hh => (hh.2 available).elim)

end YesMetaZFC.SetTheory.LargeCardinal
