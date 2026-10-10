import YesMetaZFC.SetTheory.LargeCardinal.IterationLimitSyntax
import YesMetaZFC.SetTheory.LargeCardinal.IterationDiagramSyntax
import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakAnswer

/-! # 线性状态、历史与全前驱保持的一阶编码 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def wi_state_m {d} (ω α T Q G a A S P : Term d) : Formula 1 d := set[d] ⟪
  ⌜it_diagram_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, ⌜T⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ) ∧
  (∀ i j, j ∈ ⌜α⌝ₛ → i ∈ j → ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ)) ∧
  (∀ i c, ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) → ⌜it_source_m⌝ₚ(⌜ω⌝ₛ, c)) ∧
  (∀ i c X R, ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) → ⌜kpair0_m⌝ₚ(c, X, R) →
    ⌜Formula.cardinalLessOrEqual kpair_convention_l⌝ₚ(X, ⌜ω⌝ₛ)) ∧
  ⌜it_embedding_m⌝ₚ(⌜ω⌝ₛ, ⌜α⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, ⌜P⌝ₛ)⟫
derive_free_closed wi_state_m
theorem wi_state_sat_l {d} (η : Env M d) (ω α T Q G a A S P : Term d) :
    Formula.satisfies η (wi_state_m ω α T Q G a A S P) ↔
      Wi_state_d hZF (ω.eval η) (α.eval η) (T.eval η) (Q.eval η) (G.eval η) (a.eval η) (A.eval η) (S.eval η) (P.eval η) := by
  simp only [wi_state_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, it_diagram_sat_l hZF, rd_entry0_sat_l hZF.1, it_source_sat_l hZF,
    kpair0_sat_l hZF.1, Formula.satisfies_cardinalLessOrEqual_iff I hZF.1,
    it_embedding_sat_l hZF, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun h => ⟨h.diagram, h.linear, h.sources, h.count, h.returns⟩⟩

def wi_keep_m {d} (Q G P Q' G' P' : Term d) : Formula 1 d := set[d] ⟪
  (∀ i c, ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q'⌝ₛ)) ∧
  (∀ i j f, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, j, f) → ⌜it_map_m⌝ₚ(⌜G'⌝ₛ, i, j, f)) ∧
  (∀ i f, ⌜rd_entry0_m⌝ₚ(i, f, ⌜P⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, f, ⌜P'⌝ₛ))⟫
derive_free_closed wi_keep_m
theorem wi_keep_sat_l (hE : Extensional M) {d} (η : Env M d) (Q G P Q' G' P' : Term d) :
    Formula.satisfies η (wi_keep_m Q G P Q' G' P') ↔
      Wi_keep_d (Q.eval η) (G.eval η) (P.eval η) (Q'.eval η) (G'.eval η) (P'.eval η) := by
  simp only [wi_keep_m, Wi_keep_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, rd_entry0_sat_l hE, it_map_sat_l hE, Definitional.Term.eval_weaken]; rfl

def wi_at_m {d} (H i T Q G P : Term d) : Formula 1 d := set[d] ⟪
  ∃ s, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, s, ⌜H⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(s, ⌜T⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜P⌝ₛ)⟫
derive_free_closed wi_at_m
theorem wi_at_sat_l (hE : Extensional M) {d} (η : Env M d) (H i T Q G P : Term d) :
    Formula.satisfies η (wi_at_m H i T Q G P) ↔ Wi_at_d (H.eval η) (i.eval η) (T.eval η) (Q.eval η) (G.eval η) (P.eval η) := by
  simp only [wi_at_m, Wi_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, rd_quad_sat_l hE, Definitional.Term.eval_weaken]; rfl

def wi_past_m {d} (H Q G P : Term d) : Formula 1 d := set[d] ⟪
  ∀ i U Q' G' P', ⌜wi_at_m⌝ₚ(⌜H⌝ₛ, i, U, Q', G', P') → ⌜wi_keep_m⌝ₚ(Q', G', P', ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜P⌝ₛ)⟫
derive_free_closed wi_past_m
theorem wi_past_sat_l (hE : Extensional M) {d} (η : Env M d) (H Q G P : Term d) :
    Formula.satisfies η (wi_past_m H Q G P) ↔ Wi_past_d (H.eval η) (Q.eval η) (G.eval η) (P.eval η) := by
  simp only [wi_past_m, Wi_past_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    wi_at_sat_l hE, wi_keep_sat_l hE, Definitional.Term.eval_weaken]; rfl

def wi_history_m {d} (ω a A S α D H : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜α⌝ₛ, ⌜D⌝ₛ, ⌜H⌝ₛ) ∧
  (∀ i s, ⌜rd_entry0_m⌝ₚ(i, s, ⌜H⌝ₛ) → ∃ β T Q G P, ⌜KP.succ0_m⌝ₚ(β, i) ∧
    ⌜rd_quad_m⌝ₚ(s, T, Q, G, P) ∧ ⌜wi_state_m⌝ₚ(⌜ω⌝ₛ, β, T, Q, G, ⌜a⌝ₛ, ⌜A⌝ₛ, ⌜S⌝ₛ, P)) ∧
  (∀ i j T Q G P U Q' G' P', i ∈ j → ⌜wi_at_m⌝ₚ(⌜H⌝ₛ, i, T, Q, G, P) →
    ⌜wi_at_m⌝ₚ(⌜H⌝ₛ, j, U, Q', G', P') → ⌜wi_keep_m⌝ₚ(Q, G, P, Q', G', P'))⟫
derive_free_closed wi_history_m
theorem wi_history_sat_l {d} (η : Env M d) (ω a A S α D H : Term d) :
    Formula.satisfies η (wi_history_m ω a A S α D H) ↔
      Wi_history_d hZF (ω.eval η) (a.eval η) (A.eval η) (S.eval η) (α.eval η) (D.eval η) (H.eval η) := by
  simp only [wi_history_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_mem_iff, fn0_sat_l hZF.1, rd_entry0_sat_l hZF.1,
    KP.succ0_sat_l hZF.1, rd_quad_sat_l hZF.1, wi_state_sat_l hZF,
    wi_at_sat_l hZF.1, wi_keep_sat_l hZF.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun h => ⟨h.function, h.rows, h.past⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
