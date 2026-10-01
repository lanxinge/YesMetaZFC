import YesMetaZFC.Model.Forcing.Iteration.Proper.Preservation
import YesMetaZFC.Model.Forcing.Proper.Preservation.Countable

/-! # 可数支撑迭代的 ZFC、ω₁ 与旧可数性保持

固定一次地模型的 ω₁。完整 proper 保持使各阶段的每个泛型扩张都保留该序数，
并反射旧可数性、覆盖新可数集合、保持 ω 共尾度及严格旧界；顶条件保证统一名称有效。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_iteration_preserves_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {ω δ F G b}
    (hω : M.IsOmega ω) (hRule : Row_rule_d I true ω φ ρ) (hPr : Row_pr_rule_d I φ ρ)
    (h : Row_iteration_d I true ω b φ ρ δ F G) : ∃ κ, M.IsHartogsNumber I κ ω ∧
      ∀ β D V (hD : Entry_d M β D F) (hV : Entry_d M β V G) U (hU : Generic_d M D V D U),
        let O := (h.1.stages β D V hD hV).order
        let E := extension_l M hZF D V D U
        let J := kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
        E.Models ZFC ∧ ∃ e : M.Domain → E.Domain,
          (∀ a s, Check_d M b a s → Qval_d M D V D U s (e a)) ∧
          (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧ Function.Injective e ∧
          E.IsOmega (e ω) ∧ E.IsHartogsNumber J (e κ) (e ω) ∧
          (∀ X, E.CardinalLessOrEqual J (e X) (e ω) ↔ M.CardinalLessOrEqual I X ω) ∧
          (∀ X Y, E.MemberSubset Y (e X) → E.CardinalLessOrEqual J Y (e ω) →
            ∃ A, M.MemberSubset A X ∧ M.CardinalLessOrEqual I A ω ∧ E.MemberSubset Y (e A)) ∧
          (∀ α, E.IsCofinality J (e ω) (e α) ↔ M.IsCofinality I ω α) ∧
          ∀ α cf, M.IsCofinality I cf α → M.mem ω cf → ∀ Y, E.MemberSubset Y (e α) →
            E.CardinalLessOrEqual J Y (e ω) → ∃ β, M.mem β α ∧ E.MemberSubset Y (e β) := by
  obtain ⟨κ, hκ⟩ := ZF.exists_hartogsNumber hZF I ω
  have hp := row_iteration_proper_l hZFC hω hRule hPr h
  refine ⟨κ, hκ, fun β D V hD hV U hU => ?_⟩
  have hs := h.1.stages β D V hD hV
  obtain ⟨p, hpU⟩ := hU.inhabited
  have hb := hU.upward p b hpU hs.base (hs.top p (hU.proper p hpU).1)
  exact proper_extension_l hs.order hZFC hU hω (hp β D V hD hV) hb hκ

end YesMetaZFC.Model.Forcing.Internal
