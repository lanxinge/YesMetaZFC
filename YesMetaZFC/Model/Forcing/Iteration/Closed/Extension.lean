import YesMetaZFC.Model.Forcing.Iteration.Closed.Induction
import YesMetaZFC.Model.Forcing.Closed.Extension

/-! # 可数支撑闭迭代各阶段的 ZFC 与内部序列反射

完整闭性归纳已消去阶段保持前提；共同顶条件使各泛型采用同一规范名称约定。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_iteration_closed_preserves_l {n} {φ : BinarySchema (n+4)} {ρ : Env M n} {ω δ F G b}
    (hω : M.IsOmega ω) (hRule : Row_rule_d I true ω φ ρ) (hCl : Row_cl_rule_d I ω φ ρ)
    (h : Row_iteration_d I true ω b φ ρ δ F G) :
    ∀ β D V (hD : Entry_d M β D F) (hV : Entry_d M β V G) U (hU : Generic_d M D V D U),
      let O := (h.1.stages β D V hD hV).order
      let E := extension_l M hZF D V D U
      let J := kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
      E.Models ZFC ∧ ∃ e : M.Domain → E.Domain,
        (∀ a s, Check_d M b a s → Qval_d M D V D U s (e a)) ∧
        (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧ Function.Injective e ∧ E.IsOmega (e ω) ∧
        (∀ x, E.MemberSubset x (e ω) → ∃ a, M.MemberSubset a ω ∧ e a = x) ∧
        (∀ X f, E.IsSetFunctionFromTo J f (e ω) (e X) →
          ∃ g, M.IsSetFunctionFromTo I g ω X ∧ e g = f) ∧
        (∀ X Y, E.MemberSubset Y (e X) → E.CardinalLessOrEqual J Y (e ω) →
          ∃ A, M.MemberSubset A X ∧ M.CardinalLessOrEqual I A ω ∧ e A = Y) ∧
        (∀ X, E.CardinalLessOrEqual J (e X) (e ω) ↔ M.CardinalLessOrEqual I X ω) ∧
        (∀ κ, M.IsHartogsNumber I κ ω → E.IsHartogsNumber J (e κ) (e ω)) ∧
        (∀ α, E.IsCofinality J (e ω) (e α) ↔ M.IsCofinality I ω α) ∧
        ∀ α cf, M.IsCofinality I cf α → M.mem ω cf → ∀ Y, E.MemberSubset Y (e α) →
          E.CardinalLessOrEqual J Y (e ω) → ∃ β, M.mem β α ∧ E.MemberSubset Y (e β) := by
  have hc := row_iteration_closed_l hZFC hω hRule hCl h
  intro β D V hD hV U hU
  have hs := h.1.stages β D V hD hV
  obtain ⟨p, hp⟩ := hU.inhabited
  have hb := hU.upward p b hp hs.base (hs.top p (hU.proper p hp).1)
  exact closed_extension_l hs.order hZFC hU hω (hc β D V hD hV) hb

end YesMetaZFC.Model.Forcing.Internal
