import YesMetaZFC.Model.Forcing.Iteration.Proper.Extension

/-! # 参数化 Cohen 可数支撑迭代的 proper 保持及完整区间实例

直接消费已经验证的 Cohen 原公式规则与其 proper 证书，自动构造指定内部长度
的 proper 迭代，并对任意内部可数种子返回共同 N 上的全部区间迭代引理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem cohen_iteration_pil_l (κ : M.Domain) {δ} (hδ : M.IsOrdinal δ) :
    ∃ ω b F G, M.IsOmega ω ∧ Row_iteration_d I true ω b cohen_rule_s (⟨fun _ => κ, fun _ => κ⟩ : Env M 1) δ F G ∧
      ∀ A, M.CardinalLessOrEqual I A ω → ∃ χ H N,
        Hsub_d I ω χ H N ∧ M.MemberSubset A N ∧ M.mem δ N ∧
          ∀ β, M.mem β N → Row_pil_stage_d I F G b N β := by
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨b, F, G, h, hp⟩ := row_iteration_pr_exists_l hZFC hω hδ
    (cohen_rule_l hZF hω true ⟨fun _ => κ, fun _ => κ⟩) (cohen_rule_pr_l hZFC ⟨fun _ => κ, fun _ => κ⟩)
  exact ⟨ω, b, F, G, hω, h, hp⟩

/-- 添加量与内部长度均直接参数化，所有阶段自动满足完整 club 版 properness。 -/
theorem cohen_iteration_proper_l (κ : M.Domain) {δ} (hδ : M.IsOrdinal δ) :
    ∃ ω b F G, M.IsOmega ω ∧ Row_iteration_d I true ω b cohen_rule_s (⟨fun _ => κ, fun _ => κ⟩ : Env M 1) δ F G ∧
      ∀ β D V, Entry_d M β D F → Entry_d M β V G → Proper_d I ω D V D := by
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨b, F, G, h, hp⟩ := row_iteration_proper_exists_l hZFC hω hδ
    (cohen_rule_l hZF hω true ⟨fun _ => κ, fun _ => κ⟩) (cohen_rule_pr_l hZFC ⟨fun _ => κ, fun _ => κ⟩)
  exact ⟨ω, b, F, G, hω, h, hp⟩

/-- 任意添加量与内部长度，一次取得 ZFC、ω₁、可数覆盖与可数共尾性保持。 -/
theorem cohen_iteration_preserves_l (κ : M.Domain) {δ} (hδ : M.IsOrdinal δ) :
    ∃ ω μ b F G, M.IsOmega ω ∧ M.IsHartogsNumber I μ ω ∧
      ∃ h : Row_iteration_d I true ω b cohen_rule_s (⟨fun _ => κ, fun _ => κ⟩ : Env M 1) δ F G,
        ∀ β D V (hD : Entry_d M β D F) (hV : Entry_d M β V G) U (hU : Generic_d M D V D U),
          let O := (h.1.stages β D V hD hV).order
          let E := extension_l M hZF D V D U
          let J := kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
          E.Models ZFC ∧ ∃ e : M.Domain → E.Domain,
            (∀ a s, Check_d M b a s → Qval_d M D V D U s (e a)) ∧
            (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧ Function.Injective e ∧
            E.IsOmega (e ω) ∧ E.IsHartogsNumber J (e μ) (e ω) ∧
            (∀ X, E.CardinalLessOrEqual J (e X) (e ω) ↔ M.CardinalLessOrEqual I X ω) ∧
            (∀ X Y, E.MemberSubset Y (e X) → E.CardinalLessOrEqual J Y (e ω) →
              ∃ A, M.MemberSubset A X ∧ M.CardinalLessOrEqual I A ω ∧ E.MemberSubset Y (e A)) ∧
            (∀ α, E.IsCofinality J (e ω) (e α) ↔ M.IsCofinality I ω α) ∧
            ∀ α cf, M.IsCofinality I cf α → M.mem ω cf → ∀ Y, E.MemberSubset Y (e α) →
              E.CardinalLessOrEqual J Y (e ω) → ∃ β, M.mem β α ∧ E.MemberSubset Y (e β) := by
  obtain ⟨ω, b, F, G, hω, h, _⟩ := cohen_iteration_proper_l hZFC κ hδ
  obtain ⟨μ, hμ, hp⟩ := row_iteration_preserves_l hZFC hω
    (cohen_rule_l hZF hω true ⟨fun _ => κ, fun _ => κ⟩) (cohen_rule_pr_l hZFC ⟨fun _ => κ, fun _ => κ⟩) h
  exact ⟨ω, μ, b, F, G, hω, hμ, h, hp⟩

end YesMetaZFC.Model.Forcing.Internal
