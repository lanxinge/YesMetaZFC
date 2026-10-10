import YesMetaZFC.Model.Forcing.Applications.Collapse.Proper
import YesMetaZFC.Model.Forcing.Iteration.Proper.Induction
import YesMetaZFC.Model.Forcing.Iteration.Closed.Extension

/-! # 任意内部长度的参数化可数闭塌缩迭代

两个集合参数与内部序数长度直接决定完整可数支撑迭代；全阶段闭性、全部前缀
区间以及各泛型扩张的 ZFC、序列与可数子集反射都由已实现规则自动取得。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem collapse_iteration_closed_l (X Y : M.Domain) {δ} (hδ : M.IsOrdinal δ) :
    ∃ ω b F G, M.IsOmega ω ∧
      Row_iteration_d I true ω b coll_rule_s (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y) δ F G ∧
      (∀ β, Row_cl_stage_d I ω F G β) ∧ ∀ β D V, Entry_d M β D F → Entry_d M β V G → Closed_d I D V D ω := by
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y
  obtain ⟨b, F, G, h, hi, hc⟩ := row_iteration_closed_exists_l hZFC hω hδ
    (collapse_rule_l hZFC ρ hω true) (collapse_rule_closed_l hZFC ρ hω)
  exact ⟨ω, b, F, G, hω, h, hi, hc⟩

/-- 一次构造全部闭阶段，并返回各泛型扩张中实数、旧目标序列及可数子集的实际旧原像。 -/
theorem collapse_iteration_preserves_l (X Y : M.Domain) {δ} (hδ : M.IsOrdinal δ) :
    ∃ ω b F G, M.IsOmega ω ∧
      ∃ h : Row_iteration_d I true ω b coll_rule_s (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y) δ F G,
        (∀ β, Row_cl_stage_d I ω F G β) ∧
        (∀ β D V, Entry_d M β D F → Entry_d M β V G → Closed_d I D V D ω) ∧
        ∀ β D V (hD : Entry_d M β D F) (hV : Entry_d M β V G) U (hU : Generic_d M D V D U),
          let O := (h.1.stages β D V hD hV).order
          let E := extension_l M hZF D V D U
          let J := kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
          E.Models ZFC ∧ ∃ e : M.Domain → E.Domain,
            (∀ a s, Check_d M b a s → Qval_d M D V D U s (e a)) ∧
            (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧ Function.Injective e ∧ E.IsOmega (e ω) ∧
            (∀ x, E.MemberSubset x (e ω) → ∃ a, M.MemberSubset a ω ∧ e a = x) ∧
            (∀ A f, E.IsSetFunctionFromTo J f (e ω) (e A) →
              ∃ g, M.IsSetFunctionFromTo I g ω A ∧ e g = f) ∧
            (∀ A Y, E.MemberSubset Y (e A) → E.CardinalLessOrEqual J Y (e ω) →
              ∃ C, M.MemberSubset C A ∧ M.CardinalLessOrEqual I C ω ∧ e C = Y) ∧
            (∀ A, E.CardinalLessOrEqual J (e A) (e ω) ↔ M.CardinalLessOrEqual I A ω) ∧
            (∀ κ, M.IsHartogsNumber I κ ω → E.IsHartogsNumber J (e κ) (e ω)) ∧
            (∀ α, E.IsCofinality J (e ω) (e α) ↔ M.IsCofinality I ω α) ∧
            ∀ α cf, M.IsCofinality I cf α → M.mem ω cf → ∀ Y, E.MemberSubset Y (e α) →
              E.CardinalLessOrEqual J Y (e ω) → ∃ β, M.mem β α ∧ E.MemberSubset Y (e β) := by
  obtain ⟨ω, b, F, G, hω, h, hi, hc⟩ := collapse_iteration_closed_l hZFC X Y hδ
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y
  exact ⟨ω, b, F, G, hω, h, hi, hc, row_iteration_closed_preserves_l hZFC hω
    (collapse_rule_l hZFC ρ hω true) (collapse_rule_closed_l hZFC ρ hω) h⟩

/-- 同一参数化塌缩迭代同时返回全部闭区间、proper 阶段及任意种子的共同 N 区间引理。 -/
theorem collapse_iteration_pil_l (X Y : M.Domain) {δ} (hδ : M.IsOrdinal δ) :
    ∃ ω b F G, M.IsOmega ω ∧
      Row_iteration_d I true ω b coll_rule_s (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y) δ F G ∧
      (∀ β, Row_cl_stage_d I ω F G β) ∧
      (∀ β D V, Entry_d M β D F → Entry_d M β V G → Closed_d I D V D ω ∧ Proper_d I ω D V D) ∧
      ∀ A, M.CardinalLessOrEqual I A ω → ∃ χ H N,
        Hsub_d I ω χ H N ∧ M.MemberSubset A N ∧ M.mem δ N ∧
          ∀ β, M.mem β N → Row_pil_stage_d I F G b N β := by
  obtain ⟨ω, b, F, G, hω, h, hi, hc⟩ := collapse_iteration_closed_l hZFC X Y hδ
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push Y
  refine ⟨ω, b, F, G, hω, h, hi, (fun β D V hD hV => ?_),
    fun A ha => row_iteration_pr_l hZFC hω (collapse_rule_l hZFC ρ hω true) (collapse_rule_pr_l hZFC ρ hω) h ha⟩
  have hs := h.1.stages β D V hD hV
  exact ⟨hc β D V hD hV, closed_proper_l ⟨hs.order.refl, hs.order.trans⟩ hZFC hω (hc β D V hD hV)⟩

end YesMetaZFC.Model.Forcing.Internal
