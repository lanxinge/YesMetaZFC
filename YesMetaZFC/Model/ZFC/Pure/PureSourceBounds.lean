import YesMetaZFC.Model.ZFC.Pure.PureSourceInfinity
import YesMetaZFC.Automation.ObjectTraceSemantics

/-! # 任意原模型中的幂集界与轨迹载体

幂集的原定义在全部输入上确定其成员。因此自然数轨迹的候选集合在约化再规范
重扩张后保持，且候选轨迹的每一行都是模型内部自然数。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceBounds
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

abbrev powerset (𝒩 : Structure.{0,0,0,x} signature) (source : 𝒩.Carrier .set) :=
  𝒩.funcInterp .powerSet (.cons source .nil)

theorem power_spec (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (source element : 𝒩.Carrier .set) :
    mem 𝒩 element (powerset 𝒩 source) ↔
      ∀ member, mem 𝒩 member element → mem 𝒩 member source := by
  have hProof := Derives.theory_weaken
    (fun h => intrinsic_zfc_arithmetic_support.contains_function_predicate
      (relation_plane_theory_subset_function_predicate_theory
        (power_set_operator_theory_subset_relation_plane_theory h)))
    (mem_power_set_term_iff_subset (Γ := [])
      (.fvar .here : SetOpenTerm [.set,.set]) (.fvar (.there .here)))
  have h := hProof.sound h𝒩 (templateEnv (.cons source (.cons element .nil)))
    (by intro formula hMember; cases hMember)
  change (mem 𝒩 element (powerset 𝒩 source) ↔
    𝒩.relInterp .subset (.cons element (.cons source .nil))) at h
  exact h.trans (PureZFCModels.source_subset h𝒩 element source)

theorem power_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (source : 𝒩.Carrier .set) :
    powerset 𝒩 source = powerset (canonical h𝒩) source := by
  apply PureModel.extensionality (PureZFCModels.reduct_models h𝒩)
  intro element
  exact (power_spec h𝒩 source element).trans
    (PureFinalBasic.power_value (PureZFCModels.reduct_models h𝒩) source element).symm

/-- 对象证明图实际使用的整个轨迹量词界保持。 -/
theorem trace_bound_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    powerset 𝒩 (w 𝒩) = powerset (canonical h𝒩) (w (canonical h𝒩)) := by
  rw [power_agrees h𝒩, omega_agrees h𝒩]

theorem trace_row_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {trace row : 𝒩.Carrier .set}
    (hTrace : mem 𝒩 trace (powerset 𝒩 (w 𝒩))) (hRow : mem 𝒩 row trace) :
    mem 𝒩 row (w 𝒩) :=
  (power_spec h𝒩 (w 𝒩) trace).mp hTrace row hRow

/-- 相同根值下，只需对应候选轨迹内的自然数行，无须比较其他输入上的局部解释。 -/
theorem trace_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (step : FormulaTemplate.Binary) {bound free : SetContext}
    (env : Env 𝒩 bound free) (canonicalEnv : Env (canonical h𝒩) bound free)
    (root : SetTerm bound free) (hRoot : root.eval env = root.eval canonicalEnv)
    (hStep : ∀ trace, mem 𝒩 trace (powerset 𝒩 (w 𝒩)) →
      ∀ row, mem 𝒩 row trace → mem 𝒩 row (w 𝒩) →
        (step.body.satisfies (templateEnv (.cons row (.cons trace .nil)) : Env 𝒩 [] [.set,.set]) ↔
          step.body.satisfies (templateEnv (.cons row (.cons trace .nil)) :
            Env (canonical h𝒩) [] [.set,.set]))) :
    (_root_.YesMetaZFC.Automation.ObjectTrace.condition step ωₘ root).satisfies env ↔
      (_root_.YesMetaZFC.Automation.ObjectTrace.condition step ωₘ root).satisfies canonicalEnv := by
  rw [_root_.YesMetaZFC.Automation.ObjectTrace.condition_satisfies,
    _root_.YesMetaZFC.Automation.ObjectTrace.condition_satisfies]
  change (∃ trace, mem 𝒩 trace (powerset 𝒩 (w 𝒩)) ∧ mem 𝒩 (root.eval env) trace ∧
    ∀ row, mem 𝒩 row trace → step.body.satisfies
      (templateEnv (.cons row (.cons trace .nil)) : Env 𝒩 [] [.set,.set])) ↔
    (∃ trace, mem 𝒩 trace (powerset (canonical h𝒩) (w (canonical h𝒩))) ∧
      mem 𝒩 (root.eval canonicalEnv) trace ∧
        ∀ row, mem 𝒩 row trace → step.body.satisfies
          (templateEnv (.cons row (.cons trace .nil)) : Env (canonical h𝒩) [] [.set,.set]))
  rw [← trace_bound_agrees h𝒩, ← hRoot]
  constructor
  · rintro ⟨trace, hTrace, hRootMember, hClosed⟩
    exact ⟨trace, hTrace, hRootMember, fun row hRow =>
      (hStep trace hTrace row hRow (trace_row_natural h𝒩 hTrace hRow)).mp (hClosed row hRow)⟩
  · rintro ⟨trace, hTrace, hRootMember, hClosed⟩
    exact ⟨trace, hTrace, hRootMember, fun row hRow =>
      (hStep trace hTrace row hRow (trace_row_natural h𝒩 hTrace hRow)).mpr (hClosed row hRow)⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceBounds
