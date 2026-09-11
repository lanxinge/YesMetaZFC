import YesMetaZFC.Model.ZFC.Pure.PureSourceHornConstruction
import YesMetaZFC.Model.ZFC.Pure.PureSourceCodingInversion

/-! # 任意内部 Horn 轨迹的根行反演 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceHornConstruction
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceInfinity PureSourceTraceComposition
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem rule_cases_bounds (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectHorn.step rules) root) :
    ∃ rule ∈ rules, ∃ values : Fin rule.arity → 𝒩.Carrier .set,
      (∀ i, mem 𝒩 (values i) (w 𝒩)) ∧ root = exprValue 𝒩 values rule.head ∧
      (∀ i, mem 𝒩 (values i) (suc 𝒩 (exprValue 𝒩 values rule.head))) ∧
      (∀ guard ∈ rule.guards, mem 𝒩 (exprValue 𝒩 values guard.1) (exprValue 𝒩 values guard.2)) ∧
      ∀ premise ∈ rule.premises, Witness (ObjectHorn.step rules) (exprValue 𝒩 values premise) := by
  obtain ⟨trace, hTrace, hRoot, hClosed⟩ := hg
  obtain ⟨rule, hRule, hStep⟩ := (step_satisfies rules root trace).mp (hClosed root hRoot)
  obtain ⟨values, hBounds, hHead, hGuards, hPremises⟩ := (rule_satisfies rule root trace).mp hStep
  exact ⟨rule, hRule, values, (fun i => member_natural h𝒩 ((omega_closed h𝒩).2 root hr) (hBounds i)),
    hHead, (fun i => hHead ▸ hBounds i), hGuards, fun premise hp => ⟨trace, hTrace, hPremises premise hp, hClosed⟩⟩

theorem rule_cases (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectHorn.step rules) root) :
    ∃ rule ∈ rules, ∃ values : Fin rule.arity → 𝒩.Carrier .set,
      (∀ i, mem 𝒩 (values i) (w 𝒩)) ∧ root = exprValue 𝒩 values rule.head ∧
      (∀ guard ∈ rule.guards, mem 𝒩 (exprValue 𝒩 values guard.1) (exprValue 𝒩 values guard.2)) ∧
      ∀ premise ∈ rule.premises, Witness (ObjectHorn.step rules) (exprValue 𝒩 values premise) := by
  obtain ⟨rule, hRule, values, hv, he, _, hg, hp⟩ := rule_cases_bounds h𝒩 rules hr hg
  exact ⟨rule, hRule, values, hv, he, hg, hp⟩

theorem node_head_injective (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {n tag other : Nat} (values : Fin n → 𝒩.Carrier .set) (hv : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {fields : List (𝒩.Carrier .set)} {expressions : List (ObjectHorn.Expr n)}
    (hf : ∀ value ∈ fields, mem 𝒩 value (w 𝒩))
    (he : PureSourceCoding.node 𝒩 tag fields = exprValue 𝒩 values (.node (.literal other) expressions)) :
    tag = other ∧ fields = expressions.map (exprValue 𝒩 values) := by
  rw [expr_node] at he
  exact PureSourceCodingInversion.node_injective h𝒩 hf (by
    intro value hValue
    obtain ⟨expr, _, rfl⟩ := List.mem_map.mp hValue
    exact PureSourceHorn.expr_natural h𝒩 hv expr) he

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceHornConstruction
