import YesMetaZFC.Model.ZFC.Pure.PureSourceHornElimination

/-! # 任意内部已检查轨迹的根行反演与规则合并

前提重用原内部集合轨迹；构造端合并这些集合并插入头行。
仅规则的参数和前提个数固定，不要求轨迹在外部有限。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceCheckedConstruction
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceInfinity PureSourceTraceComposition
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics ObjectTrace
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem step_satisfies (rules : List ObjectHorn.Rule) (localCondition : FormulaTemplate.Unary)
    (root trace : 𝒩.Carrier .set) :
    (ObjectCheckedTrace.step rules localCondition).body.satisfies (templateEnv (.cons root (.cons trace .nil))) ↔
      (ObjectHorn.step rules).body.satisfies (templateEnv (.cons root (.cons trace .nil))) ∧
      localCondition.body.satisfies (templateEnv (.cons root .nil)) := by
  change (_ ∧ _) ↔ (_ ∧ _)
  exact and_congr Iff.rfl (NaturalRosserSemantics.unary_satisfies localCondition _ _)

theorem rule_cases_bounds (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) (localCondition : FormulaTemplate.Unary)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectCheckedTrace.step rules localCondition) root) :
    ∃ rule ∈ rules, ∃ values : Fin rule.arity → 𝒩.Carrier .set,
      (∀ i, mem 𝒩 (values i) (w 𝒩)) ∧ root = exprValue 𝒩 values rule.head ∧
      (∀ i, mem 𝒩 (values i) (suc 𝒩 (exprValue 𝒩 values rule.head))) ∧
      (∀ guard ∈ rule.guards, mem 𝒩 (exprValue 𝒩 values guard.1) (exprValue 𝒩 values guard.2)) ∧
      localCondition.body.satisfies (templateEnv (.cons (exprValue 𝒩 values rule.head) .nil)) ∧
      ∀ premise ∈ rule.premises, Witness (ObjectCheckedTrace.step rules localCondition) (exprValue 𝒩 values premise) := by
  obtain ⟨trace, hTrace, hRoot, hClosed⟩ := hg
  have hRow := (step_satisfies rules localCondition root trace).mp (hClosed root hRoot)
  obtain ⟨rule, hRule, hStep⟩ := (ObjectHornSemantics.step_satisfies rules root trace).mp hRow.1
  obtain ⟨values, hBounds, hHead, hGuards, hPremises⟩ := (rule_satisfies rule root trace).mp hStep
  exact ⟨rule, hRule, values, (fun i => member_natural h𝒩 ((omega_closed h𝒩).2 root hr) (hBounds i)),
    hHead, (fun i => hHead ▸ hBounds i), hGuards, hHead ▸ hRow.2,
    fun premise hp => ⟨trace, hTrace, hPremises premise hp, hClosed⟩⟩

theorem rule_intro_bounds (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (rules : List ObjectHorn.Rule) (localCondition : FormulaTemplate.Unary)
    (rule : ObjectHorn.Rule) (hRule : rule ∈ rules) (values : Fin rule.arity → 𝒩.Carrier .set)
    (hv : ∀ i, mem 𝒩 (values i) (w 𝒩))
    (hBounds : ∀ i, mem 𝒩 (values i) (suc 𝒩 (exprValue 𝒩 values rule.head)))
    (hGuards : ∀ guard ∈ rule.guards, mem 𝒩 (exprValue 𝒩 values guard.1) (exprValue 𝒩 values guard.2))
    (hLocal : localCondition.body.satisfies (templateEnv (.cons (exprValue 𝒩 values rule.head) .nil)))
    (hPremises : ∀ premise ∈ rule.premises, Witness (ObjectCheckedTrace.step rules localCondition) (exprValue 𝒩 values premise)) :
    Witness (ObjectCheckedTrace.step rules localCondition) (exprValue 𝒩 values rule.head) := by
  obtain ⟨trace, hTrace, hMembers, hClosed⟩ := collect h𝒩 _ (checked_monotone rules localCondition)
    (rule.premises.map (exprValue 𝒩 values)) (by
      intro root hRoot
      obtain ⟨premise, hp, rfl⟩ := List.mem_map.mp hRoot
      exact hPremises premise hp)
  have hRow := (step_satisfies rules localCondition (exprValue 𝒩 values rule.head) trace).mpr
    ⟨(ObjectHornSemantics.step_satisfies rules (exprValue 𝒩 values rule.head) trace).mpr
      ⟨rule, hRule, (rule_satisfies rule _ trace).mpr ⟨values, hBounds, rfl, hGuards,
        (fun premise hp => hMembers _ (List.mem_map.mpr ⟨premise, hp, rfl⟩))⟩⟩, hLocal⟩
  obtain ⟨extended, hBound, _, hRoot, hExtended⟩ := insert h𝒩 _ (checked_monotone rules localCondition)
    hTrace (PureSourceHorn.expr_natural h𝒩 hv rule.head) hClosed hRow
  exact ⟨extended, hBound, hRoot, hExtended⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceCheckedConstruction
