import YesMetaZFC.Automation.ObjectTraceSemantics
import YesMetaZFC.Automation.ObjectHornSemantics

/-! # 对象轨迹的扩张与合并

轨迹是模型内部的集合，下面的包含与闭包不要求它在外部有限。
Horn 规则只正向查询前提是否属于轨迹，局部检查不依赖轨迹。
-/
namespace YesMetaZFC.Automation.ObjectTrace
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT
open RelationalTranslation NaturalRosserSemantics
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def Included (left right : 𝒩.Carrier .set) : Prop :=
  ∀ row, mem 𝒩 row left → mem 𝒩 row right

def Closed (step : FormulaTemplate.Binary) (trace : 𝒩.Carrier .set) : Prop :=
  ∀ row, mem 𝒩 row trace →
    step.body.satisfies (templateEnv (.cons row (.cons trace .nil)))

def Monotone (step : FormulaTemplate.Binary) : Prop :=
  ∀ {left right : 𝒩.Carrier .set}, Included left right →
    ∀ row, step.body.satisfies (templateEnv (.cons row (.cons left .nil))) →
      step.body.satisfies (templateEnv (.cons row (.cons right .nil)))

theorem horn_monotone (rules : List ObjectHorn.Rule) :
    Monotone (𝒩 := 𝒩) (ObjectHorn.step rules) := by
  intro left right hSubset row hRow
  obtain ⟨rule, hRule, hStep⟩ := (ObjectHornSemantics.step_satisfies rules row left).mp hRow
  obtain ⟨values, hBound, hHead, hGuard, hPremise⟩ :=
    (ObjectHornSemantics.rule_satisfies rule row left).mp hStep
  exact (ObjectHornSemantics.step_satisfies rules row right).mpr
    ⟨rule, hRule, (ObjectHornSemantics.rule_satisfies rule row right).mpr
      ⟨values, hBound, hHead, hGuard, fun premise h => hSubset _ (hPremise premise h)⟩⟩

theorem checked_monotone (rules : List ObjectHorn.Rule) (localCondition : FormulaTemplate.Unary) :
    Monotone (𝒩 := 𝒩) (ObjectCheckedTrace.step rules localCondition) := by
  intro left right hSubset row hRow
  change ((ObjectHorn.step rules).body.satisfies (templateEnv (.cons row (.cons left .nil))) ∧
    (localCondition (.fvar .here)).satisfies (templateEnv (.cons row (.cons left .nil)))) at hRow
  change _ ∧ _
  refine ⟨horn_monotone rules hSubset row hRow.1, ?_⟩
  exact (unary_satisfies localCondition _ _).mpr
    ((unary_satisfies localCondition (templateEnv (.cons row (.cons left .nil)))
      (.fvar .here)).mp hRow.2)

/-- 并集保留两侧的闭包。 -/
theorem closed_union (step : FormulaTemplate.Binary) (hMono : Monotone (𝒩 := 𝒩) step)
    {left right joined : 𝒩.Carrier .set}
    (hJoined : ∀ row, mem 𝒩 row joined ↔ mem 𝒩 row left ∨ mem 𝒩 row right)
    (hLeft : Closed step left) (hRight : Closed step right) : Closed step joined := by
  intro row hRow
  rcases (hJoined row).mp hRow with h | h
  · exact hMono (fun point hp => (hJoined point).mpr (Or.inl hp)) row (hLeft row h)
  · exact hMono (fun point hp => (hJoined point).mpr (Or.inr hp)) row (hRight row h)

/-- 新行已经满足规则时，插入该行保留闭包。 -/
theorem closed_insert (step : FormulaTemplate.Binary) (hMono : Monotone (𝒩 := 𝒩) step)
    {trace row extended : 𝒩.Carrier .set}
    (hExtended : ∀ point, mem 𝒩 point extended ↔ point = row ∨ mem 𝒩 point trace)
    (hTrace : Closed step trace)
    (hRow : step.body.satisfies (templateEnv (.cons row (.cons trace .nil)))) :
    Closed step extended := by
  have hSubset : Included trace extended := fun point hp => (hExtended point).mpr (Or.inr hp)
  intro point hp
  rcases (hExtended point).mp hp with rfl | h
  · exact hMono hSubset point hRow
  · exact hMono hSubset point (hTrace point h)

end YesMetaZFC.Automation.ObjectTrace

namespace YesMetaZFC.Automation.ObjectHorn.Expr
set_option autoImplicit false

@[simp] theorem list_variables {n : Nat} (fields : List (ObjectHorn.Expr n)) :
    (.list fields : ObjectHorn.Expr n).variables = fields.flatMap ObjectHorn.Expr.variables := by
  induction fields with
  | nil => rfl
  | cons head tail ih => simp [list, variables, ih]

end YesMetaZFC.Automation.ObjectHorn.Expr
