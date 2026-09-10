import YesMetaZFC.Automation.ObjectHornRanking
import YesMetaZFC.Automation.ObjectSyntaxTransform
import YesMetaZFC.Automation.ObjectUnaryIteration
import YesMetaZFC.Automation.ObjectProjectQuotation

/-! # 语法变换与公共树转换的实际分层秩 -/
namespace YesMetaZFC.Automation.ObjectHornRanking
set_option autoImplicit false

def transformPlan : Plan where
  tags := [0, 1, 2, 3]
  width := fun tag => if tag = 0 then 3 else 5
  slot := fun tag => if h : tag = 0 then ⟨0, by simp [h]⟩ else ⟨3, by simp [h]⟩
  phase := fun tag => if tag = 0 then 0 else 1

theorem transform_valid : Valid transformPlan ObjectSyntaxTransform.rules :=
  check_sound _ _ (by decide +kernel)

def iterationPlan : Plan where
  tags := [0]
  width := fun _ => 4
  slot := fun _ => 1
  phase := fun _ => 0

theorem iteration_valid : Valid iterationPlan ObjectUnaryIteration.rules :=
  check_sound _ _ (by decide +kernel)

def projectPlan : Plan where
  tags := [0]
  width := fun _ => 2
  slot := fun _ => 0
  phase := fun _ => 0

theorem project_valid : Valid projectPlan ObjectProjectQuotation.rules :=
  check_sound _ _ (by decide +kernel)

end YesMetaZFC.Automation.ObjectHornRanking
