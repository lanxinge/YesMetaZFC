import YesMetaZFC.Automation.ObjectTransformRanking
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaTable
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaObjectGraph

/-! # 模式正文、重命名与重命名表的实际分层秩 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaReflectionPlans
open _root_.YesMetaZFC.Automation ObjectHornRanking
set_option autoImplicit false

def bodyPlan : Plan where
  tags := [0, 1]
  width := fun _ => 2
  slot := fun _ => 1
  phase := fun _ => 0

theorem body_valid : Valid bodyPlan SchemaObjectGraph.Body.rules :=
  check_sound _ _ (by decide +kernel)

def renamePlan : Plan where
  tags := [0, 1, 2, 3, 4, 5]
  width := fun tag => if tag = 0 then 3 else if tag = 4 then 2 else 4
  slot := fun tag => if h : tag = 0 then ⟨0, by simp [h]⟩
    else if h4 : tag = 4 then ⟨1, by simp [h4]⟩
    else if h1 : tag = 1 then ⟨1, by simp [h, h4]⟩ else ⟨2, by simp [h, h4]⟩
  phase := fun tag => match tag with
    | 0 | 4 => 0
    | 1 => 1
    | 3 => 2
    | 2 => 3
    | _ => 4

theorem rename_valid : Valid renamePlan SchemaObjectGraph.Rename.rules :=
  check_sound _ _ (by decide +kernel)

def tablePlan : Plan where
  tags := [0, 1]
  width := fun _ => 3
  slot := fun _ => 1
  phase := fun tag => tag

theorem table_valid : Valid tablePlan (ObjectRangeTable.rules SchemaTable.program) :=
  check_sound _ _ (by decide +kernel)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaReflectionPlans
