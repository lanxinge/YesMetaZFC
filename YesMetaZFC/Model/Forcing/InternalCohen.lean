import YesMetaZFC.Model.Forcing.InternalBoolean
import YesMetaZFC.Model.Forcing.CohenReal
import YesMetaZFC.Model.Henkin.Schedule

/-! # Cohen 条件与名称的实际内部实例

将正则开条件编码为有限二元序列编码的自然数子集。成员关系反映每个原条件，
所以编码单射；继而直接实例化通用内部名称编码及其求值往返。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open Boolean SmallGraph Logic.FirstOrder.Completeness.Henkin

private def bool_coding_l : NatCoding Bool where
  encode | false => 0 | true => 1
  injective := by intro a b h; cases a <;> cases b <;> cases h <;> rfl

def binary_code_l : List Bool → Nat := NatCoding.list_encode bool_coding_l

theorem binary_code_injective_l : Function.Injective binary_code_l :=
  NatCoding.list_encode_injective bool_coding_l

def cohen_code_graph_l (C : Cohen_l) : WF_graph.{0} :=
  real_graph_l (fun n => ∃ p : List Bool, binary_code_l p = n ∧ C.mem p)

theorem cohen_code_mem_l (C : Cohen_l) (p : List Bool) :
    nat_set_l (binary_code_l p) ∈ SG_set.mk (cohen_code_graph_l C) ↔ C.mem p := by
  change nat_set_l (binary_code_l p) ∈ real_set_l _ ↔ _
  rw [nat_mem_real_l]
  exact ⟨fun ⟨q, hq, h⟩ => binary_code_injective_l hq ▸ h, fun h => ⟨p, rfl, h⟩⟩

theorem cohen_code_injective_l : Function.Injective (fun C => SG_set.mk (cohen_code_graph_l C)) := by
  intro C D h
  dsimp only at h
  apply PO_pre.RO_l.ext_l (tree_order_l Bool).toPO_pre
  intro p
  rw [← cohen_code_mem_l C p, ← cohen_code_mem_l D p, h]

def cohen_condition_set_l : SG_set.{0} := condition_set_l cohen_code_graph_l

def cohen_order_set_l : SG_set.{0} := order_set_l cohen_algebra_l.le cohen_code_graph_l

theorem cohen_boolean_l : SetTheory.BooleanZF.Boolean_d sg_kpair_l cohen_condition_set_l
    cohen_order_set_l (SG_set.mk (cohen_code_graph_l cohen_algebra_l.bot)) :=
  boolean_model_l cohen_algebra_l.toBA_alg cohen_code_graph_l cohen_code_injective_l

/-- 已有 Cohen 实数名称现在是地模型中的实际集合对象。 -/
def cohen_internal_name_l : SG_set.{0} :=
  encode_set_l cohen_code_graph_l cohen_real_name_l cohen_real_name_l.root

theorem cohen_internal_name_spec_l :
    Name_d sg_structure cohen_condition_set_l cohen_internal_name_l :=
  encode_name_l cohen_code_graph_l cohen_real_name_l cohen_real_name_l.root

/-- 原 Cohen 条件谓词直接解释内部名称，自动得到与原求值的往返。 -/
theorem cohen_internal_val_l (U : Cohen_l → Prop) :
    Val_d sg_structure cohen_condition_set_l (code_pred_l cohen_code_graph_l U) cohen_internal_name_l
      (Forcing.val_l U cohen_real_name_l) :=
  encode_pred_val_l cohen_code_graph_l cohen_code_injective_l cohen_real_name_l U

end YesMetaZFC.Model.Forcing.Internal
