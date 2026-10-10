import YesMetaZFC.Model.Forcing.Internal.Forcing.Conditions

/-! # 实际地模型泛型滤子实例

二元布尔条件在原小图 ZFC 模型中编码，顶原子的主滤子遇到该模型的每个稠密集。
该实例验证内部泛型接口；不把它称为无原子 Cohen 力迫的泛型滤子。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SmallGraph
attribute [local implicit_reducible] sg_model SetTheory.Definitional.Project.FirstOrderSemantics.reduct

def two_code_l : Bool → WF_graph.{0}
  | false => WF_graph.empty
  | true => WF_graph.root_sum (fun _ : PUnit => WF_graph.empty)

theorem two_ne_l : SG_set.mk (two_code_l true) ≠ SG_set.mk (two_code_l false) := by
  intro h
  have hm : SG_set.empty ∈ SG_set.mk (two_code_l true) :=
    (SG_set.mem_sum _ _).mpr ⟨PUnit.unit, rfl⟩
  exact SG_set.not_mem_empty _ (h ▸ hm)

theorem two_code_injective_l : Function.Injective (fun b => SG_set.mk (two_code_l b)) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exact False.elim (two_ne_l h.symm)
  · exact False.elim (two_ne_l h)
  · rfl

def two_order_l : PO_pre Bool where
  le a b := a = false ∨ b = true
  le_refl a := by cases a <;> simp
  le_trans := by intro a b c h k; cases a <;> cases b <;> cases c <;> simp_all

def two_conditions_l : SG_set.{0} := condition_set_l two_code_l
def two_relation_l : SG_set.{0} := order_set_l two_order_l.le two_code_l
def two_zero_l : SG_set.{0} := SG_set.mk (two_code_l false)
def two_one_l : SG_set.{0} := SG_set.mk (two_code_l true)

theorem two_cond_order_l : Cond_order_d sg_structure two_conditions_l two_relation_l two_zero_l where
  refl p hp := by
    obtain ⟨a, rfl⟩ := (SG_set.mem_sum two_code_l p).mp hp
    exact (order_mem_l two_order_l.le two_code_l two_code_injective_l a a).mpr (two_order_l.le_refl a)
  trans p q r hp hq hr h k := by
    obtain ⟨a, rfl⟩ := (SG_set.mem_sum two_code_l p).mp hp
    obtain ⟨b, rfl⟩ := (SG_set.mem_sum two_code_l q).mp hq
    obtain ⟨c, rfl⟩ := (SG_set.mem_sum two_code_l r).mp hr
    exact (order_mem_l two_order_l.le two_code_l two_code_injective_l a c).mpr
      (two_order_l.le_trans ((order_mem_l _ _ two_code_injective_l a b).mp h)
        ((order_mem_l _ _ two_code_injective_l b c).mp k))
  zero p hp hz := by
    obtain ⟨a, rfl⟩ := (SG_set.mem_sum two_code_l p).mp hp
    have h := (order_mem_l two_order_l.le two_code_l two_code_injective_l a false).mp hz
    have ha : a = false := h.elim id (fun h => Bool.noConfusion h)
    exact congrArg (fun a => SG_set.mk (two_code_l a)) ha

def two_filter_l (p : SG_set.{0}) : Prop :=
  p ∈ two_conditions_l ∧ Entry_d sg_structure two_one_l p two_relation_l

theorem two_generic_l : Generic_d sg_structure two_conditions_l two_relation_l two_zero_l two_filter_l := by
  apply generic_atom_l two_cond_order_l
    (a := two_one_l) ((SG_set.mem_sum two_code_l _).mpr ⟨true, rfl⟩) two_ne_l
  intro p hp
  obtain ⟨a, rfl⟩ := (SG_set.mem_sum two_code_l p).mp hp.1
  cases a
  · exact False.elim (hp.2.1 rfl)
  · exact two_cond_order_l.refl _ ((SG_set.mem_sum two_code_l _).mpr ⟨true, rfl⟩)

end YesMetaZFC.Model.Forcing.Internal
