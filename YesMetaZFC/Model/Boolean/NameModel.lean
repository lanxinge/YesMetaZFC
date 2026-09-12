import YesMetaZFC.Model.Boolean.Maximum
import YesMetaZFC.Model.Boolean.Soundness
import YesMetaZFC.SetTheory.Language

/-! # 标准布尔名称结构

同一小节点层的全部良基带权图形成名称域；布尔等号保留完整真值。
已经证明的图等号与隶属同余给出实际结构证书。
-/

namespace YesMetaZFC.Model.Boolean
open Logic Logic.FirstOrder SetTheory
universe u
variable {B : Type u} (𝔹 : CB_alg B)

def name_structure : BV_str.{0, 0, 0, u+1, u} ℒ B where
  Carrier _ := BV_graph.{u, u} B
  nonempty _ := ⟨BV_graph.empty 𝔹.toPO_bot⟩
  funcInterp f := nomatch f
  eqv := BV_graph.bv_eq 𝔹
  relv | .membership, .cons G (.cons H .nil) => BV_graph.bv_mem 𝔹 G H

attribute [local implicit_reducible] name_structure

theorem name_laws : BV_laws 𝔹.toBA_alg (name_structure 𝔹) where
  eq_refl := BV_graph.eq_refl 𝔹
  eq_symm := BV_graph.eq_symm 𝔹
  eq_trans := BV_graph.eq_trans 𝔹
  fn f := nomatch f
  rel := by
    intro r c xs ys h
    cases r
    cases xs; rename_i G xs; cases xs; rename_i H xs; cases xs
    cases ys; rename_i G' ys; cases ys; rename_i H' ys; cases ys
    refine ⟨𝔹.le_trans (𝔹.meet_mono (𝔹.le_meet h.1 h.2.1) (𝔹.le_refl _))
      (BV_graph.mem_congr 𝔹 G G' H H'), ?_⟩
    have hg : 𝔹.le c (BV_graph.bv_eq 𝔹 G' G) := by rw [BV_graph.eq_symm]; exact h.1
    have hh : 𝔹.le c (BV_graph.bv_eq 𝔹 H' H) := by rw [BV_graph.eq_symm]; exact h.2.1
    exact 𝔹.le_trans (𝔹.meet_mono (𝔹.le_meet hg hh) (𝔹.le_refl _))
      (BV_graph.mem_congr 𝔹 G' G H' H)

abbrev name_model := BV_str.model 𝔹 (name_structure 𝔹)

theorem name_rules : Sem_rules (name_model 𝔹) := BV_str.rules 𝔹 _ (name_laws 𝔹)

end YesMetaZFC.Model.Boolean
