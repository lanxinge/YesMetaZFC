import YesMetaZFC.Model.Boolean.Closure

/-! # 布尔值基础公理

在“没有极小成员”的布尔部分，沿任意呈现图归纳排除其每个节点属于给定集合。
因此该部分也不含任何成员，得到原基础公理的完整真值不等式。
-/

namespace YesMetaZFC.Model.Boolean.BV_graph
universe u
variable {B : Type u} (𝔹 : CB_alg B)

def nonempty_value (G : BV_graph.{u, u} B) : B :=
  𝔹.iSup (fun H : BV_graph.{u, u} B => bv_mem 𝔹 H G)

def minimal (G H : BV_graph.{u, u} B) : B :=
  𝔹.iInf (fun K : BV_graph.{u, u} B => 𝔹.imp (bv_mem 𝔹 K G) (𝔹.neg (bv_mem 𝔹 K H)))

theorem foundation (G : BV_graph.{u, u} B) :
    𝔹.le (nonempty_value 𝔹 G)
      (𝔹.iSup (fun H : BV_graph.{u, u} B => 𝔹.meet (bv_mem 𝔹 H G) (minimal 𝔹 G H))) := by
  let d := 𝔹.iSup (fun H : BV_graph.{u, u} B => 𝔹.meet (bv_mem 𝔹 H G) (minimal 𝔹 G H))
  let c := 𝔹.neg d
  have h (H : BV_graph.{u, u} B) : 𝔹.le c (𝔹.neg (bv_mem 𝔹 H G)) := by
    have ha (a : H.Domain) : 𝔹.le c (𝔹.neg (bv_mem 𝔹 (H.at_node a) G)) := by
      induction a using H.wf.induction with
      | h a ih =>
        have hb := (bounded_all 𝔹 (H.at_node a) _ (stable_neg 𝔹 (stable_elem 𝔹 G)) c).mpr
          (fun b => 𝔹.le_trans (𝔹.meet_le_left _ _) (ih b b.2))
        have hm : 𝔹.le c (minimal 𝔹 G (H.at_node a)) := by
          apply (𝔹.le_iInf_iff _ _).mpr
          intro K
          apply (𝔹.le_imp_neg_iff _ _ _).mp
          exact 𝔹.le_trans hb (𝔹.iInf_le _ K)
        have hd : 𝔹.le (𝔹.meet c (bv_mem 𝔹 (H.at_node a) G)) d :=
          𝔹.le_trans (𝔹.le_meet (𝔹.meet_le_right _ _) (𝔹.le_trans (𝔹.meet_le_left _ _) hm))
            (𝔹.le_iSup (fun K : BV_graph.{u, u} B =>
              𝔹.meet (bv_mem 𝔹 K G) (minimal 𝔹 G K)) (H.at_node a))
        apply (𝔹.le_imp_iff _ _ _).mpr
        have hz := 𝔹.le_meet hd (𝔹.meet_le_left c (bv_mem 𝔹 (H.at_node a) G))
        simpa only [c, BA_alg.meet_neg] using hz
    exact ha H.root
  apply (𝔹.le_iff_meet_neg _ _).mpr
  rw [𝔹.meet_comm, nonempty_value, 𝔹.meet_iSup, 𝔹.iSup_le_iff]
  exact fun H => (𝔹.le_imp_iff _ _ _).mp (h H)

end YesMetaZFC.Model.Boolean.BV_graph
