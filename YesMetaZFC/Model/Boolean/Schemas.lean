import YesMetaZFC.Model.Boolean.Project
import YesMetaZFC.SetTheory.Axioms.ZFC

/-! # 原 ZFC 的带参数模式

模式正文只要求尊重布尔等号，这一性质已经对全部开放 Project 公式证明。
分离和收集保留原参数、绑定次序与原公理形状。
-/

namespace YesMetaZFC.Model.Boolean.BV_project
open SetTheory SetTheory.Definitional BV_graph
universe u
variable {B : Type u} (𝔹 : CB_alg B)

attribute [local implicit_reducible] name_structure Project.FirstOrderSemantics.reduct SetTheory.signature

theorem separation_core {n} (φ : Project.UnarySchema n) (ρ : Env 𝔹 n) :
    𝔹.le 𝔹.top (value 𝔹 (Axioms.Schema.separationCore φ) ρ) := by
  simp only [Axioms.Schema.separationCore, value, value_rename, SetTheory.Env.reindex_push_unaryUnderTwo]
  change 𝔹.le 𝔹.top (𝔹.iInf (fun G : BV_graph.{u, u} B => 𝔹.iSup (fun C : BV_graph.{u, u} B =>
    𝔹.iInf (fun H : BV_graph.{u, u} B => 𝔹.iff (bv_mem 𝔹 H C)
      (𝔹.meet (bv_mem 𝔹 H G) (value 𝔹 φ.body (ρ.push H)))))))
  apply (𝔹.le_iInf_iff _ _).mpr
  intro G
  let p (H : BV_graph.{u, u} B) := value 𝔹 φ.body (ρ.push H)
  apply 𝔹.le_trans _ (𝔹.le_iSup (fun C : BV_graph.{u, u} B => 𝔹.iInf (fun H : BV_graph.{u, u} B =>
    𝔹.iff (bv_mem 𝔹 H C) (𝔹.meet (bv_mem 𝔹 H G) (p H)))) (sep 𝔹 G p))
  exact (𝔹.le_iInf_iff _ _).mpr (fun H => (𝔹.valid_iff_iff _ _).mpr
    (sep_mem 𝔹 G p (value_stable 𝔹 φ.body ρ) H))

theorem collection_core {n} (φ : Project.BinarySchema n) (ρ : Env 𝔹 n) :
    𝔹.le 𝔹.top (value 𝔹 (Axioms.Schema.collectionCore φ) ρ) := by
  simp only [Axioms.Schema.collectionCore, Project.Formula.forallMem, Project.Formula.existsMem,
    value, value_rename, SetTheory.Env.reindex_push_binaryUnderOne, SetTheory.Env.reindex_push_binaryUnderTwo]
  let R (G H : BV_graph.{u, u} B) := value 𝔹 φ.body ((ρ.push G).push H)
  change 𝔹.le 𝔹.top (𝔹.iInf (fun G : BV_graph.{u, u} B => 𝔹.imp
    (𝔹.iInf (fun H : BV_graph.{u, u} B => 𝔹.imp (bv_mem 𝔹 H G) (𝔹.iSup (R H))))
    (𝔹.iSup (fun C : BV_graph.{u, u} B => 𝔹.iInf (fun H : BV_graph.{u, u} B =>
      𝔹.imp (bv_mem 𝔹 H G) (𝔹.iSup (fun K => 𝔹.meet (bv_mem 𝔹 K C) (R H K))))))))
  apply (𝔹.le_iInf_iff _ _).mpr
  intro G
  rw [𝔹.valid_imp_iff]
  obtain ⟨C, hC⟩ := BV_graph.collection 𝔹 G R (fun H => value_stable 𝔹 φ.body (ρ.push H))
  apply 𝔹.le_trans _ (𝔹.le_iSup (fun C : BV_graph.{u, u} B => 𝔹.iInf (fun H : BV_graph.{u, u} B =>
    𝔹.imp (bv_mem 𝔹 H G) (𝔹.iSup (fun K => 𝔹.meet (bv_mem 𝔹 K C) (R H K))))) C)
  apply (bounded_all 𝔹 G _ (stable_sup 𝔹 _ (fun K => stable_meet 𝔹 (stable_const 𝔹 _)
    (value_stable_left 𝔹 φ.body ρ K))) _).mpr
  intro a
  apply 𝔹.le_trans _ (hC a)
  exact 𝔹.imp_use (𝔹.le_trans (𝔹.meet_le_left _ _)
    (𝔹.iInf_le (fun H : BV_graph.{u, u} B => 𝔹.imp (bv_mem 𝔹 H G) (𝔹.iSup (R H))) (G.at_node a)))
    (𝔹.le_trans (𝔹.meet_le_right _ _) (mem_root 𝔹 G a))

end YesMetaZFC.Model.Boolean.BV_project
