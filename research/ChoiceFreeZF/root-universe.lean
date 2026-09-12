import YesMetaZFC.Model.SmallGraph.Sets

namespace Zf_research
open YesMetaZFC.Model.SmallGraph
universe u

/-- 图的升阶只提升节点类型，所有边与良基证据都原样搬运。 -/
def ru_up (G : WF_graph.{u}) : WF_graph.{u+1} where
  Domain := ULift.{u+1,u} G.Domain
  nonempty := ⟨⟨G.root⟩⟩
  root := ⟨G.root⟩
  mem a b := G.mem a.down b.down
  wf := ⟨fun a => InvImage.accessible ULift.down (G.wf.apply a.down)⟩

theorem ru_up_bs (G : WF_graph.{u}) : G.toSG_graph.Bisim (ru_up G).toSG_graph := by
  apply SG_graph.bs_of_map ULift.up rfl
  · exact fun _ _ h => h
  · intro b c h
    exact ⟨c.down, h, rfl⟩

/-- 单个商值的升阶可直接用商消去，不选择代表元。 -/
def ru_set : SG_set.{u} → SG_set.{u+1} :=
  Quotient.lift (fun G => SG_set.mk (ru_up G)) (fun G H h => SG_set.mk_eq.mpr
    (SG_graph.bs_trans (SG_graph.bs_symm (ru_up_bs G))
      (SG_graph.bs_trans h (ru_up_bs H))))

theorem ru_mem (x y : SG_set.{u}) : ru_set x ∈ ru_set y ↔ x ∈ y := by
  induction x using Quotient.inductionOn with
  | _ G =>
    induction y using Quotient.inductionOn with
    | _ H =>
      change (ru_up G).toSG_graph.Raw_mem (ru_up H).toSG_graph ↔
        G.toSG_graph.Raw_mem H.toSG_graph
      constructor
      · rintro ⟨a, h, e⟩
        exact ⟨a.down, h, SG_graph.bs_trans (ru_up_bs G)
          (SG_graph.bs_trans e (SG_graph.bs_symm (ru_up_bs (H.at_node a.down))))⟩
      · rintro ⟨a, h, e⟩
        exact ⟨⟨a⟩, h, SG_graph.bs_trans (SG_graph.bs_symm (ru_up_bs G))
          (SG_graph.bs_trans e (ru_up_bs (H.at_node a)))⟩

/-- 将所有低层图同时纳入一个高层容器；指标是所有图，不挑选任何代表。 -/
def ru_box : SG_set.{u+1} := SG_set.mk (WF_graph.root_sum (fun G : WF_graph.{u} => ru_up G))

theorem ru_box_mem (x : SG_set.{u}) : ru_set x ∈ ru_box := by
  induction x using Quotient.inductionOn with
  | _ G => exact (SG_set.mem_sum _ _).mpr ⟨G, rfl⟩

/-- 这个容器不能下降成低层集合；否则该集合属于自身。 -/
theorem ru_box_not_low : ¬ ∃ x : SG_set.{u}, ru_box = ru_set x := by
  rintro ⟨x, h⟩
  have e := ru_box_mem x
  rw [h] at e
  have k : ∀ a : SG_set.{u}, ¬ a ∈ a := fun a =>
    SG_set.mem_wf.induction (C := fun a : SG_set.{u} => ¬ a ∈ a) a
      (fun a ih h => ih a h h)
  exact k x ((ru_mem x x).mp e)

#print axioms ru_up
#print axioms ru_set
#print axioms ru_mem
#print axioms ru_box
#print axioms ru_box_mem
#print axioms ru_box_not_low
end Zf_research
