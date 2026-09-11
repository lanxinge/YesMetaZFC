import YesMetaZFC.Model.SmallGraph.Bisimulation

/-! # 小图族的有根并合

在互不相交的图族上添一个新根。指标与每个节点域都在 `Type u`，并合节点域
仍在 `Type u`；后续收集、幂集和力迫名的小支撑构造复用这个闭包步骤。
-/

namespace YesMetaZFC.Model.SmallGraph
universe u

namespace SG_graph
variable {ι : Type u} (F : ι → SG_graph.{u})

/-- 新根的成员是各分量的根，其余边完全保留分量中的原边。 -/
inductive Sum_edge : Option (Σ i, (F i).Domain) → Option (Σ i, (F i).Domain) → Prop where
  | root (i : ι) : Sum_edge (some ⟨i, (F i).root⟩) none
  | step (i : ι) {a b : (F i).Domain} (h : (F i).mem a b) :
      Sum_edge (some ⟨i, a⟩) (some ⟨i, b⟩)

def root_sum : SG_graph.{u} where
  Domain := Option (Σ i, (F i).Domain)
  nonempty := ⟨none⟩
  mem := Sum_edge F
  root := none

theorem sum_step {i : ι} {b : (F i).Domain} {c}
    (h : Sum_edge F c (some ⟨i, b⟩)) :
    ∃ a, (F i).mem a b ∧ c = some ⟨i, a⟩ := by
  cases h with
  | step i h => exact ⟨_, h, rfl⟩

/-- 分量嵌入在任意观察根处精确保留双模拟类型。 -/
theorem sum_at (i : ι) (a : (F i).Domain) :
    ((F i).at_node a).Bisim ((root_sum F).at_node (some ⟨i, a⟩)) := by
  apply bs_of_map (fun b => some ⟨i, b⟩) rfl
  · intro b c h; exact Sum_edge.step i h
  · intro b c h
    obtain ⟨a, ha, hc⟩ := sum_step F h
    exact ⟨a, ha, hc.symm⟩

/-- 有根并合所表示的成员恰好是给定图族的各个分量。 -/
theorem sum_mem (G : SG_graph.{u}) : G.Raw_mem (root_sum F) ↔ ∃ i, G.Bisim (F i) := by
  constructor
  · rintro ⟨c, hc, hG⟩
    change Sum_edge F c none at hc
    cases hc with
    | root i => exact ⟨i, bs_trans hG (bs_symm (sum_at F i _))⟩
  · rintro ⟨i, h⟩
    exact ⟨some ⟨i, (F i).root⟩, Sum_edge.root i, bs_trans h (sum_at F i _)⟩

/-- 分量良基时，并合也良基；只对当前分量的实际边关系归纳。 -/
theorem sum_wf (hF : ∀ i, WellFounded (F i).mem) : WellFounded (root_sum F).mem := by
  have h (i : ι) (a : (F i).Domain) : Acc (Sum_edge F) (some ⟨i, a⟩) := by
    apply (hF i).induction a
    intro a ih
    refine Acc.intro _ ?_
    intro c hc
    obtain ⟨b, hb, rfl⟩ := sum_step F hc
    exact ih b hb
  refine ⟨fun a => ?_⟩
  cases a with
  | some a => exact h a.1 a.2
  | none =>
      refine Acc.intro _ ?_
      intro c hc
      cases hc with
      | root i => exact h i _

end SG_graph

/-- ZFC 图呈现的具体良基子类；不向通用模型或原始小图施加此条件。 -/
structure WF_graph extends SG_graph.{u} where
  wf : WellFounded mem

namespace WF_graph

abbrev at_node (G : WF_graph.{u}) (a : G.Domain) : WF_graph.{u} where
  toSG_graph := G.toSG_graph.at_node a
  wf := G.wf

def empty : WF_graph.{u} where
  toSG_graph := SG_graph.empty
  wf := SG_graph.empty_wf

/-- 具有实际良基性证明的小图并合。 -/
def root_sum {ι : Type u} (F : ι → WF_graph.{u}) : WF_graph.{u} where
  toSG_graph := SG_graph.root_sum (fun i => (F i).toSG_graph)
  wf := SG_graph.sum_wf _ (fun i => (F i).wf)

end WF_graph
end YesMetaZFC.Model.SmallGraph
