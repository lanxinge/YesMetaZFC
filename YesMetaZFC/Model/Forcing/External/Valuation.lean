import YesMetaZFC.Model.Boolean.Names
import YesMetaZFC.Model.SmallGraph.Sets

/-! # 名称的图求值

保留被接受的带权成员边，所得图仍然良基。求值只取双模拟商，既不选择名称
代表元，也不要求布尔代数完备；滤子性质在后续真值定理中才使用。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean SmallGraph
universe u v
variable {B : Type v}

/-- 名称求值的图呈现；非成员边及未被接受的标签均不产生成员。 -/
def val_graph_l (U : B → Prop) (G : BV_graph.{u, v} B) : WF_graph.{u} where
  Domain := G.Domain
  nonempty := G.nonempty
  mem a b := G.mem a b ∧ U (G.val a b)
  root := G.root
  wf := ⟨fun a => G.wf.induction a fun a ih =>
    Acc.intro a fun b h => ih b h.1⟩

def val_l (U : B → Prop) (G : BV_graph.{u, v} B) : SG_set.{u} :=
  SG_set.mk (val_graph_l U G)

/-- 纸面递归式：τᴳ = {σᴳ | (σ,b) ∈ τ 且 b ∈ G}。 -/
theorem val_mem_l (U : B → Prop) (G : BV_graph.{u, v} B) (x : SG_set.{u}) :
    x ∈ val_l U G ↔ ∃ a : G.Child G.root,
      U (G.val a G.root) ∧ x = val_l U (G.at_node a) := by
  rw [val_l, SG_set.mem_mk]
  exact ⟨fun ⟨a, h, e⟩ => ⟨⟨a, h.1⟩, h.2, e⟩,
    fun ⟨a, h, e⟩ => ⟨a.1, ⟨a.2, h⟩, e⟩⟩

/-- 规范名称在原成员图的每条边上标记顶值。 -/
def check_graph_l (𝔹 : BA_alg B) (G : WF_graph.{u}) : BV_graph.{u, v} B where
  toWF_graph := G
  val _ _ := 𝔹.top

theorem val_check_l (𝔹 : BA_alg B) (U : B → Prop) (h : U 𝔹.top)
    (G : WF_graph.{u}) : val_l U (check_graph_l 𝔹 G) = SG_set.mk G := by
  apply SG_set.mk_eq.mpr
  exact SG_graph.bs_of_map id rfl (fun _ _ k => k.1)
    (fun _ a k => ⟨a, ⟨k, h⟩, rfl⟩)

/-- 商集合的规范名称存在；存在证明不向外导出代表元选择函数。 -/
theorem check_exists_l (𝔹 : BA_alg B) (x : SG_set.{u}) :
    ∃ G : BV_graph.{u, v} B, ∀ U, U 𝔹.top → val_l U G = x := by
  induction x using Quotient.inductionOn with
  | _ G => exact ⟨check_graph_l 𝔹 G, fun U h => val_check_l 𝔹 U h G⟩

/-- 全宿主名称域的求值像就是全宿主集合域，不能据此声称得到了真扩张。 -/
theorem val_surjective_l (𝔹 : BA_alg B) (U : B → Prop) (h : U 𝔹.top)
    (x : SG_set.{u}) : ∃ G : BV_graph.{u, v} B, val_l U G = x := by
  obtain ⟨G, hG⟩ := check_exists_l 𝔹 x
  exact ⟨G, hG U h⟩

end YesMetaZFC.Model.Forcing
