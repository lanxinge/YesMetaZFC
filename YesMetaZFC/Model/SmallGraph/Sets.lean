import YesMetaZFC.Model.SmallGraph.RootSum

/-! # 良基小图的双模拟商

模型载体从起点固定在 `Type (u+1)`。成员关系直接由图的根成员定义，并验证
双模拟不变性；这里没有树展开、外部集合模型参数或代表元选择函数。
-/

namespace YesMetaZFC.Model.SmallGraph
universe u

abbrev graph_setoid : Setoid WF_graph.{u} where
  r G H := G.toSG_graph.Bisim H.toSG_graph
  iseqv := ⟨fun G => SG_graph.bs_refl G.toSG_graph,
    fun h => SG_graph.bs_symm h, fun h k => SG_graph.bs_trans h k⟩

/-- 全部良基有根小图按双模拟取商，载体层级此后保持不变。 -/
abbrev SG_set : Type (u + 1) := Quotient graph_setoid.{u}

namespace SG_set

def mk (G : WF_graph.{u}) : SG_set.{u} := Quotient.mk graph_setoid G

theorem mk_eq {G H : WF_graph.{u}} : mk G = mk H ↔ G.toSG_graph.Bisim H.toSG_graph :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- 商上的成员关系，不读取任选的图代表。 -/
def mem : SG_set.{u} → SG_set.{u} → Prop :=
  Quotient.lift₂ (fun G H => G.toSG_graph.Raw_mem H.toSG_graph)
    (fun _ _ _ _ h k => propext (SG_graph.mem_congr h k))

instance sg_membership : Membership SG_set.{u} SG_set.{u} where
  mem y x := mem x y

/-- 每个成员由同一小图中的一个根成员节点呈现。 -/
theorem mem_mk (G : WF_graph.{u}) (x : SG_set.{u}) :
    x ∈ mk G ↔ ∃ a, G.mem a G.root ∧ x = mk (G.at_node a) := by
  induction x using Quotient.inductionOn with
  | _ H =>
      change H.toSG_graph.Raw_mem G.toSG_graph ↔ _
      exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, mk_eq.mpr h⟩,
        fun ⟨a, ha, h⟩ => ⟨a, ha, mk_eq.mp h⟩⟩

/-- 模型外延性来自根成员的双向匹配，不把图呈现的字面相等当成集合等号。 -/
theorem ext {x y : SG_set.{u}} (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  induction x using Quotient.inductionOn with
  | _ G =>
      induction y using Quotient.inductionOn with
      | _ H =>
          apply mk_eq.mpr
          apply SG_graph.bs_children.mpr
          constructor
          · intro a ha
            have hz := (h (mk (G.at_node a))).mp ((mem_mk G _).mpr ⟨a, ha, rfl⟩)
            obtain ⟨b, hb, hab⟩ := (mem_mk H _).mp hz
            exact ⟨b, hb, mk_eq.mp hab⟩
          · intro b hb
            have hz := (h (mk (H.at_node b))).mpr ((mem_mk H _).mpr ⟨b, hb, rfl⟩)
            obtain ⟨a, ha, hab⟩ := (mem_mk G _).mp hz
            exact ⟨a, ha, mk_eq.mp hab.symm⟩

/-- 商成员关系的良基性由当前呈现图的节点归纳推出。 -/
theorem mem_wf : WellFounded (fun x y : SG_set.{u} => x ∈ y) := by
  refine ⟨fun x => ?_⟩
  induction x using Quotient.inductionOn with
  | _ G =>
      have h (a : G.Domain) : Acc (fun x y : SG_set.{u} => x ∈ y) (mk (G.at_node a)) := by
        apply G.wf.induction a
        intro a ih
        refine Acc.intro _ ?_
        intro y hy
        obtain ⟨b, hb, rfl⟩ := (mem_mk (G.at_node a) y).mp hy
        exact ih b hb
      exact h G.root

def empty : SG_set.{u} := mk WF_graph.empty

theorem not_mem_empty (x : SG_set.{u}) : ¬ x ∈ empty := by
  intro h
  obtain ⟨a, ha, _⟩ := (mem_mk WF_graph.empty x).mp h
  exact ha

/-- 每个模型集合都具有 `Type u` 中的实际成员指标族，允许重复呈现。 -/
theorem small_presentation (x : SG_set.{u}) :
    ∃ (ι : Type u) (f : ι → SG_set.{u}), ∀ z, z ∈ x ↔ ∃ i, z = f i := by
  induction x using Quotient.inductionOn with
  | _ G =>
      refine ⟨{a : G.Domain // G.mem a G.root}, fun a => mk (G.at_node a.1), ?_⟩
      intro z
      exact (mem_mk G z).trans
        ⟨fun ⟨a, ha, hz⟩ => ⟨⟨a, ha⟩, hz⟩, fun ⟨a, hz⟩ => ⟨a.1, a.2, hz⟩⟩

/-- 已给出图呈现时，小收集完全由有根并合直接计算。 -/
theorem mem_sum {ι : Type u} (F : ι → WF_graph.{u}) (z : SG_set.{u}) :
    z ∈ mk (WF_graph.root_sum F) ↔ ∃ i, z = mk (F i) := by
  induction z using Quotient.inductionOn with
  | _ G =>
      change G.toSG_graph.Raw_mem (SG_graph.root_sum (fun i => (F i).toSG_graph)) ↔ _
      rw [SG_graph.sum_mem]
      constructor
      · rintro ⟨i, h⟩
        exact ⟨i, mk_eq.mpr h⟩
      · rintro ⟨i, h⟩
        exact ⟨i, mk_eq.mp h⟩

/--
任意小指标族的值都可收集成模型集合。仅在此存在性证明内部使用 Lean 原生选择，
选择每个给定商值的呈现；输出图由已经构造的 `root_sum` 给出。
-/
theorem small_collect {ι : Type u} (f : ι → SG_set.{u}) :
    ∃ x : SG_set.{u}, ∀ z, z ∈ x ↔ ∃ i, z = f i := by
  obtain ⟨F, hF⟩ := Classical.axiomOfChoice (fun i => Quotient.exists_rep (f i))
  refine ⟨mk (WF_graph.root_sum F), fun z => (mem_sum F z).trans ?_⟩
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.trans (hF i)⟩, fun ⟨i, h⟩ => ⟨i, h.trans (hF i).symm⟩⟩

end SG_set
end YesMetaZFC.Model.SmallGraph
