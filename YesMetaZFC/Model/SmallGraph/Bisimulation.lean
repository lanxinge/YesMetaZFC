import YesMetaZFC.Model.SetTheory.Structure

/-! # 有根小图与双模拟

节点在 `Type u`，图的呈现类型在 `Type (u+1)`。原始图不要求良基；
良基性只在本次 ZFC 模型的呈现子类中使用。边的方向是“成员节点 → 集合节点”。
-/

namespace YesMetaZFC.Model.SmallGraph
universe u v w

/-- 在已有隶属图数据上指定根，不重建另一套集合论结构。 -/
structure SG_graph extends SetTheory.Structure.{u} where
  root : Domain

namespace SG_graph

/-- 改变观察根，节点与边保持原样。 -/
abbrev at_node (G : SG_graph.{u}) (a : G.Domain) : SG_graph.{u} where
  toStructure := G.toStructure
  root := a

/-- 双模拟的局部来回条件。 -/
def BS_rel (G : SG_graph.{u}) (H : SG_graph.{v}) (R : G.Domain → H.Domain → Prop) : Prop :=
  ∀ a b, R a b →
    (∀ a', G.mem a' a → ∃ b', H.mem b' b ∧ R a' b') ∧
    (∀ b', H.mem b' b → ∃ a', G.mem a' a ∧ R a' b')

/-- 两个根被某个实际双模拟关联。无需递归解释图的节点。 -/
def Bisim (G : SG_graph.{u}) (H : SG_graph.{v}) : Prop :=
  ∃ R, BS_rel G H R ∧ R G.root H.root

theorem bs_refl (G : SG_graph.{u}) : G.Bisim G := by
  refine ⟨Eq, ?_, rfl⟩
  intro a b h
  subst b
  exact ⟨fun a' h => ⟨a', h, rfl⟩, fun a' h => ⟨a', h, rfl⟩⟩

theorem bs_symm {G : SG_graph.{u}} {H : SG_graph.{v}} (h : G.Bisim H) : H.Bisim G := by
  obtain ⟨R, hR, hr⟩ := h
  exact ⟨fun b a => R a b, fun b a h => ⟨(hR a b h).2, (hR a b h).1⟩, hr⟩

theorem bs_trans {G : SG_graph.{u}} {H : SG_graph.{v}} {K : SG_graph.{w}}
    (h : G.Bisim H) (k : H.Bisim K) : G.Bisim K := by
  obtain ⟨R, hR, hr⟩ := h
  obtain ⟨S, hS, hs⟩ := k
  refine ⟨fun a c => ∃ b, R a b ∧ S b c, ?_, ⟨H.root, hr, hs⟩⟩
  rintro a c ⟨b, hab, hbc⟩
  constructor
  · intro a' ha
    obtain ⟨b', hb, hr'⟩ := (hR a b hab).1 a' ha
    obtain ⟨c', hc, hs'⟩ := (hS b c hbc).1 b' hb
    exact ⟨c', hc, b', hr', hs'⟩
  · intro c' hc
    obtain ⟨b', hb, hs'⟩ := (hS b c hbc).2 c' hc
    obtain ⟨a', ha, hr'⟩ := (hR a b hab).2 b' hb
    exact ⟨a', ha, b', hr', hs'⟩

/-- 根等价恰好表示两侧根的成员能逐个匹配到等价的有根图。 -/
theorem bs_children {G : SG_graph.{u}} {H : SG_graph.{v}} : G.Bisim H ↔
    (∀ a, G.mem a G.root → ∃ b, H.mem b H.root ∧ (G.at_node a).Bisim (H.at_node b)) ∧
    (∀ b, H.mem b H.root → ∃ a, G.mem a G.root ∧ (G.at_node a).Bisim (H.at_node b)) := by
  constructor
  · rintro ⟨R, hR, hr⟩
    constructor
    · intro a ha
      obtain ⟨b, hb, hab⟩ := (hR _ _ hr).1 a ha
      exact ⟨b, hb, R, hR, hab⟩
    · intro b hb
      obtain ⟨a, ha, hab⟩ := (hR _ _ hr).2 b hb
      exact ⟨a, ha, R, hR, hab⟩
  · intro h
    let R a b := (G.at_node a).Bisim (H.at_node b) ∨ (a = G.root ∧ b = H.root)
    refine ⟨R, ?_, Or.inr ⟨rfl, rfl⟩⟩
    intro a b hab
    rcases hab with ⟨S, hS, hs⟩ | ⟨rfl, rfl⟩
    · constructor
      · intro a' ha
        obtain ⟨b', hb, hs'⟩ := (hS a b hs).1 a' ha
        exact ⟨b', hb, Or.inl ⟨S, hS, hs'⟩⟩
      · intro b' hb
        obtain ⟨a', ha, hs'⟩ := (hS a b hs).2 b' hb
        exact ⟨a', ha, Or.inl ⟨S, hS, hs'⟩⟩
    · exact ⟨fun a ha => let ⟨b, hb, hab⟩ := h.1 a ha; ⟨b, hb, Or.inl hab⟩,
        fun b hb => let ⟨a, ha, hab⟩ := h.2 b hb; ⟨a, ha, Or.inl hab⟩⟩

/-- 一个图表示另一个图的某个成员。 -/
def Raw_mem (G : SG_graph.{u}) (H : SG_graph.{v}) : Prop :=
  ∃ b, H.mem b H.root ∧ G.Bisim (H.at_node b)

theorem mem_forward {G G' : SG_graph.{u}} {H H' : SG_graph.{v}}
    (hG : G.Bisim G') (hH : H.Bisim H') (h : G.Raw_mem H) : G'.Raw_mem H' := by
  obtain ⟨b, hb, hGb⟩ := h
  obtain ⟨b', hb', hbb'⟩ := bs_children.mp hH |>.1 b hb
  exact ⟨b', hb', bs_trans (bs_symm hG) (bs_trans hGb hbb')⟩

theorem mem_congr {G G' : SG_graph.{u}} {H H' : SG_graph.{v}}
    (hG : G.Bisim G') (hH : H.Bisim H') : G.Raw_mem H ↔ G'.Raw_mem H' :=
  ⟨mem_forward hG hH, mem_forward (bs_symm hG) (bs_symm hH)⟩

/-- 精确保留每个节点的成员的映射给出双模拟。 -/
theorem bs_of_map {G : SG_graph.{u}} {H : SG_graph.{v}} (f : G.Domain → H.Domain)
    (hr : f G.root = H.root)
    (hf : ∀ a b, G.mem a b → H.mem (f a) (f b))
    (hb : ∀ b c, H.mem c (f b) → ∃ a, G.mem a b ∧ f a = c) : G.Bisim H := by
  refine ⟨fun a b => f a = b, ?_, hr⟩
  intro a b hab
  subst b
  exact ⟨fun a' h => ⟨f a', hf _ _ h, rfl⟩, hb a⟩

/-- 单个无边节点是空集的实际图呈现。 -/
def empty : SG_graph.{u} where
  Domain := PUnit
  nonempty := ⟨PUnit.unit⟩
  mem _ _ := False
  root := PUnit.unit

theorem empty_wf : WellFounded (empty.{u}).mem :=
  ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩

end SG_graph
end YesMetaZFC.Model.SmallGraph
