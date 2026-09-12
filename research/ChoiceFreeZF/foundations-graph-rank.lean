import YesMetaZFC.Model.SmallGraph.Sets

/-! # 条件集合值秩与固定域的对角界

传递闭包图在原 universe 内定义全局秩，并直接下降到双模拟商。
传递且成员传递不预设元层线性比较；对角界不冒充已验证的经典 Hartogs 数。
-/

namespace Zf_research
open YesMetaZFC.Model.SmallGraph
universe u

/-- 把原图边改为非空下降路径；节点域与良基性都不升阶。 -/
def Fg_graph (g : WF_graph.{u}) : WF_graph.{u} where
  Domain := g.Domain
  nonempty := g.nonempty
  root := g.root
  mem := Relation.TransGen g.mem
  wf := g.wf.transGen

/-- 对同一张图的全部节点同时构造集合值秩，不选择任何商代表。 -/
def fg_rank (g : WF_graph.{u}) (a : g.Domain) : SG_set.{u} :=
  SG_set.mk ((Fg_graph g).at_node a)

theorem fg_mem (g : WF_graph.{u}) (a : g.Domain) (z : SG_set.{u}) :
    z ∈ fg_rank g a ↔ ∃ b, Relation.TransGen g.mem b a ∧ z = fg_rank g b :=
  SG_set.mem_mk ((Fg_graph g).at_node a) z

def Fg_transitive (x : SG_set.{u}) : Prop := ∀ z, z ∈ x → ∀ w, w ∈ z → w ∈ x

theorem fg_transitive (g : WF_graph.{u}) (a : g.Domain) : Fg_transitive (fg_rank g a) := by
  intro z hz w hw
  rcases (fg_mem g a z).mp hz with ⟨b, hb, rfl⟩
  rcases (fg_mem g b w).mp hw with ⟨c, hc, rfl⟩
  exact (fg_mem g a _).mpr ⟨c, hc.trans hb, rfl⟩

/-- 每个值都是传递集，且它的每个成员仍为传递集；此处不宣称跨所有秩线性比较。 -/
theorem fg_ordinal (g : WF_graph.{u}) (a : g.Domain) :
    Fg_transitive (fg_rank g a) ∧ ∀ z, z ∈ fg_rank g a → Fg_transitive z := by
  refine ⟨fg_transitive g a, fun z hz => ?_⟩
  rcases (fg_mem g a z).mp hz with ⟨b, _, rfl⟩
  exact fg_transitive g b

/-- 每条有限下降路径逐步匹配；所有见证始终在命题内组合。 -/
theorem fg_path {g : SG_graph.{u}} {h : SG_graph.{v}}
    {r : g.Domain → h.Domain → Prop} (hr : SG_graph.BS_rel g h r)
    {a b : g.Domain} (p : Relation.TransGen g.mem a b) :
    ∀ c, r b c → ∃ d, Relation.TransGen h.mem d c ∧ r a d := by
  induction p with
  | single p =>
    intro c hc
    rcases (hr _ _ hc).1 _ p with ⟨d, hd, he⟩
    exact ⟨d, Relation.TransGen.single hd, he⟩
  | tail _ p ih =>
    intro c hc
    rcases (hr _ _ hc).1 _ p with ⟨d, hd, he⟩
    rcases ih d he with ⟨e, hp, he⟩
    exact ⟨e, Relation.TransGen.tail hp hd, he⟩

theorem fg_bisim {g : WF_graph.{u}} {h : WF_graph.{v}}
    (q : g.toSG_graph.Bisim h.toSG_graph) :
    (Fg_graph g).toSG_graph.Bisim (Fg_graph h).toSG_graph := by
  rcases q with ⟨r, hr, hroot⟩
  refine ⟨r, fun a b hab => ⟨?_, ?_⟩, hroot⟩
  · exact fun c hc => fg_path hr hc b hab
  · exact fun c hc => fg_path (fun b a h => ⟨(hr a b h).2, (hr a b h).1⟩) hc a hab

/-- 任意小图商值的秩算子；商消去直接使用路径双模拟不变性。 -/
def fg_set_rank : SG_set.{u} → SG_set.{u} :=
  Quotient.lift (fun g => SG_set.mk (Fg_graph g))
    (fun _ _ h => SG_set.mk_eq.mpr (fg_bisim h))

theorem fg_set_ordinal (x : SG_set.{u}) :
    Fg_transitive (fg_set_rank x) ∧ ∀ z, z ∈ fg_set_rank x → Fg_transitive z := by
  induction x using Quotient.inductionOn with
  | _ g => exact fg_ordinal g g.root

/-- 原成员严格降低此集合值秩；不需要选出整族图的代表。 -/
theorem fg_set_lt {x y : SG_set.{u}} (h : x ∈ y) : fg_set_rank x ∈ fg_set_rank y := by
  induction y using Quotient.inductionOn with
  | _ g =>
    rcases (SG_set.mem_mk g x).mp h with ⟨a, ha, rfl⟩
    exact (fg_mem g g.root _).mpr ⟨a, Relation.TransGen.single ha, rfl⟩

/-- 纸面递归方程：rank(x) 是所有 rank(y) 与其成员的并，y 遍历 x。 -/
theorem fg_set_mem (x z : SG_set.{u}) : z ∈ fg_set_rank x ↔
    ∃ y, y ∈ x ∧ (z = fg_set_rank y ∨ z ∈ fg_set_rank y) := by
  induction x using Quotient.inductionOn with
  | _ g =>
    constructor
    · intro hz
      rcases (fg_mem g g.root z).mp hz with ⟨a, ha, rfl⟩
      cases ha with
      | single h =>
        exact ⟨SG_set.mk (g.at_node a), (SG_set.mem_mk g _).mpr ⟨a, h, rfl⟩,
          Or.inl rfl⟩
      | tail p h =>
        exact ⟨SG_set.mk (g.at_node _), (SG_set.mem_mk g _).mpr ⟨_, h, rfl⟩,
          Or.inr ((fg_mem g _ _).mpr ⟨a, p, rfl⟩)⟩
    · rintro ⟨y, hy, hz⟩
      rcases (SG_set.mem_mk g y).mp hy with ⟨a, ha, rfl⟩
      rcases hz with rfl | hz
      · exact (fg_mem g g.root _).mpr ⟨a, Relation.TransGen.single ha, rfl⟩
      · rcases (fg_mem g a z).mp hz with ⟨b, hb, rfl⟩
        exact (fg_mem g g.root _).mpr ⟨b, Relation.TransGen.tail hb ha, rfl⟩

/-- 条件序数已经是秩的不动点；无需在条件序数之间作线性比较。 -/
theorem fg_fixed (x : SG_set.{u}) (hx : Fg_transitive x)
    (hxx : ∀ y, y ∈ x → Fg_transitive y) : fg_set_rank x = x := by
  induction x using SG_set.mem_wf.induction with
  | h x ih =>
    have he (y : SG_set.{u}) (hy : y ∈ x) : fg_set_rank y = y :=
      ih y hy (hxx y hy) (fun z hz => hxx z (hx y hy z hz))
    apply SG_set.ext
    intro z
    constructor
    · intro hz
      rcases (fg_set_mem x z).mp hz with ⟨y, hy, hz⟩
      rw [he y hy] at hz
      rcases hz with rfl | hz
      · exact hy
      · exact hx y hy z hz
    · intro hz
      exact (fg_set_mem x z).mpr ⟨z, hz, Or.inl (he z hz).symm⟩

theorem fg_idempotent (x : SG_set.{u}) : fg_set_rank (fg_set_rank x) = fg_set_rank x :=
  fg_fixed _ (fg_set_ordinal x).1 (fg_set_ordinal x).2

/-- 固定小域上的全部良基有根关系；关系、证书和根的总类型仍在原层。 -/
structure Fg_code (a : Type u) where
  rel : a → a → Prop
  wf : WellFounded rel
  root : a

def Fg_code.graph {a : Type u} (c : Fg_code a) : WF_graph.{u} where
  Domain := a
  nonempty := ⟨c.root⟩
  root := c.root
  mem := c.rel
  wf := c.wf

/-- 直接并合所有固定域图的秩。不是选择一组代表，也没有先假设任何上界。 -/
def fg_bound (a : Type u) : SG_set.{u} :=
  SG_set.mk (WF_graph.root_sum (fun c : Fg_code a => Fg_graph c.graph))

theorem fg_bound_mem {a : Type u} (c : Fg_code a) :
    fg_set_rank (SG_set.mk c.graph) ∈ fg_bound a :=
  (SG_set.mem_sum _ _).mpr ⟨c, rfl⟩

theorem fg_bound_ordinal (a : Type u) :
    Fg_transitive (fg_bound a) ∧ ∀ z, z ∈ fg_bound a → Fg_transitive z := by
  constructor
  · intro z hz w hw
    rcases (SG_set.mem_sum _ _).mp hz with ⟨c, rfl⟩
    rcases (fg_mem c.graph c.root w).mp hw with ⟨b, _, e⟩
    exact (SG_set.mem_sum _ _).mpr ⟨{ c with root := b }, e⟩
  · intro z hz
    rcases (SG_set.mem_sum _ _).mp hz with ⟨c, rfl⟩
    exact fg_transitive c.graph c.root

/-- 对角对象本身不是任何固定域图的秩；不宣称经典序数线性上界。 -/
theorem fg_bound_not_rank {a : Type u} (c : Fg_code a) :
    fg_bound a ≠ fg_set_rank (SG_set.mk c.graph) := by
  intro h
  have hm : fg_bound a ∈ fg_bound a := h ▸ fg_bound_mem c
  have hn := SG_set.mem_wf.induction (C := fun x : SG_set.{u} => ¬ x ∈ x)
    (fg_bound a) (fun x ih hx => ih x hx hx)
  exact hn hm

#print axioms Fg_graph
#print axioms fg_rank
#print axioms fg_mem
#print axioms fg_ordinal
#print axioms fg_set_rank
#print axioms fg_set_ordinal
#print axioms fg_set_lt
#print axioms fg_set_mem
#print axioms fg_fixed
#print axioms fg_idempotent
#print axioms fg_bound
#print axioms fg_bound_mem
#print axioms fg_bound_ordinal
#print axioms fg_bound_not_rank

end Zf_research
