import YesMetaZFC.Model.Forcing.Internal.Names.Graph

/-! # 地模型对象的无权小图呈现

直接呈现地模型的成员关系，与名称及滤子无关。外部良基性只在这里消费；
传递包络与小呈现确定节点域，不把整个模型载体提升到小图节点层。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SmallGraph
universe u v
variable (M : SetTheory.Structure.{u})

def Ground_rep_d (x : M.Domain) (G : WF_graph.{v}) : Prop :=
  ∃ c : G.Domain → M.Domain, c G.root = x ∧
    (∀ a d, G.mem a d → M.mem (c a) (c d)) ∧
    (∀ d y, M.mem y (c d) → ∃ a, G.mem a d ∧ c a = y)

def ground_node_l {I : Type v} (x : M.Domain) (f : I → M.Domain) : Option I → M.Domain
  | none => x
  | some i => f i

def ground_graph_l (hM : _root_.WellFounded M.mem) {I : Type v}
    (x : M.Domain) (f : I → M.Domain) : WF_graph.{v} where
  Domain := Option I
  nonempty := ⟨none⟩
  root := none
  mem a d := M.mem (ground_node_l M x f a) (ground_node_l M x f d)
  wf := InvImage.wf (ground_node_l M x f) hM

/-- 一个内部传递包络足以产生该对象的全成员图，无需选择成员的递归呈现。 -/
theorem ground_decode_l (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M)
    {x S} (hx : M.mem x S) (hS : M.TransitiveSet S) :
    ∃ G : WF_graph.{v}, Ground_rep_d M x G := by
  obtain ⟨I, f, hf⟩ := hL S
  have hc (a : Option I) : M.mem (ground_node_l M x f a) S := by
    cases a with
    | none => exact hx
    | some i => exact (hf _).mpr ⟨i, rfl⟩
  refine ⟨ground_graph_l M hM x f, ground_node_l M x f, rfl, fun _ _ h => h, ?_⟩
  intro d y hy
  obtain ⟨i, rfl⟩ := (hf y).mp (hS _ (hc d) _ hy)
  exact ⟨some i, hy, rfl⟩

/-- 任意两幅忠实呈现同一地模型对象的小图，都给出同一个商集合。 -/
theorem ground_rep_eq_l {x} {G H : WF_graph.{v}}
    (h : Ground_rep_d M x G) (k : Ground_rep_d M x H) : SG_set.mk G = SG_set.mk H := by
  obtain ⟨c, hc, hf, hb⟩ := h
  obtain ⟨d, hd, kf, kb⟩ := k
  apply SG_set.mk_eq.mpr
  refine ⟨fun a b => c a = d b, ?_, hc.trans hd.symm⟩
  intro a b hab
  constructor
  · intro a' ha
    obtain ⟨b', hb', he⟩ := kb b (c a') (hab ▸ hf a' a ha)
    exact ⟨b', hb', he.symm⟩
  · intro b' hb'
    obtain ⟨a', ha, he⟩ := hb a (d b') (hab.symm ▸ kf b' b hb')
    exact ⟨a', ha, he⟩

def Ground_d (x : M.Domain) (y : SG_set.{v}) : Prop :=
  ∃ G : WF_graph.{v}, Ground_rep_d M x G ∧ SG_set.mk G = y

end YesMetaZFC.Model.Forcing.Internal
