import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.Model.SetTheory.Internal.FiniteSetCode

/-! # 任意排列后的树与函数图恢复

序数不能是标签对，也不能包含非空函数节点；含空根的树不能是标签对。
这三个排除事实固定两个端点，中间只恢复图的包含与单点延长。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem KPair_d.empty_not_mem_l {e p a b : M.Domain} (he : ∀ x, ¬ M.mem x e)
    (h : KPair_d M p a b) : ¬ M.mem e p := by
  obtain ⟨s, t, hs, ht, hp⟩ := h
  intro hep
  rcases (hp e).mp hep with eq | eq
  · exact he a (eq.symm ▸ (hs a).mpr rfl)
  · exact he a (eq.symm ▸ (ht a).mpr (Or.inl rfl))

variable (hE : Extensional M) (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b)
  (hirr : ∀ x, ¬ M.mem x x)
local notation "I" => kpair_interpretation_l M hE hP
include hirr

theorem Tg_graph_d.not_ordinal_l {k g i : M.Domain} (h : Tg_graph_d I k g) (hi : M.mem i k) :
    ¬ M.IsOrdinal g := by
  obtain ⟨y, p, hp, hpg⟩ := (h.2 i).mp hi
  exact fun hg => hp.not_transitive_l M hirr (hg.mem hpg).transitive

theorem Tg_node_d.not_ordinal_l {k S s t g i : M.Domain} (h : Tg_node_d I k S s t g) (hi : M.mem i k) :
    ¬ M.IsOrdinal S := by
  obtain ⟨q, hq, graph, _⟩ := h.2.2.2
  exact fun hS => graph.not_ordinal_l hE hP hirr hi (hS.mem hq)

/-- 只使用旧对象确实出现；不假设任何标签在新元组中的位置。 -/
theorem tg_node_recover_l {e k l n X r T S s t g a α β : M.Domain}
    (he : ∀ x, ¬ M.mem x e) (hk : M.mem e k) (hn : M.SuccessorOf n l)
    (tuple : M.IsSetFunctionFromTo I r n X) (root : Rd_entry_d e T r) (last : Rd_entry_d l β r)
    (set : Sg_set_d I e l r g) (node : Tg_node_d I k T s t g)
    (hα : M.IsOrdinal α) (hS : M.mem e S) (ne : S ≠ α) (old : M.IsSetRelation I a)
    (seenS : ∃ i, M.mem i n ∧ Rd_entry_d i S r) (seenα : ∃ i, M.mem i n ∧ Rd_entry_d i α r)
    (seen : ∀ p, M.mem p a → ∃ i, M.mem i n ∧ Rd_entry_d i p r) :
    T = S ∧ β = α ∧ M.MemberSubset a g := by
  have slot i x (hi : M.mem i n) (hx : Rd_entry_d i x r) : x = T ∨ M.mem x g ∨ x = β := by
    rcases (hn i).mp hi with hi | eq
    · by_cases ie : i = e
      · exact Or.inl (tuple.1.2 e x T (ie ▸ hx) root)
      · exact Or.inr (Or.inl ((set x).mpr ⟨i, hi, ie, hx⟩))
    · exact Or.inr (Or.inr (tuple.1.2 l x β (hE.eq_of_same_members i l eq ▸ hx) last))
  have endα : β = α := by
    obtain ⟨i, hi, hx⟩ := seenα
    rcases slot i α hi hx with eq | hg | eq
    · exact (node.not_ordinal_l hE hP hirr hk (eq ▸ hα)).elim
    · obtain ⟨x, y, hp⟩ := node.2.2.1.1.1 α hg
      exact (hp.not_transitive_l M hirr hα.transitive).elim
    · exact eq.symm
  have startS : T = S := by
    obtain ⟨i, hi, hx⟩ := seenS
    rcases slot i S hi hx with eq | hg | eq
    · exact eq.symm
    · obtain ⟨x, y, hp⟩ := node.2.2.1.1.1 S hg
      exact (KPair_d.empty_not_mem_l he hp hS).elim
    · exact (ne (eq.trans endα)).elim
  refine ⟨startS, endα, fun p hp => ?_⟩
  obtain ⟨i, hi, hx⟩ := seen p hp
  obtain ⟨x, y, pair⟩ := old p hp
  rcases slot i p hi hx with eq | hg | eq
  · exact (KPair_d.empty_not_mem_l he pair ((eq.trans startS).symm ▸ hS)).elim
  · exact hg
  · exact (pair.not_transitive_l M hirr ((eq.trans endα).symm ▸ hα.transitive)).elim

omit hirr

/-- 同域函数性把图包含加强为恰好新增末项；不需要基数计数或标准长度。 -/
theorem tg_graph_extend_l {j k a g : M.Domain} (hs : M.SuccessorOf k j)
    (ha : Tg_graph_d I j a) (hg : Tg_graph_d I k g) (sub : M.MemberSubset a g) :
    ∃ z, Rd_entry_d j z g ∧ ∀ p, M.mem p g ↔ M.mem p a ∨ KPair_d M p j z := by
  obtain ⟨z, hz⟩ := (hg.2 j).mp hs.predecessor_mem
  refine ⟨z, hz, fun p => ⟨?_, ?_⟩⟩
  · intro hp
    obtain ⟨i, x, pair⟩ := hg.1.1 p hp
    have hx : Rd_entry_d i x g := ⟨p, pair, hp⟩
    rcases (hs i).mp ((hg.2 i).mpr ⟨x, hx⟩) with hi | eq
    · obtain ⟨y, q, cq, hq⟩ := (ha.2 i).mp hi
      have xy := hg.1.2 i x y hx ⟨q, cq, sub q hq⟩
      exact Or.inl (kpair_unique_l M hE (xy ▸ pair) cq ▸ hq)
    · have ij := hE.eq_of_same_members i j eq
      have xz := hg.1.2 j x z (ij ▸ hx) hz
      exact Or.inr (ij ▸ xz ▸ pair)
  · intro hp
    rcases hp with hp | pair
    · exact sub p hp
    · obtain ⟨q, cq, hq⟩ := hz
      exact (kpair_unique_l M hE pair cq).symm ▸ hq

/-- 原节点中的标签图仍留在包含树的传递配对闭包中。 -/
theorem Tg_node_d.labels_mem_l {k S s t g W : M.Domain} (h : Tg_node_d I k S s t g)
    (hW : M.TransitiveSet W) (hS : M.mem S W)
    (pair : ∀ a b, M.mem a W → M.mem b W → ∃ p, M.mem p W ∧ Pair_d M p a b) : M.MemberSubset g W := by
  obtain ⟨q, hq, _, join⟩ := h.2.2.2
  have hqW := hW S hS q hq
  intro p hp
  obtain ⟨i, z, code⟩ := h.2.2.1.1.1 p hp
  obtain ⟨x, y, z', v, a, _, _, hz, cv, ca, ia⟩ := join i ((h.2.2.1.2 i).mpr ⟨z, p, code, hp⟩)
  have eq := h.2.2.1.1.2 i z' z hz ⟨p, code, hp⟩
  subst z'
  have iaW := rd_entry_transitive_l hW hqW ia
  have zv := (cv.mem_l M hW (ca.mem_l M hW iaW.2).2).2
  obtain ⟨a, ha, aa⟩ := pair i i iaW.1 iaW.1
  obtain ⟨b, hb, ab⟩ := pair i z iaW.1 zv
  obtain ⟨c, hc, ac⟩ := pair a b ha hb
  have encoded : KPair_d M c i z := ⟨a, b, fun x => (aa x).trans ⟨fun h => h.elim id id, Or.inl⟩, ab, ac⟩
  exact (kpair_unique_l M hE code encoded).symm ▸ hc

end YesMetaZFC.SetTheory.Internal
