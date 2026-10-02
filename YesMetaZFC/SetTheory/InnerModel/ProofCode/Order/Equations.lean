import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.Construction

/-! # 比较关系的四条构造方程 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project Internal
universe u
variable {M : Structure.{u}}

theorem po_num_natural_l (hE : Extensional M) {k x} (hx : Num_d (M := M) k x) : KP.N0_d x := by
  induction k generalizing x with
  | zero => exact KP.n0_empty_l hx
  | succ k ih => obtain ⟨y, hy, hs⟩ := hx; exact KP.n0_succ_l hE (ih hy) hs

theorem po_num_lt_l (hKP : M.Models KP) {i j a b} (ha : Num_d (M := M) i a) (hb : Num_d j b) :
    M.mem a b ↔ i < j := by
  have trans {k x} (hx : Num_d (M := M) k x) : M.TransitiveSet x := (po_num_natural_l hKP.1 hx).1
  refine ⟨fun h => ?_, num_lt_l hKP.1 ha hb⟩
  rcases Nat.lt_trichotomy i j with hij | he | hji
  · exact hij
  · subst j
    exact (KP.mem_irrefl_d hKP b (num_unique_l hKP.1 ha hb ▸ h)).elim
  · exact (KP.mem_irrefl_d hKP a (trans ha b (num_lt_l hKP.1 hb ha hji) a h)).elim

theorem po_leaf_mono_l {T U c a : M.Domain} (ht : M.MemberSubset T U) : Pc_leaf_d T c a → Pc_leaf_d U c a :=
  fun ⟨e, he, h⟩ => ⟨e, ht e he, h⟩

theorem po_node_mono_l {T U c a b d : M.Domain} {k} (ht : M.MemberSubset T U) :
    Pc_node_d T k c a b d → Pc_node_d U k c a b d :=
  fun ⟨t, htt, v, hv, h⟩ => ⟨t, ht t htt, v, ht v hv, h⟩

private theorem tag_l (hKP : M.Models KP) {i j : Nat} {c d t s a b t' s' x y : M.Domain}
    (ht : Num_d i t) (hs : Num_d j s) (hc : KPair_d M c t a) (hd : KPair_d M d s b)
    (hx : KPair_d M c t' x) (hy : KPair_d M d s' y) (h : M.mem t' s') : i < j := by
  obtain ⟨rfl, _⟩ := kpair_injective_l M hx hc
  obtain ⟨rfl, _⟩ := kpair_injective_l M hy hd
  exact (po_num_lt_l hKP ht hs).mp h

theorem po_leaf_iff_l (hM : M.Models KPi) {A B c d a b : M.Domain}
    (hc : Pc_leaf_d A c a) (hd : Pc_leaf_d B d b) : Po_lt_d c d ↔ M.mem a b := by
  let hKP := (KPi.models_iff_l.mp hM).1
  constructor
  · intro h
    obtain ⟨T, h⟩ := po_unfold_l h
    rcases h with ⟨x, _, y, _, hx, hy, h⟩ | ⟨t, _, s, _, x, _, y, _, hx, hy, h⟩ |
      ⟨k, x, _, y, _, z, _, p, _, q, _, r, _, hx, _, _⟩
    · exact (pc_leaf_inj_l hx hc) ▸ (pc_leaf_inj_l hy hd) ▸ h
    · obtain ⟨e, _, he, hec⟩ := hc
      obtain ⟨f, _, hf, hfd⟩ := hd
      exact (Nat.lt_irrefl 0 (tag_l hKP he hf hec hfd hx hy h)).elim
    · exact (pc_leaf_node_false_l hKP hc hx).elim
  · intro h
    obtain ⟨T, ht, hT⟩ := pc_cover_l hM [A, B, a, b]
    exact po_close_l hM (Or.inl ⟨a, hT a (by simp), b, hT b (by simp),
      po_leaf_mono_l (ht A (hT A (by simp))) hc, po_leaf_mono_l (ht B (hT B (by simp))) hd, h⟩)

theorem po_leaf_node_l (hM : M.Models KPi) {A B c d a x y z : M.Domain} {k}
    (hc : Pc_leaf_d A c a) (hd : Pc_node_d B k d x y z) : Po_lt_d c d := by
  obtain ⟨e, he, hn, hp⟩ := hc
  obtain ⟨t, htt, v, hv, ho, _, hq⟩ := hd
  obtain ⟨T, ht, hT⟩ := pc_cover_l hM [A, B, a]
  exact po_close_l hM (Or.inr (Or.inl ⟨e, ht A (hT A (by simp)) e he,
    t, ht B (hT B (by simp)) t htt, a, hT a (by simp), v, ht B (hT B (by simp)) v hv,
      hp, hq, num_lt_l (KPi.models_iff_l.mp hM).1.1 hn ho (pc_tag_pos_l k)⟩))

theorem po_node_leaf_false_l (hKP : M.Models KP) {A B c d a x y z : M.Domain} {k}
    (hc : Pc_node_d A k c x y z) (hd : Pc_leaf_d B d a) : ¬ Po_lt_d c d := by
  intro h
  obtain ⟨T, h⟩ := po_unfold_l h
  rcases h with ⟨p, _, q, _, hp, _, _⟩ | ⟨t, _, s, _, p, _, q, _, hp, hq, h⟩ |
    ⟨l, p, _, q, _, r, _, u, _, v, _, w, _, _, hq, _⟩
  · exact pc_leaf_node_false_l hKP hp hc
  · obtain ⟨t', _, v, _, ht, _, he⟩ := hc
    obtain ⟨s', _, hs, hf⟩ := hd
    exact Nat.not_lt_zero _ (tag_l hKP ht hs he hf hp hq h)
  · exact pc_leaf_node_false_l hKP hd hq

theorem po_node_iff_l (hM : M.Models KPi) {A B c d a b e x y z : M.Domain} {k l}
    (hc : Pc_node_d A k c a b e) (hd : Pc_node_d B l d x y z) :
    Po_lt_d c d ↔ pc_tag_l k < pc_tag_l l ∨ (k = l ∧ Po_lex_d Po_lt_d a b e x y z) := by
  let hKP := (KPi.models_iff_l.mp hM).1
  constructor
  · intro h
    obtain ⟨T, h⟩ := po_unfold_l h
    rcases h with ⟨p, _, q, _, hp, _, _⟩ | ⟨t, _, s, _, p, _, q, _, hp, hq, h⟩ |
      ⟨j, a', _, b', _, e', _, x', _, y', _, z', _, hp, hq, h⟩
    · exact (pc_leaf_node_false_l hKP hp hc).elim
    · obtain ⟨t', _, v, _, ht, _, he⟩ := hc
      obtain ⟨s', _, w, _, hs, _, hf⟩ := hd
      exact Or.inl (tag_l hKP ht hs he hf hp hq h)
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := pc_node_inj_l hKP hp hc
      obtain ⟨rfl, rfl, rfl, rfl⟩ := pc_node_inj_l hKP hq hd
      exact Or.inr ⟨rfl, h⟩
  · rintro (h | ⟨rfl, h⟩)
    · obtain ⟨t, ht, v, hv, ho, _, hp⟩ := hc
      obtain ⟨s, hs, w, hw, hn, _, hq⟩ := hd
      obtain ⟨T, hT, hU⟩ := pc_cover_l hM [A, B]
      have ai := hT A (hU A (by simp))
      have bi := hT B (hU B (by simp))
      exact po_close_l hM (Or.inr (Or.inl ⟨t, ai t ht, s, bi s hs, v, ai v hv, w, bi w hw,
        hp, hq, num_lt_l hKP.1 ho hn h⟩))
    · obtain ⟨T, ht, hT⟩ := pc_cover_l hM [A, B, a, b, e, x, y, z]
      exact po_close_l hM (Or.inr (Or.inr ⟨k, a, hT a (by simp), b, hT b (by simp), e, hT e (by simp),
        x, hT x (by simp), y, hT y (by simp), z, hT z (by simp),
        po_node_mono_l (ht A (hT A (by simp))) hc, po_node_mono_l (ht B (hT B (by simp))) hd, h⟩))

end YesMetaZFC.SetTheory.InnerModel
