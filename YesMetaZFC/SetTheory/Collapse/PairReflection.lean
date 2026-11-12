import YesMetaZFC.SetTheory.Collapse.Mostowski

/-! # 非传递源的有序对坐标回收

满坍塌可合并代表元，但不能把单元素集合变成双元素集合。因此当像中的
Kuratowski 对具有不同坐标时，原对的两个坐标都必须在源中，并逐项映到
指定坐标。这里只使用实际满成员映射及目标传递性，不要求源配对闭包。
-/
namespace YesMetaZFC.SetTheory
open InnerModel
universe u
variable {M : Structure.{u}} {Q B F : M.Domain} (h : Mc_map_d Q B F) (ht : M.TransitiveSet B)

namespace Mc_map_d
include h ht

/-- 像中一个成员的原像必须是原二元集合中的某个元素。 -/
theorem pair_preimage_l {p q a b z : M.Domain} (hp : Pair_d M p a b)
    (edge : Rd_entry_d p q F) (hz : M.mem z q) : Rd_entry_d a z F ∨ Rd_entry_d b z F := by
  obtain ⟨u,hu⟩ := h.onto z (ht q (h.function.bound_l edge).2 z hz)
  exact ((hp u).mp ((h.member u p z q hu edge).mpr hz)).elim
    (fun eq => Or.inl (eq ▸ hu)) (fun eq => Or.inr (eq ▸ hu))

theorem singleton_preimage_l {p q a z : M.Domain} (hp : M.IsSingletonOf p a)
    (edge : Rd_entry_d p q F) (hz : M.mem z q) : Rd_entry_d a z F :=
  (h.pair_preimage_l ht (fun u => (hp u).trans ⟨Or.inl,fun e => e.elim id id⟩) edge hz).elim id id

/-- 异坐标的像不能由缺失坐标或倒置的单、双元素集合产生。 -/
theorem kpair_preimage_l {p q a b x y : M.Domain} (hp : KPair_d M p a b)
    (hq : KPair_d M q x y) (edge : Rd_entry_d p q F) (ne : x ≠ y) :
    M.mem a Q ∧ M.mem b Q ∧ Rd_entry_d a x F ∧ Rd_entry_d b y F := by
  obtain ⟨s,t,single,pair,outer⟩ := hp
  obtain ⟨v,w,single',pair',outer'⟩ := hq
  have unique {a x y} (hx : Rd_entry_d a x F) (hy : Rd_entry_d a y F) : x = y :=
    h.function.2.2 a (h.function.bound_l hx).1 x (h.function.bound_l hx).2
      y (h.function.bound_l hy).2 hx hy
  have vw : v ≠ w := by
    intro eq
    exact ne ((single' y).mp (eq.symm ▸ (pair' y).mpr (Or.inr rfl))).symm
  have no : ¬ Rd_entry_d s w F := by
    intro hs
    exact ne (unique (h.singleton_preimage_l ht single hs ((pair' x).mpr (Or.inl rfl)))
      (h.singleton_preimage_l ht single hs ((pair' y).mpr (Or.inr rfl))))
  have tw : Rd_entry_d t w F :=
    (h.pair_preimage_l ht outer edge ((outer' w).mpr (Or.inr rfl))).elim (fun hs => (no hs).elim) id
  have sv : Rd_entry_d s v F :=
    (h.pair_preimage_l ht outer edge ((outer' v).mpr (Or.inl rfl))).elim id (fun hv => (vw (unique hv tw)).elim)
  have ax := h.singleton_preimage_l ht single sv ((single' x).mpr rfl)
  have by' : Rd_entry_d b y F :=
    (h.pair_preimage_l ht pair tw ((pair' y).mpr (Or.inr rfl))).elim (fun ay => (ne (unique ax ay)).elim) id
  exact ⟨(h.function.bound_l ax).1,(h.function.bound_l by').1,ax,by'⟩

/-- 原对本来就在对角线上时，非空对角像也唯一回收原坐标。 -/
theorem diagonal_preimage_l (hE : Extensional M) {p q a x : M.Domain} (hp : KPair_d M p a a)
    (hq : KPair_d M q x x) (edge : Rd_entry_d p q F) : Rd_entry_d a x F := by
  obtain ⟨s,t,single,pair,outer⟩ := hp
  have eq : s = t := hE.eq_of_same_members s t fun z =>
    (single z).trans ((pair z).trans ⟨fun e => e.elim id id,Or.inl⟩).symm
  subst t
  obtain ⟨v,_,single',_,outer'⟩ := hq
  have sv := (h.pair_preimage_l ht outer edge ((outer' v).mpr (Or.inl rfl))).elim id id
  exact h.singleton_preimage_l ht single sv ((single' x).mpr rfl)

end Mc_map_d
end YesMetaZFC.SetTheory
