import YesMetaZFC.SetTheory.Ord.CanonicalPairing

/-! # 良序端延拓中的坍塌值不变

初段的旧坍塌图已经满足大关系上的同一方程，故不必重新递归。
典范序数方块正是这一通用传输定理的实际实例。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Structure.IsWellOrderCollapseValue.end_l {R S X Y p c}
    (h : M.IsWellOrderCollapseValue I R X p c) (hp : M.mem p X)
    (hx : M.IsRelationInitialSegment I X S Y)
    (hr : ∀ a b, M.mem a X → M.mem b X → (M.PairMember I a b R ↔ M.PairMember I a b S)) :
    M.IsWellOrderCollapseValue I S Y p c := by
  obtain ⟨P, F, hP, hF, hc⟩ := h
  have hPX : M.MemberSubset P X := fun x hx => ((hP x).mp hx).1
  have pred : M.IsPredecessorSet I P S Y p := by
    intro x
    exact (hP x).trans ⟨fun ⟨h, hxp⟩ => ⟨hx.1 x h, (hr x p h hp).mp hxp⟩,
      fun ⟨h, hxp⟩ => ⟨hx.2 p hp x h hxp, (hr x p (hx.2 p hp x h hxp) hp).mpr hxp⟩⟩
  refine ⟨P, F, pred, ⟨hF.1, hF.2.1, ⟨fun x h => hx.1 x (hPX x h), ?_⟩, ?_⟩, hc⟩
  · intro x hxp y hy hyx
    have hyX := hx.2 x (hPX x hxp) y hy hyx
    exact hF.2.2.1.2 x hxp y hyX ((hr y x hyX (hPX x hxp)).mpr hyx)
  · intro x hxp y hxy z
    exact (hF.2.2.2 x hxp y hxy z).trans (exists_congr fun a => and_congr_right fun ha =>
      and_congr (hr a x (hPX a ha) (hPX x hxp)) Iff.rfl)

/-- 小序数方块在任意大方块中都是同一典范序的初段。 -/
theorem oc_square_end_l {a b X Y R S} (ha : M.IsOrdinal a)
    (h : M.IsCanonicalOrdinalPairOrder I R X a) (g : M.IsCanonicalOrdinalPairOrder I S Y b)
    (hab : M.MemberSubset a b) : M.IsRelationInitialSegment I X S Y ∧
      ∀ p q, M.mem p X → M.mem q X → (M.PairMember I p q R ↔ M.PairMember I p q S) := by
  have sub : M.MemberSubset X Y := by
    intro p hp
    obtain ⟨x, hx, y, hy, hc⟩ := (h.1 p).mp hp
    exact (g.1 p).mpr ⟨x, hab x hx, y, hab y hy, hc⟩
  have agree p q (hp : M.mem p X) (hq : M.mem q X) :
      M.PairMember I p q R ↔ M.PairMember I p q S :=
    ⟨fun hr => (g.2.2 p q).mpr ⟨sub p hp, sub q hq, ((h.2.2 p q).mp hr).2.2⟩,
      fun hr => (h.2.2 p q).mpr ⟨hp, hq, ((g.2.2 p q).mp hr).2.2⟩⟩
  refine ⟨⟨sub, ?_⟩, agree⟩
  intro p hp q _ hqp
  obtain ⟨x, hx, y, hy, hp⟩ := (h.1 p).mp hp
  obtain ⟨_, _, u, v, x', y', m, n, hq, hp', hm, hn, lt⟩ := (g.2.2 q p).mp hqp
  obtain ⟨rfl, rfl⟩ := I.injective hp hp'
  have hnA := hn.mem hx hy
  have hmA : M.mem m a := lt.elim (ha.transitive n hnA m) (fun h => h.1.symm ▸ hnA)
  have bound z (hz : M.mem z m ∨ z = m) : M.mem z a :=
    hz.elim (ha.transitive m hmA z) (fun he => he.symm ▸ hmA)
  exact (h.1 q).mpr ⟨u, bound u hm.left_mem_or_eq, v, bound v hm.right_mem_or_eq, hq⟩

end YesMetaZFC.SetTheory
