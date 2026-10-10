import YesMetaZFC.SetTheory.InnerModel.Separation.Family
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Member

/-! # 全部 rud 输出成员的共同传递界

四次无序对扩张容纳有序对和三元组；再加入输入关系的全部纤维。
整个界由有限基实际构造，属于原 rud 闭包。
-/

namespace YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : Structure.{u}}

theorem rt_pair_to_opair_l {U V W : M.Domain}
    (h : ∀ a b p, M.mem a U → M.mem b U → Pair_d M p a b → M.mem p V)
    (g : ∀ a b p, M.mem a V → M.mem b V → Pair_d M p a b → M.mem p W)
    {a b p} (ha : M.mem a U) (hb : M.mem b U) (hp : KPair_d M p a b) : M.mem p W := by
  obtain ⟨s, t, hs, ht, hp⟩ := hp
  exact g s t p (h a a s ha ha (fun z => (hs z).trans ⟨Or.inl, fun h => h.elim id id⟩))
    (h a b t ha hb ht) hp

theorem rd_family_bound_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C)
    (hU : M.mem U C) (hu : M.TransitiveSet U) :
    ∃ T, M.mem T C ∧ M.TransitiveSet T ∧ M.MemberSubset U T ∧
      ∀ k a b c t, M.mem a U → M.mem b U → M.mem c U → Rd_mem_d k a b c t → M.mem t T := by
  obtain ⟨V₁, h₁C, h₁, u₁, p₁⟩ := rt_pair_hull_l hKP hC hU hu
  obtain ⟨V₂, h₂C, h₂, u₂, p₂⟩ := rt_pair_hull_l hKP hC h₁C h₁
  obtain ⟨V₃, h₃C, h₃, u₃, p₃⟩ := rt_pair_hull_l hKP hC h₂C h₂
  obtain ⟨V₄, h₄C, h₄, u₄, p₄⟩ := rt_pair_hull_l hKP hC h₃C h₃
  obtain ⟨F, hFC, hF⟩ := rt_fibers_l hKP hC hU hu
  obtain ⟨T, hTC, hT⟩ := hC.union_l hKP h₄C hFC
  have incl x hx := (hT x).mpr (Or.inl hx)
  have old x hx := incl x (u₄ x (u₃ x (u₂ x (u₁ x hx))))
  have pair {a b p} (ha : M.mem a U) (hb : M.mem b U) (hp : KPair_d M p a b) :=
    rt_pair_to_opair_l p₁ p₂ ha hb hp
  have triple {a b c t} (ha : M.mem a U) (hb : M.mem b U) (hc : M.mem c U) (ht : Rd_triple_d t a b c) : M.mem t T := by
    obtain ⟨q, hq, ht⟩ := ht
    exact incl t (rt_pair_to_opair_l p₃ p₄ (u₂ a (u₁ a ha)) (pair hb hc hq) ht)
  have entry {a x y} (ha : M.mem a U) (h : Rd_entry_d x y a) := rd_entry_transitive_l hu ha h
  refine ⟨T, hTC, ?_, old, ?_⟩
  · intro t ht x hx
    rcases (hT t).mp ht with ht | ht
    · exact incl x (h₄ t ht x hx)
    · obtain ⟨a, b, ha, _, hf⟩ := (hF t).mp ht
      exact old x (entry ha ((hf x).mp hx)).1
  · intro k a b c t ha hb hc ht
    cases k with
    | pair => exact ht.elim (fun h => h ▸ old a ha) (fun h => h ▸ old b hb)
    | diff => exact old t (hu a ha t ht.1)
    | prod =>
      obtain ⟨x, y, hx, hy, hp⟩ := ht
      exact incl t (u₄ t (u₃ t (pair (hu a ha x hx) (hu b hb y hy) hp)))
    | mid =>
      obtain ⟨x, y, z, hy, he, hp⟩ := ht
      exact triple (entry hb he).1 (hu a ha y hy) (entry hb he).2 hp
    | last =>
      obtain ⟨x, y, z, hz, he, hp⟩ := ht
      exact triple (entry hb he).1 (entry hb he).2 (hu a ha z hz) hp
    | union => obtain ⟨x, hx, ht⟩ := ht; exact old t (hu x (hu a ha x hx) t ht)
    | range => obtain ⟨x, he⟩ := ht; exact old t (entry ha he).2
    | mem =>
      obtain ⟨x, y, hx, hy, _, hp⟩ := ht
      exact incl t (u₄ t (u₃ t (pair (hu a ha x hx) (hu a ha y hy) hp)))
    | fibers =>
      obtain ⟨y, hy, hf⟩ := ht
      exact (hT t).mpr (Or.inr ((hF t).mpr ⟨a, y, ha, hu b hb y hy, hf⟩))
    | opair =>
      have bound (hp : Pair_d M t a b) := incl t (u₄ t (u₃ t (u₂ t (p₁ a b t ha hb hp))))
      exact ht.elim (fun hs => incl t (u₄ t (u₃ t (u₂ t (p₁ a a t ha ha
        (fun z => (hs z).trans ⟨Or.inl, fun h => h.elim id id⟩)))))) bound
    | triple =>
      rcases ht with hs | ⟨q, hq, ht⟩
      · exact incl t (u₄ t (u₃ t (u₂ t (p₁ a a t ha ha (fun z => (hs z).trans ⟨Or.inl, fun h => h.elim id id⟩)))))
      · exact incl t (u₄ t (p₃ a q t (u₂ a (u₁ a ha)) (pair hb hc hq) ht))
    | adj => exact ht.elim (fun h => h ▸ old a ha) (fun hp => incl t (u₄ t (u₃ t (pair hb hc hp))))
    | fiber => exact old t (entry ha ht).1

end YesMetaZFC.SetTheory.InnerModel
