import YesMetaZFC.SetTheory.Filter.Internal

/-! # 内部滤子的单元素扩张与超滤判据

所有新滤子都由 ZF 分离构造。二择判据使用经典逻辑，但不选择极大扩张；
一般超滤扩张原理不是本模块的 ZF 定理。
-/

namespace YesMetaZFC.SetTheory.FilterZF
open Definitional.Project
universe u
variable {ℳ : Structure.{u}}

def maximal_m {n : Nat} (A F : Term n) : Formula 1 n :=
  .conj (filter_m A F) (.conj (proper_m F) (.forallE
    (.imp (filter_m A.weaken .newest) (.imp (proper_m .newest)
      (.imp (Formula.subset F.weaken .newest) (Formula.subset .newest F.weaken))))))

derive_free_closed maximal_m

theorem maximal_sat_d {n : Nat} (e : Env ℳ n) (A F : Term n) :
    Formula.satisfies e (maximal_m A F) ↔ Maximal_d (A.eval e) (F.eval e) := by
  simp only [maximal_m, Maximal_d, Formula.satisfies_conj_iff, filter_sat_d,
    proper_sat_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, Subset_d, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken]

def adjoin_m : UnarySchema 3 where
  body := .existsE (.conj (.mem (.bound 0) (.bound 3))
    (.forallE (.imp (.mem (.bound 0) (.bound 1))
      (.imp (.mem (.bound 0) (.bound 3)) (.mem (.bound 0) (.bound 2))))))

theorem adjoin_exists_d (hZF : ℳ.Models ZF) {A F B : ℳ.Domain}
    (hF : IsFilter_d (ℳ := ℳ) A F) (hB : Subset_d (ℳ := ℳ) B A) :
    ∃ G, IsFilter_d (ℳ := ℳ) A G ∧ Subset_d (ℳ := ℳ) F G ∧ ℳ.mem B G ∧
      ∀ t, ℳ.mem t G ↔ Subset_d (ℳ := ℳ) t A ∧
        ∃ s, ℳ.mem s F ∧ ∀ x, ℳ.mem x s → ℳ.mem x B → ℳ.mem x t := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF A
  let e : Env ℳ 3 := ⟨fun i => if i = 0 then B else if i = 1 then F else A, fun _ => A⟩
  obtain ⟨G, hG⟩ := ZF.separation_exists_d hZF adjoin_m e P
  have k : ∀ t, ℳ.mem t G ↔ Subset_d (ℳ := ℳ) t A ∧
      ∃ s, ℳ.mem s F ∧ ∀ x, ℳ.mem x s → ℳ.mem x B → ℳ.mem x t := by
    intro t
    rw [hG, hP]
    simp only [adjoin_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Term.eval_bound, Subset_d]
    rfl
  refine ⟨G, ⟨fun t ht => ((k t).mp ht).1,
    (k A).mpr ⟨fun _ hx => hx, A, hF.2.1, fun _ hx _ => hx⟩, ?_, ?_⟩,
    fun s hs => (k s).mpr ⟨hF.1 s hs, s, hs, fun _ hx _ => hx⟩,
    (k B).mpr ⟨hB, A, hF.2.1, fun _ _ hx => hx⟩, k⟩
  · intro s t hs hst ht
    obtain ⟨r, hr, h⟩ := ((k s).mp hs).2
    exact (k t).mpr ⟨ht, r, hr, fun x hx hb => hst x (h x hx hb)⟩
  · intro s t hs ht
    obtain ⟨r, hr, h⟩ := ((k s).mp hs).2
    obtain ⟨q, hq, h₁⟩ := ((k t).mp ht).2
    obtain ⟨v, hv, hvr, hvq⟩ := hF.2.2.2 r q hr hq
    obtain ⟨w, hw⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) v B
    exact ⟨w, (k w).mpr ⟨fun x hx => hB x ((hw x).mp hx).2,
      v, hv, fun x hx hb => (hw x).mpr ⟨hx, hb⟩⟩,
      fun x hx => h x (hvr x ((hw x).mp hx).1) ((hw x).mp hx).2,
      fun x hx => h₁ x (hvq x ((hw x).mp hx).1) ((hw x).mp hx).2⟩

theorem adjoin_proper_d {A F B C G : ℳ.Domain}
    (hF : IsFilter_d (ℳ := ℳ) A F)
    (hC : ∀ x, ℳ.mem x C ↔ ℳ.mem x A ∧ ¬ ℳ.mem x B)
    (hG : ∀ t, ℳ.mem t G ↔ Subset_d (ℳ := ℳ) t A ∧
      ∃ s, ℳ.mem s F ∧ ∀ x, ℳ.mem x s → ℳ.mem x B → ℳ.mem x t)
    (h : ¬ ℳ.mem C F) : Proper_d (ℳ := ℳ) G := by
  intro t ht
  obtain ⟨s, hs, k⟩ := ((hG t).mp ht).2
  apply Classical.byContradiction
  intro h₁
  apply h
  apply hF.2.2.1 s C hs
  · intro x hx
    exact (hC x).mpr ⟨hF.1 s hs x hx, fun hb => h₁ ⟨x, k x hx hb⟩⟩
  · exact fun x hx => ((hC x).mp hx).1

/-- 极大内部适当滤子决定每个内部子集，ZF 已足够。 -/
theorem maximal_decides_d (hZF : ℳ.Models ZF) {A F B C : ℳ.Domain}
    (h : Maximal_d (ℳ := ℳ) A F) (hB : Subset_d (ℳ := ℳ) B A)
    (hC : ∀ x, ℳ.mem x C ↔ ℳ.mem x A ∧ ¬ ℳ.mem x B) :
    ℳ.mem B F ∨ ℳ.mem C F := by
  rcases Classical.em (ℳ.mem C F) with hc | hc
  · exact Or.inr hc
  · obtain ⟨G, hG, hFG, hb, k⟩ := adjoin_exists_d hZF h.1 hB
    exact Or.inl (h.2.2 G hG (adjoin_proper_d h.1 hC k hc) hFG B hb)

/-- 二择性质反推极大性；互补集合仍是内部集合。 -/
theorem maximal_of_decides_d (hZF : ℳ.Models ZF) {A F : ℳ.Domain}
    (hF : IsFilter_d (ℳ := ℳ) A F) (h : Proper_d (ℳ := ℳ) F)
    (k : ∀ B C, Subset_d (ℳ := ℳ) B A →
      (∀ x, ℳ.mem x C ↔ ℳ.mem x A ∧ ¬ ℳ.mem x B) → ℳ.mem B F ∨ ℳ.mem C F) :
    Maximal_d (ℳ := ℳ) A F := by
  refine ⟨hF, h, fun G hG hp hFG B hb => ?_⟩
  obtain ⟨C, hc⟩ := KP.difference_exists_d (ZF.modelsKP hZF) B A
  rcases k B C (hG.1 B hb) hc with h₁ | h₁
  · exact h₁
  · obtain ⟨r, hr, hrB, hrC⟩ := hG.2.2.2 B C hb (hFG C h₁)
    obtain ⟨x, hx⟩ := hp r hr
    exact False.elim (((hc x).mp (hrC x hx)).2 (hrB x hx))

end YesMetaZFC.SetTheory.FilterZF
