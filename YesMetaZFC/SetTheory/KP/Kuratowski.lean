import YesMetaZFC.SetTheory.KP.Sigma1
import YesMetaZFC.SetTheory.Kuratowski

/-! # KP 中的有界配对图与笛卡尔积

有序对的见证取自输出本身，故实际图是 Δ₀。两次 Δ₀ 替换及一次并集构造
笛卡尔积；本层不消费 ZF 的全收集或幂集。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}}

def pair0_m {n} (p x y : Term n) : Formula 1 n :=
  .conj (.mem x p) (.conj (.mem y p) (Formula.forallMem p
    (.disj (Formula.extensionalEq .newest x.weaken) (Formula.extensionalEq .newest y.weaken))))
derive_free_closed pair0_m

theorem pair0_delta_l {n} (p x y : Term n) : (pair0_m p x y).IsDelta0 :=
  .conj (.mem _ _) (.conj (.mem _ _) (.forallMem _ (.disj (.atom _ _ _) (.atom _ _ _))))

theorem pair0_sat_l (hE : Extensional M) {n} (ρ : Env M n) (p x y : Term n) :
    Formula.satisfies ρ (pair0_m p x y) ↔ Pair_d M (p.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [pair0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]
  exact ⟨fun ⟨hx, hy, h⟩ t => ⟨h t, fun he => he.elim (fun he => he.symm ▸ hx) (fun he => he.symm ▸ hy)⟩,
    fun h => ⟨(h _).mpr (Or.inl rfl), (h _).mpr (Or.inr rfl), fun t => (h t).mp⟩⟩

def kpair0_m {n} (p x y : Term n) : Formula 1 n :=
  Formula.existsMem p (Formula.existsMem p.weaken
    (.conj (pair0_m (.bound 1) x.weaken.weaken x.weaken.weaken)
      (.conj (pair0_m .newest x.weaken.weaken y.weaken.weaken) (pair0_m p.weaken.weaken (.bound 1) .newest))))
derive_free_closed kpair0_m

theorem kpair0_delta_l {n} (p x y : Term n) : (kpair0_m p x y).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (pair0_delta_l ..) (.conj (pair0_delta_l ..) (pair0_delta_l ..))))

theorem kpair0_sat_l (hE : Extensional M) {n} (ρ : Env M n) (p x y : Term n) :
    Formula.satisfies ρ (kpair0_m p x y) ↔ KPair_d M (p.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [kpair0_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, pair0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨s, _, t, _, hs, ht, hp⟩
    exact ⟨s, t, fun z => (hs z).trans ⟨fun h => h.elim id id, Or.inl⟩, ht, hp⟩
  · rintro ⟨s, t, hs, ht, hp⟩
    exact ⟨s, (hp s).mpr (Or.inl rfl), t, (hp t).mpr (Or.inr rfl),
      (fun z => (hs z).trans ⟨Or.inl, fun h => h.elim id id⟩), ht, hp⟩

namespace KP

theorem krow_exists_l (hKP : M.Models KP) (x Y : M.Domain) :
    ∃ D, ∀ p, M.mem p D ↔ ∃ y, M.mem y Y ∧ KPair_d M p x y := by
  let φ : Delta0BinarySchema 1 := {
    body := kpair0_m .newest (.bound 2) (.bound 1)
    delta0 := kpair0_delta_l .. }
  let ρ : Env M 1 := ⟨fun _ => x, fun _ => x⟩
  have hφ y p : φ.toBinarySchema.denote ρ y p ↔ KPair_d M p x y := kpair0_sat_l hKP.1 _ _ _ _
  let I := kpair_interpretation_l M hKP.1 (exists_pair hKP)
  simpa only [hφ] using d0_image_l hKP φ ρ Y
    (fun y _ => (I.total x y).imp (fun p hp => (hφ y p).mpr hp))
    (fun y _ p q hp hq => kpair_unique_l M hKP.1 ((hφ y p).mp hp) ((hφ y q).mp hq))

private def krow_m {n} (D x Y : Term n) : Formula 1 n :=
  .conj (Formula.forallMem D (Formula.existsMem Y.weaken (kpair0_m (.bound 1) x.weaken.weaken .newest)))
    (Formula.forallMem Y (Formula.existsMem D.weaken (kpair0_m .newest x.weaken.weaken (.bound 1))))
derive_free_closed krow_m

private theorem krow_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (D x Y : Term n) :
    Formula.satisfies ρ (krow_m D x Y) ↔
      ∀ p, M.mem p (D.eval ρ) ↔ ∃ y, M.mem y (Y.eval ρ) ∧ KPair_d M p (x.eval ρ) y := by
  simp only [krow_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, kpair0_sat_l hKP.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨h, g⟩ p
    refine ⟨h p, fun ⟨y, hy, hp⟩ => ?_⟩
    obtain ⟨q, hq, hqy⟩ := g y hy
    exact (kpair_unique_l M hKP.1 hqy hp) ▸ hq
  · intro h
    refine ⟨fun p => (h p).mp, fun y hy => ?_⟩
    obtain ⟨p, hp⟩ := (kpair_interpretation_l M hKP.1 (exists_pair hKP)).total (x.eval ρ) y
    exact ⟨p, (h p).mpr ⟨y, hy, hp⟩, hp⟩

/-- KP 已足以构造标准 Kuratowski 笛卡尔积。 -/
theorem kprod_exists_l (hKP : M.Models KP) (X Y : M.Domain) :
    ∃ D, ∀ p, M.mem p D ↔ ∃ x, M.mem x X ∧ ∃ y, M.mem y Y ∧ KPair_d M p x y := by
  let φ : Delta0BinarySchema 1 := {
    body := krow_m .newest (.bound 1) (.bound 2)
    delta0 := .conj (.forallMem _ (.existsMem _ (kpair0_delta_l ..)))
      (.forallMem _ (.existsMem _ (kpair0_delta_l ..))) }
  let ρ : Env M 1 := ⟨fun _ => Y, fun _ => Y⟩
  have hφ x D : φ.toBinarySchema.denote ρ x D ↔
      ∀ p, M.mem p D ↔ ∃ y, M.mem y Y ∧ KPair_d M p x y := krow_sat_l hKP _ _ _ _
  obtain ⟨C, hC⟩ := d0_image_l hKP φ ρ X
    (fun x _ => (krow_exists_l hKP x Y).imp (fun D hD => (hφ x D).mpr hD))
    (fun x _ D E hD hE => hKP.1.eq_of_same_members D E
      (fun p => ((hφ x D).mp hD p).trans ((hφ x E).mp hE p).symm))
  obtain ⟨D, hD⟩ := exists_union hKP C
  refine ⟨D, fun p => (hD p).trans ?_⟩
  constructor
  · rintro ⟨B, hB, hp⟩
    obtain ⟨x, hx, hB⟩ := (hC B).mp hB
    exact ⟨x, hx, ((hφ x B).mp hB p).mp hp⟩
  · rintro ⟨x, hx, y, hy, hp⟩
    obtain ⟨B, hB⟩ := krow_exists_l hKP x Y
    exact ⟨B, (hC B).mpr ⟨x, hx, (hφ x B).mpr hB⟩, (hB p).mpr ⟨y, hy, hp⟩⟩

end KP
end YesMetaZFC.SetTheory
