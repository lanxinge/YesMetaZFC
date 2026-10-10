import YesMetaZFC.SetTheory.Card.Finite
import YesMetaZFC.SetTheory.Ord.Recursion

/-! # 内部有限序数集的最大元与并界

对原公式作有限集合插入归纳，故这里的有限性允许模型中的非标准自然数界。
非空有限序数集有最大元；因此有限个属于序数并的坐标落在同一个成员中。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 非空内部有限序数子集的最大元；不使用选择公理。 -/
theorem finite_max_l (hZF : M.Models ZF) {ω α D} (hω : M.IsOmega ω)
    (hα : M.IsOrdinal α) (hD : Finite_d I ω D) (hd : M.MemberSubset D α)
    (hne : ∃ i, M.mem i D) : ∃ m, M.mem m D ∧ ∀ i, M.mem i D → M.mem i m ∨ i = m := by
  let ρ : Env M 1 := ⟨fun _ => α, fun _ => α⟩
  let φ : UnarySchema 1 := {
    body := .imp (Formula.subset .newest (.bound 1))
      (.disj (.forallE (.neg (.mem .newest (.bound 1))))
        (.existsE (.conj (.mem .newest (.bound 1))
          (Formula.forallMem (.bound 1) (.disj (.mem .newest (.bound 1))
            (Formula.extensionalEq .newest (.bound 1))))))) }
  have hφ X : φ.denote ρ X ↔ M.MemberSubset X α →
      (∀ i, ¬ M.mem i X) ∨ ∃ m, M.mem m X ∧ ∀ i, M.mem i X → M.mem i m ∨ i = m := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_forall_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_forallMem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  have h := finite_ind_l I hZF hω φ ρ (fun E he => (hφ E).mpr (fun _ => Or.inl he))
    (fun X a Y _ ih hY => (hφ Y).mpr (fun hy => by
      have ha := (hY a).mpr (Or.inr rfl)
      rcases (hφ X).mp ih (fun i hi => hy i ((hY i).mpr (Or.inl hi))) with he | ⟨m, hm, hmax⟩
      · exact Or.inr ⟨a, ha, fun i hi => ((hY i).mp hi).elim
          (fun h => False.elim (he i h)) Or.inr⟩
      · have hmY := (hY m).mpr (Or.inl hm)
        rcases hα.wellOrder.linear.compare m (hy m hmY) a (hy a ha) with he | hma | ham
        · have he := hZF.1.eq_of_same_members m a he
          subst m
          exact Or.inr ⟨a, ha, fun i hi => ((hY i).mp hi).elim (hmax i) Or.inr⟩
        · exact Or.inr ⟨a, ha, fun i hi => ((hY i).mp hi).elim
            (fun hi => (hmax i hi).elim (fun him => Or.inl ((hα.mem (hy a ha)).transitive m hma i him))
              (fun he => Or.inl (he ▸ hma))) Or.inr⟩
        · exact Or.inr ⟨m, hmY, fun i hi => ((hY i).mp hi).elim (hmax i)
            (fun he => Or.inl (he ▸ ham))⟩)) D hD
  exact ((hφ D).mp h hd).elim (fun he => False.elim (hne.elim fun i hi => he i hi)) id

/-- 序数并中的有限子集由一个阶段界住；空支撑只要求阶段集非空。 -/
theorem finite_union_bound_l (hZF : M.Models ZF) {ω δ σ D} (hω : M.IsOmega ω)
    (hδ : M.IsOrdinal δ) (hσ : M.IsUnionOf σ δ) (hne : ∃ α, M.mem α δ)
    (hD : Finite_d I ω D) (hd : M.MemberSubset D σ) :
    ∃ α, M.mem α δ ∧ M.MemberSubset D α := by
  classical
  by_cases he : ∃ i, M.mem i D
  · have hDδ : M.MemberSubset D δ := fun i hi => by
      obtain ⟨α, hα, hiα⟩ := (hσ i).mp (hd i hi)
      exact hδ.transitive α hα i hiα
    obtain ⟨m, hm, hmax⟩ := finite_max_l I hZF hω hδ hD hDδ he
    obtain ⟨α, hα, hmα⟩ := (hσ m).mp (hd m hm)
    exact ⟨α, hα, fun i hi => (hmax i hi).elim
      (fun him => (hδ.mem hα).transitive m hmα i him) (fun he => he ▸ hmα)⟩
  · obtain ⟨α, hα⟩ := hne
    exact ⟨α, hα, fun i hi => False.elim (he ⟨i, hi⟩)⟩

end YesMetaZFC.SetTheory.ZF
