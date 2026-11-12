import YesMetaZFC.SetTheory.Filter.Extension

/-! # 容许子集代数上的滤子

共同细化族足以形成约化幂的商。相对超滤只在指定的实际集合代数内向上封闭
并作二择；不要求源模型拥有背景中的全部子集。
-/
namespace YesMetaZFC.SetTheory.FilterZF
open Definitional.Project
universe u
variable {ℳ : Structure.{u}}

structure Base_d (D U : ℳ.Domain) : Prop where
  bounds : ∀ A, ℳ.mem A U → ℳ.MemberSubset A D
  top : ℳ.mem D U
  meet : ∀ A B, ℳ.mem A U → ℳ.mem B U → ∃ C, ℳ.mem C U ∧ ℳ.MemberSubset C A ∧ ℳ.MemberSubset C B

def base_m {n} (D U : Term n) : Formula 1 n := .conj
  (Formula.forallMem U (Formula.subset .newest D.weaken)) (.conj (.mem D U)
    (Formula.forallMem U (Formula.forallMem U.weaken (Formula.existsMem U.weaken.weaken
      (.conj (Formula.subset .newest (.bound 2)) (Formula.subset .newest (.bound 1)))))))
derive_free_closed base_m

theorem base_sat_l {n} (ρ : Env ℳ n) (D U : Term n) :
    Formula.satisfies ρ (base_m D U) ↔ Base_d (D.eval ρ) (U.eval ρ) := by
  simp only [base_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, h.2.1, fun A B hA hB => h.2.2 A hA B hB⟩,
    fun h => ⟨h.bounds, h.top, fun A hA B hB => h.meet A B hA hB⟩⟩

theorem IsFilter_d.base_l {D U : ℳ.Domain} (h : IsFilter_d (ℳ := ℳ) D U) : Base_d D U :=
  ⟨h.1, h.2.1, h.2.2.2⟩

structure Field_d (D B : ℳ.Domain) : Prop where
  bounds : ∀ A, ℳ.mem A B → ℳ.MemberSubset A D
  top : ℳ.mem D B
  diff : ∀ A, ℳ.mem A B → ∃ C, ℳ.mem C B ∧ ∀ x, ℳ.mem x C ↔ ℳ.mem x D ∧ ¬ ℳ.mem x A
  inter : ∀ A C, ℳ.mem A B → ℳ.mem C B → ∃ E, ℳ.mem E B ∧ ∀ x, ℳ.mem x E ↔ ℳ.mem x A ∧ ℳ.mem x C

def field_m {n} (D B : Term n) : Formula 1 n := .conj
  (Formula.forallMem B (Formula.subset .newest D.weaken)) (.conj (.mem D B) (.conj
    (Formula.forallMem B (Formula.existsMem B.weaken (.forallE (.iff (.mem .newest (.bound 1))
      (.conj (.mem .newest D.weaken.weaken.weaken) (.neg (.mem .newest (.bound 2))))))))
    (Formula.forallMem B (Formula.forallMem B.weaken (Formula.existsMem B.weaken.weaken (.forallE
      (.iff (.mem .newest (.bound 1)) (.conj (.mem .newest (.bound 3)) (.mem .newest (.bound 2))))))))))
derive_free_closed field_m

theorem field_sat_l {n} (ρ : Env ℳ n) (D B : Term n) :
    Formula.satisfies ρ (field_m D B) ↔ Field_d (D.eval ρ) (B.eval ρ) := by
  simp only [field_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, fun A C hA hC => h.2.2.2 A hA C hC⟩,
    fun h => ⟨h.bounds, h.top, h.diff, fun A hA C hC => h.inter A C hA hC⟩⟩

theorem field_power_l (hKP : ℳ.Models KP) {D B} (hB : ℳ.IsPowerSetOf B D) : Field_d D B := by
  refine ⟨fun A hA => (hB A).mp hA, (hB D).mpr (fun _ h => h), ?_, ?_⟩
  · intro A _
    obtain ⟨C, hC⟩ := KP.difference_exists_d hKP A D
    exact ⟨C, (hB C).mpr (fun x hx => ((hC x).mp hx).1), hC⟩
  · intro A C hA _
    obtain ⟨E, hE⟩ := KP.intersection_exists_d hKP A C
    exact ⟨E, (hB E).mpr (fun x hx => (hB A).mp hA x ((hE x).mp hx).1), hE⟩

structure Rel_ultra_d (D B U : ℳ.Domain) : Prop where
  field : Field_d D B
  base : Base_d D U
  admissible : ℳ.MemberSubset U B
  upward : ∀ A C, ℳ.mem A U → ℳ.mem C B → ℳ.MemberSubset A C → ℳ.mem C U
  proper : Proper_d (ℳ := ℳ) U
  decides : ∀ A C, ℳ.mem A B → ℳ.mem C B →
    (∀ x, ℳ.mem x C ↔ ℳ.mem x D ∧ ¬ ℳ.mem x A) → ℳ.mem A U ∨ ℳ.mem C U

def rel_ultra_m {n} (D B U : Term n) : Formula 1 n := .conj (field_m D B) (.conj (base_m D U)
  (.conj (Formula.subset U B) (.conj
    (Formula.forallMem U (Formula.forallMem B.weaken (.imp (Formula.subset (.bound 1) .newest) (.mem .newest U.weaken.weaken))))
    (.conj (proper_m U) (Formula.forallMem B (Formula.forallMem B.weaken (.imp
      (.forallE (.iff (.mem .newest (.bound 1)) (.conj (.mem .newest D.weaken.weaken.weaken) (.neg (.mem .newest (.bound 2))))))
      (.disj (.mem (.bound 1) U.weaken.weaken) (.mem .newest U.weaken.weaken)))))))))
derive_free_closed rel_ultra_m

theorem rel_ultra_sat_l {n} (ρ : Env ℳ n) (D B U : Term n) :
    Formula.satisfies ρ (rel_ultra_m D B U) ↔ Rel_ultra_d (D.eval ρ) (B.eval ρ) (U.eval ρ) := by
  simp only [rel_ultra_m, Formula.satisfies_conj_iff, field_sat_l, base_sat_l,
    Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, proper_sat_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_disj_iff, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, fun A C hA hC => h.2.2.2.1 A hA C hC, h.2.2.2.2.1,
      fun A C hA hC => h.2.2.2.2.2 A hA C hC⟩,
    fun h => ⟨h.field, h.base, h.admissible, (fun A hA C hC => h.upward A C hA hC), h.proper,
      fun A hA C hC => h.decides A C hA hC⟩⟩

/-- 容许域为完整幂集时，相对超滤精确恢复原集合超滤接口。 -/
theorem Rel_ultra_d.full_l (hKP : ℳ.Models KP) {D B U} (h : Rel_ultra_d (ℳ := ℳ) D B U)
    (hB : ℳ.IsPowerSetOf B D) : Maximal_d (ℳ := ℳ) D U := by
  have hf : IsFilter_d (ℳ := ℳ) D U := ⟨h.base.bounds, h.base.top,
    fun A C hA hAC hC => h.upward A C hA ((hB C).mpr hC) hAC, h.base.meet⟩
  exact maximal_of_decides_d hKP hf h.proper fun A C hA hC =>
    h.decides A C ((hB A).mpr hA) ((hB C).mpr fun x hx => ((hC x).mp hx).1) hC

theorem maximal_relative_l (hKP : ℳ.Models KP) {D B U} (h : Maximal_d (ℳ := ℳ) D U)
    (hB : ℳ.IsPowerSetOf B D) : Rel_ultra_d D B U := by
  refine ⟨field_power_l hKP hB, h.1.base_l, fun A hA => (hB A).mpr (h.1.1 A hA), ?_, h.2.1, ?_⟩
  · exact fun A C hA hC hAC => h.1.2.2.1 A C hA hAC ((hB C).mp hC)
  · exact fun A C hA _ hC => maximal_decides_d hKP hB h ((hB A).mp hA) hC

theorem Rel_ultra_d.complement_l {D B U A C} (h : Rel_ultra_d (ℳ := ℳ) D B U)
    (hA : ℳ.mem A B) (hC : ℳ.mem C B) (hc : ∀ x, ℳ.mem x C ↔ ℳ.mem x D ∧ ¬ ℳ.mem x A) :
    ℳ.mem C U ↔ ¬ ℳ.mem A U := by
  have disjoint (ha : ℳ.mem A U) (hb : ℳ.mem C U) : False := by
    obtain ⟨E, hE, hEA, hEC⟩ := h.base.meet A C ha hb
    obtain ⟨x, hx⟩ := h.proper E hE
    exact ((hc x).mp (hEC x hx)).2 (hEA x hx)
  exact ⟨fun hC hA => disjoint hA hC, fun hn => (h.decides A C hA hC hc).elim (fun ha => (hn ha).elim) id⟩

/-- 三个实际容许集合满足或非方程时，其超滤成员资格满足同一方程。 -/
theorem Rel_ultra_d.nor_l {D P U A B C} (h : Rel_ultra_d (ℳ := ℳ) D P U)
    (ha : ℳ.mem A P) (hb : ℳ.mem B P) (hc : ℳ.mem C P)
    (hs : ∀ x, ℳ.mem x C ↔ ℳ.mem x D ∧ ¬ (ℳ.mem x A ∨ ℳ.mem x B)) :
    ℳ.mem C U ↔ ¬ (ℳ.mem A U ∨ ℳ.mem B U) := by
  obtain ⟨A', ha', hA⟩ := h.field.diff A ha
  obtain ⟨B', hb', hB⟩ := h.field.diff B hb
  have inter : ℳ.mem C U ↔ ℳ.mem A' U ∧ ℳ.mem B' U := by
    refine ⟨fun hC => ⟨h.upward C A' hC ha' ?_, h.upward C B' hC hb' ?_⟩, ?_⟩
    · exact fun x hx => (hA x).mpr ⟨((hs x).mp hx).1, fun ha => ((hs x).mp hx).2 (Or.inl ha)⟩
    · exact fun x hx => (hB x).mpr ⟨((hs x).mp hx).1, fun hb => ((hs x).mp hx).2 (Or.inr hb)⟩
    · rintro ⟨hA', hB'⟩
      obtain ⟨W, hW, hwA, hwB⟩ := h.base.meet A' B' hA' hB'
      exact h.upward W C hW hc (fun x hx => (hs x).mpr
        ⟨((hA x).mp (hwA x hx)).1, fun h => h.elim ((hA x).mp (hwA x hx)).2 ((hB x).mp (hwB x hx)).2⟩)
  exact inter.trans ((and_congr (h.complement_l ha ha' hA) (h.complement_l hb hb' hB)).trans
    ⟨fun ⟨ha, hb⟩ h => h.elim ha hb, fun h => ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩⟩)

end YesMetaZFC.SetTheory.FilterZF
