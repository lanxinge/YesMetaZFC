import YesMetaZFC.SetTheory.TransitiveClosure
import YesMetaZFC.SetTheory.RankImage
import YesMetaZFC.SetTheory.Card.Finite

/-! # 内部遗传大小与 H(κ)

遗传大小小于 κ，指 TC({x}) 可单射到某个 μ∈κ。κ 为基数时，这些对象全部
位于 Vκ，故 H(κ) 由实际分离构造。定义本身不以层级截断替代遗传大小条件。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Hmem_d (κ x : M.Domain) : Prop := ∃ T μ,
  Tc_d (M := M) x T ∧ M.mem μ κ ∧ M.CardinalLessOrEqual I T μ

def hmem_m {n} (κ x : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (tc_m x.weaken.weaken (.bound 1))
    (.conj (.mem .newest κ.weaken.weaken) (Formula.cardinalLessOrEqual 𝒞 (.bound 1) .newest))))
derive_free_closed hmem_m

theorem hmem_sat_l (hE : Extensional M) {n} (ρ : Env M n) (κ x : Term n) :
    Formula.satisfies ρ (hmem_m (𝒞 := 𝒞) κ x) ↔ Hmem_d I (κ.eval ρ) (x.eval ρ) := by
  simp only [hmem_m, Hmem_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tc_sat_l, Formula.satisfies_mem_iff, Formula.satisfies_cardinalLessOrEqual_iff I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def H_d (κ H : M.Domain) : Prop := ∀ x, M.mem x H ↔ Hmem_d I κ x

def h_m {n} (κ H : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest H.weaken) (hmem_m (𝒞 := 𝒞) κ.weaken .newest))
derive_free_closed h_m

theorem h_sat_l (hE : Extensional M) {n} (ρ : Env M n) (κ H : Term n) :
    Formula.satisfies ρ (h_m (𝒞 := 𝒞) κ H) ↔ H_d I (κ.eval ρ) (H.eval ρ) := by
  simp only [h_m, H_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, hmem_sat_l I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem h_unique_l (hE : Extensional M) {κ H K} (h : H_d I κ H) (k : H_d I κ K) : H = K :=
  hE.eq_of_same_members H K (fun x => (h x).trans (k x).symm)

namespace ZF

theorem hmem_size_l (hZF : M.Models ZF) {κ x} (hx : Hmem_d I κ x) :
    ∃ μ, M.mem μ κ ∧ M.CardinalLessOrEqual I x μ := by
  obtain ⟨T, μ, hT, hμ, ht⟩ := hx
  obtain ⟨F, hF⟩ := exists_inclusionInjection hZF I (hT.1 x hT.2.1)
  obtain ⟨G, hG⟩ := ht
  exact ⟨μ, hμ, exists_compositionInjection hZF I hF hG⟩

theorem hmem_of_transitive_l (hZF : M.Models ZF) {κ x T μ} (hT : M.TransitiveSet T)
    (hx : M.mem x T) (hμ : M.mem μ κ) (ht : M.CardinalLessOrEqual I T μ) : Hmem_d I κ x := by
  obtain ⟨S, hS⟩ := tc_exists_l I hZF x
  obtain ⟨F, hF⟩ := exists_inclusionInjection hZF I (hS.2.2 T hT hx)
  obtain ⟨G, hG⟩ := ht
  exact ⟨S, μ, hS, hμ, exists_compositionInjection hZF I hF hG⟩

/-- 原 ZF 中实际构造 H(κ)，并证明没有遗漏 Vκ 以外的遗传小对象。 -/
theorem h_exists_l (hZF : M.Models ZF) {κ} (hκ : M.IsCardinal I κ) : ∃ H, H_d I κ H := by
  obtain ⟨V, hV⟩ := v_exists_l I hZF hκ.1
  let ρ : Env M 1 := ⟨fun _ => κ, fun _ => κ⟩
  let φ : UnarySchema 1 := { body := hmem_m (𝒞 := 𝒞) (.bound 1) .newest }
  obtain ⟨H, hH⟩ := separation_exists_d hZF φ ρ V
  refine ⟨H, fun x => (hH x).trans ?_⟩
  have hx : φ.denote ρ x ↔ Hmem_d I κ x := hmem_sat_l I hZF.1 _ _ _
  change (M.mem x V ∧ φ.denote ρ x) ↔ _
  rw [hx]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨T, μ, hT, hμ, ht⟩ := h
  exact rk_transitive_bound_l I hZF hT.1 hκ hμ ht hV x hT.2.1

theorem h_transitive_l (hZF : M.Models ZF) {κ H} (hH : H_d I κ H) : M.TransitiveSet H := by
  intro x hx y hy
  obtain ⟨T, μ, hT, hμ, ht⟩ := (hH x).mp hx
  exact (hH y).mpr (hmem_of_transitive_l I hZF hT.1 (hT.1 x hT.2.1 y hy) hμ ht)

/-- 小传递集合的任意子集也遗传小；追加该子集只增加一个基数槽位。 -/
theorem hmem_of_subset_l (hZF : M.Models ZF) {κ T μ D} (hκ : M.IsLimitOrdinal κ)
    (hT : M.TransitiveSet T) (hDT : M.MemberSubset D T) (hμ : M.mem μ κ)
    (ht : M.CardinalLessOrEqual I T μ) : Hmem_d I κ D := by
  obtain ⟨S, hS⟩ := KP.exists_insert (modelsKP hZF) T D
  have hSt : M.TransitiveSet S := by
    intro x hx y hy
    apply (hS y).mpr
    rcases (hS x).mp hx with hx | rfl
    · exact Or.inl (hT x hx y hy)
    · exact Or.inl (hDT y hy)
  obtain ⟨ν, hν, hμν⟩ := hκ.2.2 μ hμ
  obtain ⟨σ, hσ⟩ := KP.exists_successor (modelsKP hZF) μ
  obtain ⟨F, hF⟩ := insert_bound_l I hZF hσ ht hS
  have hσν : M.MemberSubset σ ν := by
    intro i hi
    rcases (hσ i).mp hi with hi | hi
    · exact (hκ.1.mem hν).transitive μ hμν i hi
    · exact (hZF.1.eq_of_same_members i μ hi).symm ▸ hμν
  obtain ⟨G, hG⟩ := exists_inclusionInjection hZF I hσν
  exact hmem_of_transitive_l I hZF hSt ((hS D).mpr (Or.inr rfl)) hν
    (exists_compositionInjection hZF I hF hG)

/-- 极限指标下 H(κ) 对其元素的全部实际子集封闭；不要求强极限性。 -/
theorem h_subsets_l (hZF : M.Models ZF) {κ H B} (hκ : M.IsLimitOrdinal κ)
    (hH : H_d I κ H) (hB : M.mem B H) : ∀ D, M.MemberSubset D B → M.mem D H := by
  obtain ⟨T, μ, hT, hμ, ht⟩ := (hH B).mp hB
  exact fun D hDB => (hH D).mpr (hmem_of_subset_l I hZF hκ hT.1
    (fun x hx => hT.1 B hT.2.1 x (hDB x hx)) hμ ht)

/-- 极限指标以下的每个序数都属于相应的遗传小集合。 -/
theorem h_ordinal_l (hZF : M.Models ZF) {κ H α} (hκ : M.IsLimitOrdinal κ)
    (hH : H_d I κ H) (hα : M.mem α κ) : M.mem α H :=
  (hH α).mpr (hmem_of_subset_l I hZF hκ (hκ.1.mem hα).transitive (fun _ h => h) hα
    (exists_inclusionInjection hZF I (fun _ h => h)))

end ZF
end YesMetaZFC.SetTheory
