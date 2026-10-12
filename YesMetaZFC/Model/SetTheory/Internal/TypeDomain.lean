import YesMetaZFC.Model.SetTheory.Internal.TypePoolBounded

/-! # κ 型的固定常量域

常量域恰为 Vκ 与单个 κ 的并；该条件是有界公式。
在任意更高极限秩层中，实际域与全部查询均自动满足所需秩界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tt_constants0_m {d} (κ B U : Term d) : Formula 1 d := set[d] ⟪
  ⌜B⌝ₛ ⊆ ⌜U⌝ₛ ∧ ⌜κ⌝ₛ ∈ ⌜U⌝ₛ ∧ (∀ x ∈ ⌜U⌝ₛ, x ∈ ⌜B⌝ₛ ∨ x = ⌜κ⌝ₛ)⟫
derive_free_closed tt_constants0_m

theorem tt_constants0_delta_l {d} (κ B U : Term d) : (tt_constants0_m κ B U).IsDelta0 :=
  .conj (.atom ..) (.conj (.mem ..) (.forallMem _ (.disj (.mem ..) (.atom ..))))

theorem tt_constants0_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ B U : Term d) :
    Formula.satisfies ρ (tt_constants0_m κ B U) ↔
      ∀ x, M.mem x (U.eval ρ) ↔ M.mem x (B.eval ρ) ∨ x = κ.eval ρ := by
  simp only [tt_constants0_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun ⟨sub, point, all⟩ x => ⟨all x, fun h => h.elim (sub x) (fun eq => eq.symm ▸ point)⟩,
    fun h => ⟨fun x hx => (h x).mpr (Or.inl hx), (h (κ.eval ρ)).mpr (Or.inr rfl), fun x => (h x).mp⟩⟩

theorem tt_constants_rank_l (hZF : M.Models ZF) {δ Z κ B U : M.Domain}
    (hZ : V_d (kp_pair_l (ZF.modelsKP hZF)) δ Z) (hδ : M.IsLimitOrdinal δ) (hκ : M.mem κ δ)
    (hB : V_d (kp_pair_l (ZF.modelsKP hZF)) κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) : M.mem U Z := by
  obtain ⟨B', U', hB', hU', spec⟩ := tt_constants_exists_l hZF hZ hδ hκ
  have eqB := ZF.v_unique_l _ hZF hB' hB
  subst B'
  exact hZF.1.eq_of_same_members U' U (fun x => (spec x).trans (constants x).symm) ▸ hU'

theorem Tt_pool_d.unique_l (hE : Extensional M) (I : kpair_convention_l.Interpretation M)
    {ω n U D E : M.Domain} (h : Tt_pool_d I ω n U D) (k : Tt_pool_d I ω n U E) : D = E :=
  hE.eq_of_same_members D E (fun p => ⟨h.mono_l I k (fun _ h => h) p, k.mono_l I h (fun _ h => h) p⟩)

/-- 非零极限域已有 ω 与每个内部自然数的合法常量名字。 -/
theorem tt_constants_finite_l (hZF : M.Models ZF) {ω κ n B U : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hκ : M.IsLimitOrdinal κ) (hB : V_d (kp_pair_l (ZF.modelsKP hZF)) κ B) (hc : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) :
    M.mem ω U ∧ M.mem n U := by
  have sub := hω.subset_limitOrdinal hZF hκ
  refine ⟨(hc ω).mpr ?_, (hc n).mpr (Or.inl (ZF.v_ordinal_mem_l (kp_pair_l (ZF.modelsKP hZF)) hZF hB (sub n hn)))⟩
  rcases (hω.isOrdinal hZF).trichotomy hZF.1 hκ.1 (KP.difference_exists_d (ZF.modelsKP hZF))
    (KP.intersection_exists_d (ZF.modelsKP hZF) ω κ) with eq | lt | gt
  · exact Or.inr (hZF.1.eq_of_same_members ω κ eq)
  · exact Or.inl (ZF.v_ordinal_mem_l (kp_pair_l (ZF.modelsKP hZF)) hZF hB lt)
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) κ (sub κ gt)).elim

end YesMetaZFC.SetTheory.Internal
