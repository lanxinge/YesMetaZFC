import YesMetaZFC.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.Fiber
import YesMetaZFC.SetTheory.Card.CountablePair

/-! # 模型内部的可数并

先在模型内统一选择各成员到 ω 的单射，再把并集单射到 ω×ω，最后用已有 Cantor
配对定理压回 ω。成员的枚举与单射见证均为内部集合编码函数。
-/

namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- κ 个大小不超过 κ 的集合，其并可单射到 κ×κ；不预设 κ 为基数。 -/
theorem union_bound_l (hZFC : M.Models ZFC) {κ A U W : M.Domain}
    (hA : M.CardinalLessOrEqual I A κ) (hU : M.IsUnionOf U A)
    (hc : ∀ T, M.mem T A → M.CardinalLessOrEqual I T κ)
    (hW : M.IsCartesianProduct I W κ κ) : M.CardinalLessOrEqual I U W := by
  obtain ⟨f, hf⟩ := hA
  let hZF := models_zf_l hZFC
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I U κ
  obtain ⟨K, hK⟩ := ZF.exists_powerSet hZF P
  let φ : BinarySchema 1 := { body := Formula.isInjectionFromTo 𝒞 .newest (.bound 1) (.bound 2) }
  let ρ : Env M 1 := ⟨fun _ => κ, fun _ => κ⟩
  have hφ T j : φ.denote ρ T j ↔ M.IsSetInjectionFromTo I j T κ :=
    Formula.satisfies_isInjectionFromTo_iff I hZF.1 ((ρ.push T).push j) .newest (.bound 1) (.bound 2)
  obtain ⟨G, hG, hg⟩ := uniformize_formula_l I hZFC φ ρ (X := A) (Y := K) (by
    intro T hT
    obtain ⟨j, hj⟩ := hc T hT
    refine ⟨j, (hK j).mpr ?_, (hφ T j).mpr hj⟩
    intro q hq
    obtain ⟨x, n, hcode⟩ := hj.1.1.1 q hq
    have hxn : M.PairMember I x n j := ⟨q, hcode, hq⟩
    exact (hP q).mpr ⟨x, (hU x).mpr ⟨T, hT, hj.1.input_mem_of_pairMember hxn⟩,
      n, hj.1.output_mem_of_pairMember hxn, hcode⟩)
  have hg {T j} (h : M.PairMember I T j G) : M.IsSetInjectionFromTo I j T κ := (hφ T j).mp (hg T j h)
  let δ : Env M 2 := (⟨fun _ => f, fun _ => f⟩ : Env M 1).push G
  let ψ : BinarySchema 2 := {
    body := .existsE (.existsE (.existsE (.existsE (.conj (𝒞.code (.bound 4) (.bound 3) (.bound 2))
      (.conj (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 3) (.bound 7))
        (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 6))
          (Formula.orderedPairMem 𝒞 (.bound 5) (.bound 2) .newest))))))) }
  have hψ x q : ψ.denote δ x q ↔ ∃ n k T j,
      I.Codes q n k ∧ M.PairMember I T n f ∧ M.PairMember I T j G ∧ M.PairMember I x k j := by
    simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨H, hH, hh⟩ := uniformize_formula_l I hZFC ψ δ (X := U) (Y := W) (by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := (hU x).mp hx
    obtain ⟨n, hn, hnT⟩ := hf.1.2.2 T hT
    obtain ⟨j, _, hTj⟩ := hG.2.2 T hT
    obtain ⟨k, hk, hxk⟩ := (hg hTj).1.2.2 x hxT
    obtain ⟨q, hq⟩ := I.total n k
    exact ⟨q, (hW q).mpr ⟨n, hn, k, hk, hq⟩, (hψ x q).mpr ⟨n, k, T, j, hq, hnT, hTj, hxk⟩⟩)
  have hinj : M.IsSetInjectionFromTo I H U W := by
    refine ⟨hH, fun x y q hx hy => ?_⟩
    obtain ⟨n, k, T, j, hq, hnT, hTj, hxj⟩ := (hψ x q).mp (hh x q hx)
    obtain ⟨m, l, V, e, hq', hmV, hVe, hye⟩ := (hψ y q).mp (hh y q hy)
    obtain ⟨rfl, rfl⟩ := I.injective hq hq'
    have he := hf.2 T V n hnT hmV
    subst V
    have he := hG.1.2 T j e hTj hVe
    subst e
    exact (hg hTj).2 x y k hxj hye
  exact ⟨H, hinj⟩

/-- 可数集合族的可数并；族只须可数，不要求预先给出满枚举。 -/
theorem countable_union_l (hZFC : M.Models ZFC) {ω A U : M.Domain} (hω : M.IsOmega ω)
    (hA : M.CardinalLessOrEqual I A ω) (hU : M.IsUnionOf U A)
    (hc : ∀ T, M.mem T A → M.CardinalLessOrEqual I T ω) : M.CardinalLessOrEqual I U ω := by
  let hZF := models_zf_l hZFC
  obtain ⟨W, hW⟩ := ZF.exists_cartesianProduct hZF I ω ω
  obtain ⟨F, hF⟩ := union_bound_l I hZFC hA hU hc hW
  have hωc := ZF.omega_cardinal_l I hZF hω
  obtain ⟨J, hJ⟩ := ZF.cartesianSquare_cardinalLessOrEqual_of_selfMultiplication hZF I
    ⟨hωc, Structure.Equinumerous.refl hZF I ω⟩ hW (ZF.omega_selfMultiplication hZF I hω hωc)
  exact ZF.exists_compositionInjection hZF I hF hJ

/-- 可定义小纤维覆盖的基数界：纤维集合及其编号函数自动由分离与替换构造。 -/
theorem cover_bound_l (hZFC : M.Models ZFC) {n} (φ : BinarySchema n) (ρ : Env M n)
    {J X κ W} (hJ : M.CardinalLessOrEqual I J κ) (hW : M.IsCartesianProduct I W κ κ)
    (hc : ∀ i, M.mem i J → ∀ D, (∀ x, M.mem x D ↔ M.mem x X ∧ φ.denote ρ i x) →
      M.CardinalLessOrEqual I D κ)
    (ht : ∀ x, M.mem x X → ∃ i, M.mem i J ∧ φ.denote ρ i x) : M.CardinalLessOrEqual I X W := by
  let hZF := models_zf_l hZFC
  obtain ⟨P, _, f, hf, he⟩ := ZF.fiber_function_l I hZF φ ρ J X
  obtain ⟨A, hA⟩ := ZF.exists_range_of_setFunction hZF I hf.1 hf.2.1
  have hfun : M.IsSetFunctionFromTo I f J A := ⟨hf.1, hf.2.1, fun i hi => by
    obtain ⟨D, _, hiD⟩ := hf.2.2 i hi
    exact ⟨D, (hA D).mpr ⟨i, hiD⟩, hiD⟩⟩
  obtain ⟨g, hg⟩ := surjection_bound_l I hZFC hfun (fun D hD => by
    obtain ⟨i, hiD⟩ := (hA D).mp hD
    exact ⟨i, hf.input_mem_of_pairMember hiD, hiD⟩)
  obtain ⟨j, hj⟩ := hJ
  have hs {i D} (hi : M.PairMember I i D f) :
      ∀ x, M.mem x D ↔ M.mem x X ∧ φ.denote ρ i x := ((he i D).mp hi).2
  refine union_bound_l I hZFC (ZF.exists_compositionInjection hZF I hg hj) ?_ (fun D hD => ?_) hW
  · intro x
    constructor
    · intro hx
      obtain ⟨i, hi, hix⟩ := ht x hx
      obtain ⟨D, _, hiD⟩ := hf.2.2 i hi
      exact ⟨D, (hA D).mpr ⟨i, hiD⟩, (hs hiD x).mpr ⟨hx, hix⟩⟩
    · rintro ⟨D, hD, hx⟩
      obtain ⟨i, hiD⟩ := (hA D).mp hD
      exact ((hs hiD x).mp hx).1
  · obtain ⟨i, hiD⟩ := (hA D).mp hD
    exact hc i (hf.input_mem_of_pairMember hiD) D (hs hiD)

theorem countable_cover_l (hZFC : M.Models ZFC) {ω} (hω : M.IsOmega ω)
    {n} (φ : BinarySchema n) (ρ : Env M n) {J X}
    (hJ : M.CardinalLessOrEqual I J ω)
    (hc : ∀ i, M.mem i J → ∀ D, (∀ x, M.mem x D ↔ M.mem x X ∧ φ.denote ρ i x) →
      M.CardinalLessOrEqual I D ω)
    (ht : ∀ x, M.mem x X → ∃ i, M.mem i J ∧ φ.denote ρ i x) : M.CardinalLessOrEqual I X ω := by
  let hZF := models_zf_l hZFC
  obtain ⟨W, hW⟩ := ZF.exists_cartesianProduct hZF I ω ω
  obtain ⟨F, hF⟩ := cover_bound_l I hZFC φ ρ hJ hW hc ht
  obtain ⟨G, hG⟩ := ZF.exists_identityBijection hZF I ω
  obtain ⟨H, hH⟩ := ZF.countable_product_l I hZF hω ⟨G, hG.1⟩ ⟨G, hG.1⟩ hW
  exact ZF.exists_compositionInjection hZF I hF hH

end YesMetaZFC.SetTheory.ZFC
