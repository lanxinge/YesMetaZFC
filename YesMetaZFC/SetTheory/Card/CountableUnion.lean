import YesMetaZFC.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.Card.Omega
import YesMetaZFC.SetTheory.Card.Aleph.Multiplication

/-! # 模型内部的可数并

先在模型内统一选择各成员到 ω 的单射，再把并集单射到 ω×ω，最后用已有 Cantor
配对定理压回 ω。成员的枚举与单射见证均为内部集合编码函数。
-/

namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem countable_union_l (hZFC : M.Models ZFC) {ω A U f : M.Domain} (hω : M.IsOmega ω)
    (hf : M.IsSetFunctionFromTo I f ω A) (hs : M.IsSetSurjectiveOnto I f ω A)
    (hU : M.IsUnionOf U A) (hc : ∀ T, M.mem T A → M.CardinalLessOrEqual I T ω) :
    M.CardinalLessOrEqual I U ω := by
  let hZF := models_zf_l hZFC
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I U ω
  obtain ⟨K, hK⟩ := ZF.exists_powerSet hZF P
  let φ : BinarySchema 1 := { body := Formula.isInjectionFromTo 𝒞 .newest (.bound 1) (.bound 2) }
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  have hφ T j : φ.denote ρ T j ↔ M.IsSetInjectionFromTo I j T ω :=
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
  have hg {T j} (h : M.PairMember I T j G) : M.IsSetInjectionFromTo I j T ω := (hφ T j).mp (hg T j h)
  obtain ⟨W, hW⟩ := ZF.exists_cartesianProduct hZF I ω ω
  let δ : Env M 2 := (⟨fun _ => f, fun _ => f⟩ : Env M 1).push G
  let ψ : BinarySchema 2 := {
    body := .existsE (.existsE (.existsE (.existsE (.conj (𝒞.code (.bound 4) (.bound 3) (.bound 2))
      (.conj (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) (.bound 7))
        (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 6))
          (Formula.orderedPairMem 𝒞 (.bound 5) (.bound 2) .newest))))))) }
  have hψ x q : ψ.denote δ x q ↔ ∃ n k T j,
      I.Codes q n k ∧ M.PairMember I n T f ∧ M.PairMember I T j G ∧ M.PairMember I x k j := by
    simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨H, hH, hh⟩ := uniformize_formula_l I hZFC ψ δ (X := U) (Y := W) (by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := (hU x).mp hx
    obtain ⟨n, hn, hnT⟩ := hs T hT
    obtain ⟨j, _, hTj⟩ := hG.2.2 T hT
    obtain ⟨k, hk, hxk⟩ := (hg hTj).1.2.2 x hxT
    obtain ⟨q, hq⟩ := I.total n k
    exact ⟨q, (hW q).mpr ⟨n, hn, k, hk, hq⟩, (hψ x q).mpr ⟨n, k, T, j, hq, hnT, hTj, hxk⟩⟩)
  have hinj : M.IsSetInjectionFromTo I H U W := by
    refine ⟨hH, fun x y q hx hy => ?_⟩
    obtain ⟨n, k, T, j, hq, hnT, hTj, hxj⟩ := (hψ x q).mp (hh x q hx)
    obtain ⟨m, l, V, e, hq', hmV, hVe, hye⟩ := (hψ y q).mp (hh y q hy)
    obtain ⟨rfl, rfl⟩ := I.injective hq hq'
    have he := hf.1.2 n T V hnT hmV
    subst V
    have he := hG.1.2 T j e hTj hVe
    subst e
    exact (hg hTj).2 x y k hxj hye
  have hωc := ZF.omega_cardinal_l I hZF hω
  obtain ⟨J, hJ⟩ := ZF.cartesianSquare_cardinalLessOrEqual_of_selfMultiplication hZF I
    ⟨hωc, Structure.Equinumerous.refl hZF I ω⟩ hW (ZF.omega_selfMultiplication hZF I hω hωc)
  exact ZF.exists_compositionInjection hZF I hinj hJ

end YesMetaZFC.SetTheory.ZFC
