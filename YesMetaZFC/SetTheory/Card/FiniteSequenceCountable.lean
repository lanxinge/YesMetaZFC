import YesMetaZFC.SetTheory.Card.FiniteSequenceNumbering

/-! # ZF 中可数字母表的全部有限序列仍可数

一条内部 ω 递归统一给出每层单射，最终编号为 (长度,层内编号) 的自然数配对。
没有逐层任选枚举，也没有把可数选择藏在可数并定理中。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 全部内部有限序列具有一个模型内自然数编号；只用原 ZF。 -/
theorem countable_fseq_l (hZF : M.Models ZF) {ω X S} (hω : M.IsOmega ω)
    (hX : M.CardinalLessOrEqual I X ω) (hS : Fseq_space_d I ω X S) : M.CardinalLessOrEqual I S ω := by
  obtain ⟨Q, hQ⟩ := hX
  obtain ⟨W, hW⟩ := exists_cartesianProduct hZF I ω ω
  obtain ⟨T, hT⟩ := exists_identityBijection hZF I ω
  obtain ⟨J, hJ⟩ := countable_product_l I hZF hω ⟨T, hT.1⟩ ⟨T, hT.1⟩ hW
  obtain ⟨H, hH⟩ := fseq_recursion_l I hZF hω X S Q J
  have levels := fseq_numbering_l I hZF hω hS hW hQ hJ hH
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push H).push J
  let φ : BinarySchema 4 := {
    body := .existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 3) (.bound 9)) (.conj
      (Formula.isFunctionFromTo 𝒞 (.bound 5) (.bound 3) (.bound 8)) (.conj
      (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 2) (.bound 7)) (.conj
      (Formula.orderedPairMem 𝒞 (.bound 5) (.bound 1) (.bound 2)) (.conj
      (𝒞.code .newest (.bound 3) (.bound 1))
      (Formula.orderedPairMem 𝒞 .newest (.bound 4) (.bound 6)))))))))) }
  have hφ F z : φ.denote ρ F z ↔ ∃ n K t p,
      M.mem n ω ∧ M.IsSetFunctionFromTo I F n X ∧ M.PairMember I n K H ∧
        M.PairMember I F t K ∧ I.Codes p n t ∧ M.PairMember I p z J := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_isFunctionFromTo_iff I hZF.1,
      Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff]
    rfl
  apply exists_setInjectionFromTo_of_denote hZF I φ ρ
  · intro F hF
    obtain ⟨n, hn, hf⟩ := (hS F).mp hF
    obtain ⟨K, hK⟩ := (hH.1.2.2 n).mp hn
    obtain ⟨A, hA, hk⟩ := levels n hn K hK
    obtain ⟨t, ht, hFt⟩ := hk.1.2.2 F ((hA F).mpr hf)
    obtain ⟨p, hp⟩ := I.total n t
    obtain ⟨z, _, hz⟩ := hJ.1.2.2 p ((hW p).mpr ⟨n, hn, t, ht, hp⟩)
    exact ⟨z, (hφ F z).mpr ⟨n, K, t, p, hn, hf, hK, hFt, hp, hz⟩⟩
  · intro F _ z w hz hw
    obtain ⟨n, K, t, p, hn, hf, hK, hFt, hp, hz⟩ := (hφ F z).mp hz
    obtain ⟨m, L, s, q, _, hg, hL, hFs, hq, hw⟩ := (hφ F w).mp hw
    have he := hf.2.1.eq hZF.1 hg.2.1
    subst m
    have he := hH.1.2.1.2 n K L hK hL
    subst L
    obtain ⟨A, _, hk⟩ := levels n hn K hK
    have he := hk.1.1.2 F t s hFt hFs
    subst s
    have he := I.unique hp hq
    subst q
    exact hJ.1.1.2 p z w hz hw
  · intro F z _ hz
    obtain ⟨_, _, _, _, _, _, _, _, _, hz⟩ := (hφ F z).mp hz
    exact hJ.1.output_mem_of_pairMember hz
  · intro F G z _ _ hz hw
    obtain ⟨n, K, t, p, hn, _, hK, hFt, hp, hz⟩ := (hφ F z).mp hz
    obtain ⟨m, L, s, q, _, _, hL, hGs, hq, hw⟩ := (hφ G z).mp hw
    have he := hJ.2 p q z hz hw
    subst q
    obtain ⟨he, hf⟩ := I.injective hp hq
    subst m
    subst s
    have he := hH.1.2.1.2 n K L hK hL
    subst L
    obtain ⟨A, _, hk⟩ := levels n hn K hK
    exact hk.2 F G t hFt hGs

/-- 从一个内部可数字母表直接装配有限序列全集及其内部单射。 -/
theorem fseq_countable_space_l (hZF : M.Models ZF) {ω X} (hω : M.IsOmega ω)
    (hX : M.CardinalLessOrEqual I X ω) : ∃ S, Fseq_space_d I ω X S ∧ M.CardinalLessOrEqual I S ω := by
  obtain ⟨S, hS⟩ := fseq_space_exists_l I hZF hω X
  exact ⟨S, hS, countable_fseq_l I hZF hω hX hS⟩

end YesMetaZFC.SetTheory.ZF
