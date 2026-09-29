import YesMetaZFC.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.Card.Cantor
import YesMetaZFC.SetTheory.Card.CantorBernstein

/-! # 连续统假设的原语言公式与基数判据

CH 表达为 P(ω) 的基数不超过 ω 的 Hartogs 序数；Cantor 定理保证该上界恰为
第一不可数基数。公式保留原有序对约定参数，可直接使用平坦对或 Kuratowski 对实例。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u

def CH_d {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) : Prop :=
  ∃ ω P κ, M.IsOmega ω ∧ M.IsPowerSetOf P ω ∧ M.IsHartogsNumber I κ ω ∧ M.CardinalLessOrEqual I P κ

def hartogs_m (𝒞 : OrderedPairConvention) {n} (κ ω : Term n) : Formula 1 n :=
  .conj (Formula.isOrdinal κ) (.forallE (.imp (Formula.isOrdinal .newest)
    (.iff (.mem .newest κ.weaken) (Formula.cardinalLessOrEqual 𝒞 .newest ω.weaken))))
derive_free_closed hartogs_m

def ch_m (𝒞 : OrderedPairConvention) : Formula 1 0 := .existsE (.existsE (.existsE
  (.conj (Formula.isOmega (.bound 2)) (.conj (Formula.isPowerSet (.bound 1) (.bound 2))
    (.conj (hartogs_m 𝒞 .newest (.bound 2)) (Formula.cardinalLessOrEqual 𝒞 (.bound 1) .newest))))))
derive_free_closed ch_m

def ch_sentence_l (𝒞 : OrderedPairConvention) : Sentence := ⟨ch_m 𝒞, ch_m_freeClosed 𝒞⟩

def ZFC_CH (𝒞 : OrderedPairConvention) : Theory := fun s => ZFC s ∨ s = ch_sentence_l 𝒞

theorem ch_sat_l {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    (hE : Extensional M) (ρ : Env M 0) : Formula.satisfies ρ (ch_m 𝒞) ↔ CH_d I := by
  simp only [ch_m, CH_d, hartogs_m, Structure.IsHartogsNumber, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isPowerSet_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_cardinalLessOrEqual_iff I hE]
  rfl

namespace ZFC
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 内部满射的纤维选择给出反向基数不等式。 -/
theorem surjection_bound_l (hZFC : M.Models ZFC) {F X Y}
    (hf : M.IsSetFunctionFromTo I F X Y) (hs : M.IsSetSurjectiveOnto I F X Y) : M.CardinalLessOrEqual I Y X := by
  let φ : BinarySchema 1 := { body := Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 2) }
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  have hφ y x : φ.denote ρ y x ↔ M.PairMember I x y F :=
    Formula.satisfies_orderedPairMem_iff I ((ρ.push y).push x) .newest (.bound 1) (.bound 2)
  obtain ⟨G, hG, hg⟩ := uniformize_formula_l I hZFC φ ρ (X := Y) (Y := X) (by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hs y hy
    exact ⟨x, hx, (hφ y x).mpr hxy⟩)
  exact ⟨G, hG, fun y z x hy hz => hf.1.2 x y z ((hφ y x).mp (hg y x hy)) ((hφ z x).mp (hg z x hz))⟩

/-- 一个序数界的所有真初段可数且足以覆盖实数时，该界自动就是 ω₁。 -/
theorem continuum_bound_l (hZFC : M.Models ZFC) {ω P κ} (hω : M.IsOmega ω)
    (hP : M.IsPowerSetOf P ω) (hκ : M.IsOrdinal κ)
    (hs : ∀ α, M.mem α κ → M.CardinalLessOrEqual I α ω) (hb : M.CardinalLessOrEqual I P κ) : CH_d I := by
  let hZF := models_zf_l hZFC
  have hn : ¬ M.CardinalLessOrEqual I κ ω := by
    rintro ⟨G, hG⟩
    obtain ⟨F, hF⟩ := hb
    have hPω := ZF.exists_compositionInjection hZF I hF hG
    have hc := ZF.cardinalLess_powerSet hZF I hP
    exact hc.2 (ZF.equinumerous_of_cardinalLessOrEqual hZF I hc.1 hPω)
  refine ⟨ω, P, κ, hω, hP, ⟨hκ, fun α hα => ⟨hs α, fun hαω => ?_⟩⟩, hb⟩
  rcases hα.trichotomy hZF.1 hκ (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) α κ) with he | hακ | hκα
  · exact False.elim (hn (hZF.1.eq_of_same_members α κ he ▸ hαω))
  · exact hακ
  · obtain ⟨F, hF⟩ := ZF.exists_inclusionInjection hZF I (hα.transitive κ hκα)
    obtain ⟨G, hG⟩ := hαω
    exact False.elim (hn (ZF.exists_compositionInjection hZF I hF hG))

end ZFC
end YesMetaZFC.SetTheory
