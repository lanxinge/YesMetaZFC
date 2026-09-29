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

def not_ch_sentence_l (𝒞 : OrderedPairConvention) : Sentence :=
  ⟨.neg (ch_m 𝒞), by simp only [Definitional.Formula.FreeClosed]; exact ch_m_freeClosed 𝒞⟩

def ZFC_not_CH (𝒞 : OrderedPairConvention) : Theory := fun s => ZFC s ∨ s = not_ch_sentence_l 𝒞

theorem ch_sat_l {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    (hE : Extensional M) (ρ : Env M 0) : Formula.satisfies ρ (ch_m 𝒞) ↔ CH_d I := by
  simp only [ch_m, CH_d, hartogs_m, Structure.IsHartogsNumber, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isPowerSet_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_cardinalLessOrEqual_iff I hE]
  rfl

namespace ZF
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 序数的所有真初段可嵌入 X，而本身不能时，它恰为 X 的 Hartogs 序数。 -/
theorem hartogs_bound_l (hZF : M.Models ZF) {κ X} (hκ : M.IsOrdinal κ)
    (hs : ∀ α, M.mem α κ → M.CardinalLessOrEqual I α X)
    (hn : ¬ M.CardinalLessOrEqual I κ X) : M.IsHartogsNumber I κ X := by
  refine ⟨hκ, fun α hα => ⟨hs α, fun hαX => ?_⟩⟩
  rcases hα.trichotomy hZF.1 hκ (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) α κ) with he | hακ | hκα
  · exact False.elim (hn (hZF.1.eq_of_same_members α κ he ▸ hαX))
  · exact hακ
  · obtain ⟨F, hF⟩ := ZF.exists_inclusionInjection hZF I (hα.transitive κ hκα)
    obtain ⟨G, hG⟩ := hαX
    exact False.elim (hn (ZF.exists_compositionInjection hZF I hF hG))

/-- 超过 ω₁ 的可区分实数族直接否定原 CH 句子的语义。 -/
theorem not_ch_l (hZF : M.Models ZF) {ω P κ μ} (hω : M.IsOmega ω) (hP : M.IsPowerSetOf P ω)
    (hκ : M.IsHartogsNumber I κ ω) (hμP : M.CardinalLessOrEqual I μ P)
    (hn : ¬ M.CardinalLessOrEqual I μ κ) : ¬ CH_d I := by
  rintro ⟨ω', P', κ', hω', hP', hκ', hCH⟩
  have hωeq : ω' = ω := hZF.1.eq_of_same_members ω' ω (fun x =>
    ⟨hω'.2 ω hω.1 x, hω.2 ω' hω'.1 x⟩)
  subst ω'
  have hPeq := hP'.eq hZF.1 hP
  subst P'
  have hκeq : κ' = κ := hZF.1.eq_of_same_members κ' κ (fun α =>
    ⟨fun h => (hκ.2 α (hκ'.1.mem h)).mpr ((hκ'.2 α (hκ'.1.mem h)).mp h),
      fun h => (hκ'.2 α (hκ.1.mem h)).mpr ((hκ.2 α (hκ.1.mem h)).mp h)⟩)
  subst κ'
  obtain ⟨F, hF⟩ := hμP
  obtain ⟨G, hG⟩ := hCH
  exact hn (ZF.exists_compositionInjection hZF I hF hG)

end ZF

namespace ZFC
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

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
  exact ⟨ω, P, κ, hω, hP, ZF.hartogs_bound_l I hZF hκ hs hn, hb⟩

end ZFC
end YesMetaZFC.SetTheory
