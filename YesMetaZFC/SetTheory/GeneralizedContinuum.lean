import YesMetaZFC.SetTheory.Continuum
import YesMetaZFC.SetTheory.Card.Aleph.Basic
import YesMetaZFC.SetTheory.Card.Cofinality.OrderType

/-! # 原对象语言的广义连续统假设

以 P(κ) 与 κ 的 Hartogs 数等势表达 2^κ=κ⁺。幂集的 Hartogs 上界已经足够：
该上界使幂集可良序，Cantor 排除更小序型，故从上界到等势只需 ZF。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u

def GCH_d {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) : Prop :=
  ∀ ω κ P θ, M.IsOmega ω → M.IsInfiniteCardinal I ω κ → M.IsPowerSetOf P κ →
    M.IsHartogsNumber I θ κ → M.Equinumerous I P θ

def gch_m (𝒞 : OrderedPairConvention) : Formula 1 0 :=
  .forallE (.forallE (.forallE (.forallE
    (.imp (Formula.isOmega (.bound 3)) (.imp (Formula.isInfiniteCardinal 𝒞 (.bound 3) (.bound 2))
      (.imp (Formula.isPowerSet (.bound 1) (.bound 2)) (.imp (hartogs_m 𝒞 .newest (.bound 2))
        (Formula.equinumerous 𝒞 (.bound 1) .newest))))))))
derive_free_closed gch_m

def gch_sentence_l (𝒞 : OrderedPairConvention) : Sentence := ⟨gch_m 𝒞, gch_m_freeClosed 𝒞⟩
def ZFC_GCH (𝒞 : OrderedPairConvention) : Theory := fun s => ZFC s ∨ s = gch_sentence_l 𝒞

theorem gch_sat_l {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    (hE : Extensional M) (ρ : Env M 0) : Formula.satisfies ρ (gch_m 𝒞) ↔ GCH_d I := by
  simp only [gch_m, GCH_d, hartogs_m, Structure.IsHartogsNumber, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_conj_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isOmega_iff, Formula.satisfies_isInfiniteCardinal_iff I hE,
    Formula.satisfies_isPowerSet_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_cardinalLessOrEqual_iff I hE, Formula.satisfies_equinumerous_iff I hE]
  rfl

/-- 幂集可嵌入源集的 Hartogs 数时，二者等势；无须选择公理。 -/
theorem ZF.hartogs_power_eq_l {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    (hZF : M.Models ZF) {X P θ} (hP : M.IsPowerSetOf P X) (hθ : M.IsHartogsNumber I θ X)
    (hb : M.CardinalLessOrEqual I P θ) : M.Equinumerous I P θ := by
  obtain ⟨F, hF⟩ := hb
  obtain ⟨S, hS⟩ := ZF.exists_range_of_setFunction hZF I hF.1.1 hF.1.2.1
  have hs : M.MemberSubset S θ := fun y hy => (hS y).mp hy |>.elim fun _ hx => hF.1.output_mem_of_pairMember hx
  have hf : M.IsSetBijectionFromTo I F P S := by
    refine ⟨⟨⟨hF.1.1, hF.1.2.1, fun x hx => ?_⟩, hF.2⟩, fun y hy => ?_⟩
    · obtain ⟨y, _, hxy⟩ := hF.1.2.2 x hx
      exact ⟨y, (hS y).mpr ⟨x, hxy⟩, hxy⟩
    · obtain ⟨x, hxy⟩ := (hS y).mp hy
      exact ⟨x, hF.1.input_mem_of_pairMember hxy, hxy⟩
  obtain ⟨R, a, _, ho, ht⟩ := ZF.exists_membershipWellOrderType_of_subsetOrdinal hZF I hθ.1 hs
  have ha := ht.isOrdinal hZF I ho
  have eq : M.Equinumerous I P a := (show M.Equinumerous I P S from ⟨F, hf⟩).trans hZF I (ht.equinumerous hZF I ho)
  rcases ha.trichotomy hZF.1 hθ.1 (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) a θ) with same | hal | hla
  · exact hZF.1.eq_of_same_members a θ same ▸ eq
  · obtain ⟨G, hG⟩ := eq
    obtain ⟨H, hH⟩ := (hθ.2 a ha).mp hal
    have hc := ZF.cardinalLess_powerSet hZF I hP
    exact (hc.2 (ZF.equinumerous_of_cardinalLessOrEqual hZF I hc.1
      (ZF.exists_compositionInjection hZF I hG.1 hH))).elim
  · obtain ⟨G, hG⟩ := ZF.exists_inclusionInjection hZF I (ha.transitive θ hla)
    obtain ⟨H, hH⟩ := eq.symm hZF I
    exact ZF.equinumerous_of_cardinalLessOrEqual hZF I ⟨F, hF⟩
      (ZF.exists_compositionInjection hZF I hG hH.1)

/-- 从 GCH 实例直接取得内部幂集、后继基数及二者间的双射图。 -/
theorem ZF.gch_power_l {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    (hZF : M.Models ZF) (hg : GCH_d I) {ω κ} (hω : M.IsOmega ω) (hκ : M.IsInfiniteCardinal I ω κ) :
    ∃ P θ F, M.IsPowerSetOf P κ ∧ M.IsHartogsNumber I θ κ ∧ M.IsSetBijectionFromTo I F P θ := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF κ
  obtain ⟨θ, hθ⟩ := ZF.exists_hartogsNumber hZF I κ
  obtain ⟨F, hF⟩ := hg ω κ P θ hω hκ hP hθ
  exact ⟨P, θ, F, hP, hθ, hF⟩

end YesMetaZFC.SetTheory
