import YesMetaZFC.SetTheory.Card.SmallBound
import YesMetaZFC.SetTheory.Card.CountableUnion
import YesMetaZFC.SetTheory.Card.Properties.Basic
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # 正则基数以下的小并

先在模型内统一选择各成员的序数大小界，再由正则性给这些界取公共上界。
因此少于 κ 个、各自大小小于 κ 的集合之并仍有一个严格低于 κ 的实际单射界。
-/

namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem small_union_l (hZFC : M.Models ZFC) {ω κ A μ U} (hω : M.IsOmega ω)
    (hκ : M.IsRegularCardinal I κ) (hωκ : M.mem ω κ) (hμ : M.mem μ κ)
    (hA : M.CardinalLessOrEqual I A μ) (hU : M.IsUnionOf U A)
    (ha : ∀ a, M.mem a A → ∃ ξ, M.mem ξ κ ∧ M.CardinalLessOrEqual I a ξ) :
    ∃ ν, M.mem ν κ ∧ M.CardinalLessOrEqual I U ν := by
  have hZF := models_zf_l hZFC
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => κ⟩
  let φ : BinarySchema 0 := { body := Formula.cardinalLessOrEqual 𝒞 (.bound 1) .newest }
  have hφ a ξ : φ.denote ρ a ξ ↔ M.CardinalLessOrEqual I a ξ :=
    Formula.satisfies_cardinalLessOrEqual_iff I hZF.1 _ _ _
  obtain ⟨F, hF, hf⟩ := uniformize_formula_l I hZFC φ ρ (X := A) (Y := κ) (by
    intro a haA
    obtain ⟨ξ, hξ, haξ⟩ := ha a haA
    exact ⟨ξ, hξ, (hφ a ξ).mpr haξ⟩)
  obtain ⟨R, hR⟩ := ZF.exists_range_of_setFunction hZF I hF.1 hF.2.1
  have hFR : M.IsSetFunctionFromTo I F A R := ⟨hF.1, hF.2.1, fun a ha => by
    obtain ⟨ξ, _, hξ⟩ := hF.2.2 a ha
    exact ⟨ξ, (hR ξ).mpr ⟨a, hξ⟩, hξ⟩⟩
  have hRμ := ZF.ordinal_image_bound_l I hZF (hκ.isCardinal.1.mem hμ) hA hFR
    (fun ξ hξ => (hR ξ).mp hξ |>.elim fun a ha => ⟨a, hF.input_mem_of_pairMember ha, ha⟩)
  have hRκ : M.MemberSubset R κ := fun ξ hξ => (hR ξ).mp hξ |>.elim fun a ha => hF.output_mem_of_pairMember ha
  obtain ⟨γ, hγ, hRγ⟩ := (ZF.small_subset_bounded_l I hZF hκ hRκ hμ hRμ).exists_bound
  obtain ⟨ν, hνκ, hν, hμν, hγν⟩ := ZF.common_cardinal_l I hZF hκ.isCardinal.1 hωκ hμ hγ
  obtain ⟨G, hG⟩ := hA
  obtain ⟨J, hJ⟩ := hμν
  have hAν := ZF.exists_compositionInjection hZF I hG hJ
  obtain ⟨W, hW⟩ := ZF.exists_cartesianProduct hZF I ν ν
  obtain ⟨K, hK⟩ := union_bound_l I hZFC hAν hU (fun a haA => by
    obtain ⟨ξ, _, haξ⟩ := hF.2.2 a haA
    have hξγ : M.MemberSubset ξ γ := by
      rcases hRγ ξ ((hR ξ).mpr ⟨a, haξ⟩) with he | hξγ
      · exact he ▸ (fun _ h => h)
      · exact (hκ.isCardinal.1.mem hγ).transitive.memberSubset hξγ
    obtain ⟨P, hP⟩ := (hφ a ξ).mp (hf a ξ haξ)
    obtain ⟨Q, hQ⟩ := ZF.exists_inclusionInjection hZF I hξγ
    obtain ⟨D, hD⟩ := hγν
    obtain ⟨E, hE⟩ := ZF.exists_compositionInjection hZF I hP hQ
    exact ZF.exists_compositionInjection hZF I hE hD) hW
  obtain ⟨L, hL⟩ := ZF.cartesianSquare_cardinalLessOrEqual_of_selfMultiplication hZF I
    ⟨hν.1, Structure.Equinumerous.refl hZF I ν⟩ hW
    (ZF.infiniteCardinal_selfMultiplication hZF I hω (ZF.omega_cardinal_l I hZF hω) hν)
  exact ⟨ν, hνκ, ZF.exists_compositionInjection hZF I hK hL⟩

end YesMetaZFC.SetTheory.ZFC
