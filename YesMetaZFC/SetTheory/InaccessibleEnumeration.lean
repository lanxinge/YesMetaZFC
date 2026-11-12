import YesMetaZFC.SetTheory.InaccessibleHierarchy

/-! # 不可达秩段的实际等势枚举

Vκ 是 κ 个严格小秩层之并，故 |Vκ|≤κ；反向使用 κ⊆Vκ。
Cantor–Bernstein 给出实际 κ→Vκ 双射，供序数限制到整个秩段的恢复使用。
-/
namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem inaccessible_enumeration_l (hZFC : M.Models ZFC) {ω κ B : M.Domain}
    (hω : M.IsOmega ω) (hωκ : M.mem ω κ) (hr : M.IsRegularCardinal I κ)
    (hs : M.IsStrongLimitCardinal I κ) (hB : V_d I κ B) : ∃ f, M.IsSetBijectionFromTo I f κ B := by
  let hZF := models_zf_l hZFC
  obtain ⟨F, hf, step⟩ := hB
  have hB : V_d I κ B := ⟨F, hf, step⟩
  obtain ⟨A, hA⟩ := ZF.exists_range_of_setFunction hZF I hf.1.2.1 hf.1.2.2
  have fn : M.IsSetFunctionFromTo I F κ A := ⟨hf.1.2.1, hf.1.2.2, fun α hα =>
    ((hf.1.2.2 α).mp hα).imp fun V hv => ⟨(hA V).mpr ⟨α, hv⟩, hv⟩⟩
  have onto : M.IsSetSurjectiveOnto I F κ A := fun V hv => ((hA V).mp hv).imp fun α ha =>
    ⟨fn.input_mem_of_pairMember ha, ha⟩
  have history α V (hαV : M.PairMember I α V F) := hf.recursionValue_of_pairMember (fn.input_mem_of_pairMember hαV) hαV
  have union : M.IsUnionOf B A := fun x => ⟨fun hx => by
    obtain ⟨α, V, hα, hV, hxV⟩ := (ZF.v_limit_mem_l I hZF hB hr.isLimitOrdinal.2.2 x).mp hx
    obtain ⟨W, hW, hαW⟩ := fn.2.2 α hα
    exact ⟨W, hW, ZF.v_unique_l I hZF hV (history α W hαW) ▸ hxV⟩,
    fun ⟨V, hvA, hxV⟩ => by
      obtain ⟨α, hα, hαV⟩ := onto V hvA
      exact v_transitive_l I hB V (ZF.v_mem_l I hZF (history α V hαV) hB hα) x hxV⟩
  have hAκ := ZF.ordinal_image_bound_l I hZF hr.isCardinal.1
    (ZF.exists_inclusionInjection hZF I (fun _ h => h)) fn onto
  have bound : M.CardinalLessOrEqual I B κ := infinite_union_l I hZFC hω
    ⟨hr.isCardinal, ZF.exists_inclusionInjection hZF I (hr.isCardinal.1.transitive ω hωκ)⟩ hAκ union (fun V hv => by
      obtain ⟨α, hα, hαV⟩ := onto V hv
      obtain ⟨μ, hμ, g, hg⟩ := inaccessible_level_small_l I hZFC hω hωκ hr hs hα (history α V hαV)
      obtain ⟨r, hr'⟩ := ZF.exists_inclusionInjection hZF I (hr.isCardinal.1.transitive μ hμ)
      exact ZF.exists_compositionInjection hZF I hg hr')
  exact ZF.equinumerous_of_cardinalLessOrEqual hZF I
    (ZF.exists_inclusionInjection hZF I (ZF.v_ordinal_subset_l I hZF hB)) bound

end YesMetaZFC.SetTheory.ZFC
