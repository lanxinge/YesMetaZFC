import YesMetaZFC.SetTheory.Rank
import YesMetaZFC.SetTheory.Card.OrdinalImage
import YesMetaZFC.SetTheory.Card.CantorBernstein

/-! # 传递集合的秩像与遗传大小的层级界

传递集合的秩像没有缺口，故本身是序数。秩函数的实际满射随后把遗传基数界
转化为累积层级界；最小原像编号使该论证只需 ZF。
-/

namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 传递集合的实际秩图满射到一个内部序数。 -/
theorem rk_image_l (hZF : M.Models ZF) {T} (hT : M.TransitiveSet T) :
    ∃ α F, M.IsOrdinal α ∧ M.IsSetFunctionFromTo I F T α ∧ M.IsSetSurjectiveOnto I F T α ∧
      ∀ x β, M.PairMember I x β F ↔ M.mem x T ∧ Rk_d I x β := by
  classical
  obtain ⟨γ, hγ⟩ := rk_exists_l I hZF T
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => T⟩
  let φ : BinarySchema 0 := { body := rk_m (𝒞 := 𝒞) (.bound 1) .newest }
  have hφ x β : φ.denote ρ x β ↔ Rk_d I x β := rk_sat_l I hZF.1 _ _ _
  obtain ⟨F, hF, hf'⟩ := exists_setFunctionFromTo_of_denote hZF I φ ρ (source := T) (target := γ)
    (fun x _ => (rk_exists_l I hZF x).elim fun β hβ => ⟨β, (hφ x β).mpr hβ⟩)
    (fun x _ α β ha hb => rk_unique_l I hZF.1 ((hφ x α).mp ha) ((hφ x β).mp hb))
    (fun x β hx hβ => rk_member_l I hZF ((hφ x β).mp hβ) hγ hx)
  have hf x β : M.PairMember I x β F ↔ M.mem x T ∧ Rk_d I x β :=
    (hf' x β).trans (and_congr_right fun _ => hφ x β)
  obtain ⟨A, hA⟩ := exists_range_of_setFunction hZF I hF.1 hF.2.1
  have hAγ : M.MemberSubset A γ := fun α ha => (hA α).mp ha |>.elim fun x hx => hF.output_mem_of_pairMember hx
  have hAtrans : M.TransitiveSet A := by
    intro α hα β hβα
    have hβo := (hγ.ordinal I).mem (hAγ α hα) |>.mem hβα
    let η : Env M 1 := ⟨fun _ => β, fun _ => β⟩
    let ψ : UnarySchema 1 := { body := .disj (Formula.extensionalEq .newest (.bound 1)) (.mem (.bound 1) .newest) }
    obtain ⟨D, hD'⟩ := separation_exists_d hZF ψ η A
    have hD δ : M.mem δ D ↔ M.mem δ A ∧ (δ = β ∨ M.mem β δ) := by
      rw [hD' δ]
      simp only [ψ, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
        Formula.satisfies_mem_iff]
      rfl
    obtain ⟨δ, hδ, hMin⟩ := (hγ.ordinal I).wellOrder.least D
      (fun δ hδ => hAγ δ ((hD δ).mp hδ).1) ⟨α, (hD α).mpr ⟨hα, Or.inr hβα⟩⟩
    obtain ⟨hδA, he | hβδ⟩ := (hD δ).mp hδ
    · exact he ▸ hδA
    · obtain ⟨x, hfx⟩ := (hA δ).mp hδA
      obtain ⟨hxT, hrx⟩ := (hf x δ).mp hfx
      obtain ⟨V, hV⟩ := v_exists_l I hZF hβo
      have hn : ¬ M.MemberSubset x V := by
        intro hxV
        obtain ⟨_, _, _, h⟩ := hrx
        exact KP.mem_irrefl_d (modelsKP hZF) β (h β V hV hxV β hβδ)
      obtain ⟨y, hyx, hyV⟩ : ∃ y, M.mem y x ∧ ¬ M.mem y V := by
        apply Classical.byContradiction
        intro h
        exact hn (fun y hy => Classical.byContradiction (fun hny => h ⟨y, hy, hny⟩))
      obtain ⟨ε, _, hyε⟩ := hF.2.2 y (hT x hxT y hyx)
      have hry := ((hf y ε).mp hyε).2
      have hεδ := rk_member_l I hZF hry hrx hyx
      have heD : M.mem ε D := by
        refine (hD ε).mpr ⟨(hA ε).mpr ⟨y, hyε⟩, ?_⟩
        rcases Structure.IsOrdinal.trichotomy hZF.1 (hry.ordinal I) hβo
            (KP.difference_exists_d (modelsKP hZF)) (KP.intersection_exists_d (modelsKP hZF) ε β) with he | hεβ | hβε
        · exact Or.inl (hZF.1.eq_of_same_members ε β he)
        · exact (hyV ((rk_mem_l I hZF hry hV).mpr hεβ)).elim
        · exact Or.inr hβε
      rcases hMin ε heD with he | hδε
      · have he := hZF.1.eq_of_same_members δ ε he
        exact (KP.mem_irrefl_d (modelsKP hZF) ε (he ▸ hεδ)).elim
      · exact (KP.mem_irrefl_d (modelsKP hZF) δ ((hrx.ordinal I).transitive ε hεδ δ hδε)).elim
  refine ⟨A, F, (hγ.ordinal I).of_transitive_subset hAγ hAtrans, ⟨hF.1, hF.2.1, fun x hx => ?_⟩,
    fun α hα => (hA α).mp hα |>.elim fun x hx => ⟨x, hF.input_mem_of_pairMember hx, hx⟩, hf⟩
  obtain ⟨α, _, hxα⟩ := hF.2.2 x hx
  exact ⟨α, (hA α).mpr ⟨x, hxα⟩, hxα⟩

/-- 小于基数 κ 的传递集合位于 Vκ；内部满射的像界不使用选择公理。 -/
theorem rk_transitive_bound_l (hZF : M.Models ZF) {T κ μ V}
    (hT : M.TransitiveSet T) (hκ : M.IsCardinal I κ) (hμ : M.mem μ κ)
    (ht : M.CardinalLessOrEqual I T μ) (hV : V_d I κ V) : M.MemberSubset T V := by
  obtain ⟨α, F, hα, hF, hs, hf⟩ := rk_image_l I hZF hT
  obtain ⟨G, hG⟩ := ordinal_image_bound_l I hZF (hκ.1.mem hμ) ht hF hs
  have not_le (hκα : M.MemberSubset κ α) : False := by
    obtain ⟨J, hJ⟩ := exists_inclusionInjection hZF I hκα
    have hκμ := exists_compositionInjection hZF I hJ hG
    have hμκ := exists_inclusionInjection hZF I (hκ.1.transitive.memberSubset hμ)
    exact hκ.2 μ hμ (equinumerous_of_cardinalLessOrEqual hZF I hμκ hκμ)
  have hακ : M.mem α κ := by
    rcases Structure.IsOrdinal.trichotomy hZF.1 hα hκ.1
        (KP.difference_exists_d (modelsKP hZF)) (KP.intersection_exists_d (modelsKP hZF) α κ) with he | hακ | hκα
    · exact (not_le (fun x hx => (he x).mpr hx)).elim
    · exact hακ
    · exact (not_le (hα.transitive.memberSubset hκα)).elim
  intro x hx
  obtain ⟨β, hβα, hxβ⟩ := hF.2.2 x hx
  exact (rk_mem_l I hZF ((hf x β).mp hxβ).2 hV).mpr (hκ.1.transitive α hακ β hβα)

end YesMetaZFC.SetTheory.ZF
