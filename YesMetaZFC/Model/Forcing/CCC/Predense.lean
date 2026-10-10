import YesMetaZFC.Model.Forcing.CCC.Syntax
import YesMetaZFC.SetTheory.Choice

/-! # CCC 的可数预稠密子族

按内部序数枚举给定条件族。每个条件先加强到只可能遇到最早枚举位置；不同
最早位置的见证互不相容，CCC 因而把这些位置压为可数。无需另设极大反链公理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

/-- 每个实际条件族有可数子族，在所有能与原族相容的条件处预稠密。 -/
theorem ccc_predense_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {ω A}
    (hc : Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R z)
    (hA : ∀ p, M.mem p A → M.mem p B ∧ p ≠ z) : ∃ D,
    M.MemberSubset D A ∧ M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) D ω ∧
    ∀ p, M.mem p B → (∃ a, M.mem a A ∧ Cmp_d M B R z p a) →
      ∃ q, M.mem q D ∧ Cmp_d M B R z p q := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨κ, F, hκ, hF, honto⟩ := ZFC.ordinal_enum_l hZFC I A
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push F
  let φ : BinarySchema 4 := { body := .existsE (.conj (entry_m (.bound 2) .newest (.bound 3))
    (.conj (below_m (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest)
      (Formula.forallMem (.bound 2) (.forallE (.imp (entry_m (.bound 1) .newest (.bound 5))
        (.neg (cmp_m (.bound 8) (.bound 7) (.bound 6) (.bound 3) .newest))))))) }
  have hφ i r : φ.denote ρ i r ↔ ∃ p, Entry_d M i p F ∧ Below_d M B R z r p ∧
      ∀ j, M.mem j i → ∀ q, Entry_d M j q F → ¬ Cmp_d M B R z r q := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      entry_sat_l M hZF.1, below_sat_l M hZF.1, Formula.satisfies_forallMem_iff,
      Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_neg_iff, cmp_sat_l M hZF.1]
    rfl
  obtain ⟨J, hJ'⟩ := ZF.separation_exists_d hZF ({ body := .existsE φ.body } : UnarySchema 4) ρ κ
  have hJ i : M.mem i J ↔ M.mem i κ ∧ ∃ r, φ.denote ρ i r := by
    simpa only [UnarySchema.denote, Formula.satisfies_exists_iff, BinarySchema.denote] using hJ' i
  obtain ⟨G, hG, hg⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := J) (Y := B) (by
    intro i hi
    obtain ⟨r, hr⟩ := ((hJ i).mp hi).2
    exact ⟨r, ((hφ i r).mp hr).choose_spec.2.1.1, hr⟩)
  have spec {i r} (hr : Entry_d M i r G) := (hφ i r).mp (hg i r hr)
  have unique {i j r s} (hir : Entry_d M i r G) (hjs : Entry_d M j s G)
      (hrs : Cmp_d M B R z r s) : i = j := by
    obtain ⟨p, hip, hrp, hi⟩ := spec hir
    obtain ⟨q, hjq, hsq, hj⟩ := spec hjs
    have hit := ((hJ i).mp (hG.input_mem_of_pairMember hir)).1
    have hjt := ((hJ j).mp (hG.input_mem_of_pairMember hjs)).1
    obtain ⟨t, htr, hts⟩ := hrs
    rcases hκ.wellOrder.linear.compare i hit j hjt with he | hij | hji
    · exact hZF.1.eq_of_same_members i j he
    · exact False.elim (hj i hij p hip ⟨t, ⟨htr.1, htr.2.1, hts⟩,
        O.trans t r p htr.1 hrp.1 (hA p (hF.output_mem_of_pairMember hip)).1 htr.2.2 hrp.2.2⟩)
    · exact False.elim (hi j hji q hjq ⟨t, htr,
        O.trans t s q htr.1 hsq.1 (hA q (hF.output_mem_of_pairMember hjq)).1 hts hsq.2.2⟩)
  obtain ⟨X, hX⟩ := ZF.exists_range_of_setFunction hZF I hG.1 hG.2.1
  have hGX : M.IsSetInjectionFromTo I G J X := by
    refine ⟨⟨hG.1, hG.2.1, fun i hi => ?_⟩, fun i j r hi hj => ?_⟩
    · obtain ⟨r, _, hr⟩ := hG.2.2 i hi
      exact ⟨r, (hX r).mpr ⟨i, hr⟩, hr⟩
    · obtain ⟨_, _, hr, _⟩ := spec hi
      exact unique hi hj ⟨r, below_refl_l O hr.1 hr.2.1, O.refl r hr.1⟩
  have hanti : Antichain_d M B R z X := by
    refine ⟨fun r hr => ?_, fun r s hr hs hrs => ?_⟩
    · obtain ⟨i, hi⟩ := (hX r).mp hr
      obtain ⟨_, _, hr, _⟩ := spec hi
      exact ⟨hr.1, hr.2.1⟩
    · obtain ⟨i, hi⟩ := (hX r).mp hr
      obtain ⟨j, hj⟩ := (hX s).mp hs
      exact hG.1.2 i r s hi (unique hi hj hrs ▸ hj)
  obtain ⟨g, hgω⟩ := hc X hanti
  have hJω := ZF.exists_compositionInjection hZF I hGX hgω
  obtain ⟨K, hK⟩ := ZF.exists_restriction hZF I F J
  have hKF : M.IsSetFunction I K ∧ (∀ i, M.mem i J ↔ ∃ p, M.PairMember I i p K) := ⟨⟨hK.1, fun i p q hp hq =>
    hF.1.2 i p q ((hK.2 i p).mp hp).2 ((hK.2 i q).mp hq).2⟩, fun i => by
    constructor
    · intro hi
      obtain ⟨p, _, hp⟩ := hF.2.2 i ((hJ i).mp hi).1
      exact ⟨p, (hK.2 i p).mpr ⟨hi, hp⟩⟩
    · rintro ⟨p, hp⟩
      exact ((hK.2 i p).mp hp).1⟩
  obtain ⟨D, hD⟩ := ZF.exists_range_of_setFunction hZF I hKF.1 hKF.2
  have hKD : M.IsSetFunctionFromTo I K J D := ⟨hKF.1, hKF.2, fun i hi => by
    obtain ⟨p, hp⟩ := (hKF.2 i).mp hi
    exact ⟨p, (hD p).mpr ⟨i, hp⟩, hp⟩⟩
  obtain ⟨g, hg⟩ := ZFC.surjection_bound_l I hZFC hKD (fun p hp => by
    obtain ⟨i, hi⟩ := (hD p).mp hp
    exact ⟨i, ((hK.2 i p).mp hi).1, hi⟩)
  obtain ⟨f, hf⟩ := hJω
  refine ⟨D, fun p hp => (hD p).mp hp |>.elim fun i hi =>
    hF.output_mem_of_pairMember ((hK.2 i p).mp hi).2,
    ZF.exists_compositionInjection hZF I hg hf, fun p hp hpa => ?_⟩
  let η : Env M 5 := ρ.push p
  let ψ : UnarySchema 5 := { body := .existsE (.conj (entry_m (.bound 1) .newest (.bound 3))
    (cmp_m (.bound 6) (.bound 5) (.bound 4) (.bound 2) .newest)) }
  obtain ⟨T, hT'⟩ := ZF.separation_exists_d hZF ψ η κ
  have hT i : M.mem i T ↔ M.mem i κ ∧ ∃ q, Entry_d M i q F ∧ Cmp_d M B R z p q := by
    rw [hT' i]
    simp only [ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      entry_sat_l M hZF.1, cmp_sat_l M hZF.1]
    rfl
  obtain ⟨a, ha, hpa⟩ := hpa
  obtain ⟨i, hi, hia⟩ := honto a ha
  have hiT := (hT i).mpr ⟨hi, a, hia, hpa⟩
  obtain ⟨j, hj, hmin⟩ := hκ.wellOrder.least T (fun j hj => ((hT j).mp hj).1) ⟨i, hiT⟩
  obtain ⟨hjκ, q, hjq, r, hrp, hrq⟩ := (hT j).mp hj
  have hjJ : M.mem j J := (hJ j).mpr ⟨hjκ, r, (hφ j r).mpr ⟨q, hjq, ⟨hrp.1, hrp.2.1, hrq⟩, by
    intro k hkj t hkt hrt
    obtain ⟨s, hsr, hst⟩ := hrt
    have hkT := (hT k).mpr ⟨hκ.transitive j hjκ k hkj, t, hkt, s,
      below_trans_l O hp hsr hrp, hst⟩
    rcases hmin k hkT with he | hjk
    · have he := hZF.1.eq_of_same_members j k he
      exact hκ.wellOrder.linear.irrefl k (hκ.transitive j hjκ k hkj) (he ▸ hkj)
    · exact hκ.wellOrder.linear.irrefl j hjκ (hκ.wellOrder.linear.trans j hjκ k
        (hκ.transitive j hjκ k hkj) j hjκ hjk hkj)⟩⟩
  exact ⟨q, (hD q).mpr ⟨j, (hK.2 j q).mpr ⟨hjJ, hjq⟩⟩, r, hrp, hrq⟩

/-- 对实际函数族取可数个原始代表；允许投影图有任意重复值。 -/
theorem ccc_family_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) {ω A K}
    (hc : Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R z)
    (hK : M.IsSetFunctionFromTo (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) K A B)
    (hz : ∀ p a, Entry_d M p a K → a ≠ z) : ∃ J,
    M.MemberSubset J A ∧ M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) J ω ∧
    ∀ q, M.mem q A → ∃ p a b, M.mem p J ∧ Entry_d M q a K ∧ Entry_d M p b K ∧ Cmp_d M B R z a b := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨X, hX⟩ := ZF.exists_range_of_setFunction hZF I hK.1 hK.2.1
  obtain ⟨D, hdX, hdω, hcover⟩ := ccc_predense_l O hZFC hc (fun a ha => by
    obtain ⟨p, hp⟩ := (hX a).mp ha
    exact ⟨hK.output_mem_of_pairMember hp, hz p a hp⟩)
  let ρ : Env M 1 := ⟨fun _ => K, fun _ => K⟩
  let φ : BinarySchema 1 := { body := entry_m .newest (.bound 1) (.bound 2) }
  have hφ a p : φ.denote ρ a p ↔ Entry_d M p a K := entry_sat_l M hZF.1 _ _ _ _
  obtain ⟨G, hG, hg⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := D) (Y := A) (by
    intro a ha
    obtain ⟨p, hp⟩ := (hX a).mp (hdX a ha)
    exact ⟨p, hK.input_mem_of_pairMember hp, (hφ a p).mpr hp⟩)
  obtain ⟨J, hJ⟩ := ZF.exists_range_of_setFunction hZF I hG.1 hG.2.1
  have hGJ : M.IsSetFunctionFromTo I G D J := ⟨hG.1, hG.2.1, fun a ha => by
    obtain ⟨p, _, hp⟩ := hG.2.2 a ha
    exact ⟨p, (hJ p).mpr ⟨a, hp⟩, hp⟩⟩
  obtain ⟨f, hf⟩ := ZFC.surjection_bound_l I hZFC hGJ (fun p hp => by
    obtain ⟨a, ha⟩ := (hJ p).mp hp
    exact ⟨a, hG.input_mem_of_pairMember ha, ha⟩)
  obtain ⟨g, hgω⟩ := hdω
  refine ⟨J, fun p hp => (hJ p).mp hp |>.elim fun a ha => hG.output_mem_of_pairMember ha,
    ZF.exists_compositionInjection hZF I hf hgω, fun q hq => ?_⟩
  obtain ⟨a, _, hqa⟩ := hK.2.2 q hq
  have haB := hK.output_mem_of_pairMember hqa
  obtain ⟨b, hbD, hab⟩ := hcover a haB ⟨a, (hX a).mpr ⟨q, hqa⟩,
    a, below_refl_l O haB (hz q a hqa), O.refl a haB⟩
  obtain ⟨p, _, hbp⟩ := hG.2.2 b hbD
  exact ⟨p, a, b, (hJ p).mpr ⟨b, hbp⟩, hqa, (hφ b p).mp (hg b p hbp), hab⟩

end YesMetaZFC.Model.Forcing.Internal
