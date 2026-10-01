import YesMetaZFC.Model.Forcing.Proper.Master.Basic
import YesMetaZFC.Model.Forcing.CCC.Predense
import YesMetaZFC.SetTheory.CountableHull

/-! # CCC 的内部可数主条件闭包

为每个稠密集实际选取可数预稠密子集，再对这张多值图作内部可数闭包。所得
集合包含任意给定可数种子，且每个正条件都是其主条件。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z ω : M.Domain}

/-- CCC 偏序在任意含条件域的集合中，自动产生包含指定种子的内部可数主条件闭包。 -/
theorem ccc_mstr_hull_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) (hω : M.IsOmega ω)
    (hc : Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R z)
    {X A} (hBX : M.MemberSubset B X) (hAX : M.MemberSubset A X)
    (hA : M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) A ω) : ∃ N,
    M.MemberSubset A N ∧ M.MemberSubset N X ∧
    M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) N ω ∧
    ∀ p, M.mem p B → p ≠ z → Mstr_d M B R z N p := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF X
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push ω
  let φ : BinarySchema 4 := {
    body := .conj (Formula.cardinalLessOrEqual kpair_convention_l .newest (.bound 2))
      (.imp (dense_set_m (.bound 5) (.bound 4) (.bound 3) (.bound 1))
        (.conj (Formula.subset .newest (.bound 1)) (Formula.forallMem (.bound 5)
          (.imp (.neg (Formula.extensionalEq .newest (.bound 4))) (.existsE
            (.conj (.mem .newest (.bound 2)) (cmp_m (.bound 7) (.bound 6) (.bound 5) (.bound 1) .newest))))))) }
  have hφ D Y : φ.denote ρ D Y ↔ M.CardinalLessOrEqual I Y ω ∧
      (Dense_set_d M B R z D → M.MemberSubset Y D ∧
        ∀ p, M.mem p B → p ≠ z → ∃ s, M.mem s Y ∧ Cmp_d M B R z p s) := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff,
      Formula.satisfies_cardinalLessOrEqual_iff I hZF.1, Formula.satisfies_imp_iff,
      dense_set_sat_l M hZF.1, Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Formula.satisfies_exists_iff, Formula.satisfies_mem_iff, cmp_sat_l M hZF.1]
    rfl
  obtain ⟨F, hF, hf⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := X) (Y := P) (by
    intro D _
    classical
    by_cases hd : Dense_set_d M B R z D
    · obtain ⟨Y, hYD, hy, hpred⟩ := ccc_predense_l O hZFC hc hd.1
      refine ⟨Y, (hP Y).mpr (fun p hp => hBX p (hd.1 p (hYD p hp)).1), (hφ D Y).mpr ⟨hy, fun _ => ⟨hYD, ?_⟩⟩⟩
      intro p hp hn
      obtain ⟨r, hr, hrD⟩ := hd.2 p hp hn
      exact hpred p hp ⟨r, hrD, r, hr, O.refl r hr.1⟩
    · obtain ⟨E, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
      exact ⟨E, (hP E).mpr (fun x hx => False.elim (he x hx)), (hφ D E).mpr
        ⟨ZF.exists_inclusionInjection hZF I (fun x hx => False.elim (he x hx)), fun h => False.elim (hd h)⟩⟩)
  obtain ⟨N, haN, hNX, hn, hclosed⟩ := ZFC.cc_hull_l I hZFC hω hP hF
    (fun D Y hDY => ((hφ D Y).mp (hf D Y hDY)).1) hAX hA
  refine ⟨N, haN, hNX, hn, fun p hp hz => ⟨hp, hz, fun D hDN hd r hr => ?_⟩⟩
  obtain ⟨Y, _, hDY⟩ := hF.2.2 D (hNX D hDN)
  obtain ⟨s, hs, hrs⟩ := (((hφ D Y).mp (hf D Y hDY)).2 hd).2 r hr.1 hr.2.1
  exact ⟨s, (((hφ D Y).mp (hf D Y hDY)).2 hd).1 s hs, hclosed D Y hDN hDY s hs, hrs⟩

/-- 一键闭包允许种子包含任意对象；环境自动加入全部条件及其子集。 -/
theorem ccc_mstr_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) (hω : M.IsOmega ω)
    (hc : Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R z)
    {A} (hA : M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) A ω) : ∃ N,
    M.MemberSubset A N ∧ M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) N ω ∧
    ∀ p, M.mem p B → p ≠ z → Mstr_d M B R z N p := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨P, _⟩ := ZF.exists_powerSet hZF B
  obtain ⟨Y, hY⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) B P
  obtain ⟨X, hX⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) Y A
  obtain ⟨N, hAN, _, hn, hm⟩ := ccc_mstr_hull_l O hZFC hω hc
    (fun p hp => (hX p).mpr (Or.inl ((hY p).mpr (Or.inl hp))))
    (fun a ha => (hX a).mpr (Or.inr ha)) hA
  exact ⟨N, hAN, hn, hm⟩

end YesMetaZFC.Model.Forcing.Internal
