import YesMetaZFC.Model.Forcing.CohenAdd
import YesMetaZFC.SetTheory.Continuum
import YesMetaZFC.Model.SetTheory.Countable

/-! # ZFC＋¬CH 的参数化 Cohen 扩张

添加量只要在地模型中超过 ω₁，就得到 ¬CH。旧 ω₁ 的基数性由可数链条件保持，
所有旧真初段仍可数，故它仍是扩张的 ω₁。默认装配取第二个 Hartogs 序数为添加量。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

/-- 任意超过旧 ω₁ 的添加量均产生原 ZFC＋¬CH 模型。 -/
theorem cohen_not_ch_l {M : SetTheory.Structure.{u}} {B R : M.Domain} {U : M.Domain → Prop}
    (O : Cond_order_d M B R B) (hZFC : M.Models ZFC) (hU : Generic_d M B R B U)
    {ω κ ν} (hω : M.IsOmega ω)
    (hκ : M.IsHartogsNumber (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) κ ω)
    (hν : ¬ M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ν κ)
    (hc : Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R B)
    (h : Cohen_result_d O hZFC hU ω ν) :
    (extension_l M (ZFC.models_zf_l hZFC) B R B U).Models (ZFC_not_CH kpair_convention_l) := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let E := extension_l M hZF B R B U
  obtain ⟨hE, b, hb, e, hi, he, hv, hωE, hpres, A, H, hA, hH, _⟩ := h
  let hEZF := ZFC.models_zf_l hE
  let J := kpair_interpretation_l E hE.1 (KP.exists_pair (ZF.modelsKP hEZF))
  obtain ⟨f, hf⟩ := ZF.exists_identityBijection hZF I ω
  have hωκ := (hκ.2 ω (hω.isOrdinal hZF)).mpr ⟨f, hf.1⟩
  have hκInf : M.IsInfiniteCardinal I ω κ :=
    ⟨hκ.isCardinal hZF I, ZF.exists_inclusionInjection hZF I (hκ.1.transitive ω hωκ)⟩
  have hκE : E.IsInfiniteCardinal J (e ω) (e κ) := hpres κ hκInf
  have hsmall α (hα : E.mem α (e κ)) : E.CardinalLessOrEqual J α (e ω) := by
    obtain ⟨a, ha, rfl⟩ := (he κ α).mp hα
    obtain ⟨f, hf⟩ := (hκ.2 a (hκ.1.mem ha)).mp ha
    exact ⟨e f, image_injection_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hEZF)) e hi he hf⟩
  have hκω : ¬ E.CardinalLessOrEqual J (e κ) (e ω) := fun h =>
    hκE.1.2 (e ω) ((image_member_l e hi he).mpr hωκ)
      (ZF.equinumerous_of_cardinalLessOrEqual hEZF J hκE.2 h)
  have hκH := ZF.hartogs_bound_l J hEZF hκE.1.1 hsmall hκω
  have hn : ¬ CH_d J := ZF.not_ch_l J hEZF hωE hA hκH ⟨H, hH⟩ (fun h =>
    hν (ccc_cardinal_reflect_l O hZFC hU hω hc hκInf hb e hi he hv h))
  refine ⟨hE.1, fun s hs => ?_⟩
  rcases hs with hs | rfl
  · exact hE.2 s hs
  · rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    apply (Formula.satisfies_neg_iff (⟨Fin.elim0, f⟩ : Env E 0) (ch_m kpair_convention_l)).mpr
    exact fun h => hn ((ch_sat_l J hE.1 _).mp h)

/-- 任意地模型自动获得迫使 ¬CH 的偏序；该结论不要求存在外部良基呈现。 -/
theorem not_ch_forcing_l (M : SetTheory.Structure.{u}) (hZFC : M.Models ZFC) :
    ∃ B R, Cond_order_d M B R B ∧ (∃ p, M.mem p B ∧ p ≠ B) ∧
      ∀ U, Generic_d M B R B U →
        (extension_l M (ZFC.models_zf_l hZFC) B R B U).Models (ZFC_not_CH kpair_convention_l) := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨κ, hκ⟩ := ZF.exists_hartogsNumber hZF I ω
  obtain ⟨ν, hν⟩ := ZF.exists_hartogsNumber hZF I κ
  obtain ⟨ω', B, R, hω', O, hp, hc, h⟩ := cohen_forcing_l M hZFC ν
  have hωeq : ω' = ω := hZF.1.eq_of_same_members ω' ω (fun x =>
    ⟨hω'.2 ω hω.1 x, hω.2 ω' hω'.1 x⟩)
  subst ω'
  exact ⟨B, R, O, hp, fun U hU => cohen_not_ch_l O hZFC hU hω hκ
    (hν.not_cardinalLessOrEqual (ZF.modelsKP hZF)) hc (h U hU)⟩

/-- 任意可数地模型上，一次构造偏序、泛型及原 ZFC＋¬CH 扩张。 -/
theorem not_ch_extension_l (M : SetTheory.Structure.{u}) (hZFC : M.Models ZFC)
    (e : Nat → M.Domain) (he : Function.Surjective e) :
    ∃ B R U, Cond_order_d M B R B ∧ Generic_d M B R B U ∧
      (extension_l M (ZFC.models_zf_l hZFC) B R B U).Models (ZFC_not_CH kpair_convention_l) := by
  obtain ⟨B, R, O, ⟨p, hp, hn⟩, h⟩ := not_ch_forcing_l M hZFC
  obtain ⟨U, hU, _⟩ := internal_generic_l O e he hp hn
  exact ⟨B, R, U, O, hU, h U hU⟩

/-- 实际 ZFC＋¬CH 模型；地模型实例由现有可数初等子模型构造提供。 -/
theorem not_ch_model_l : ∃ N : SetTheory.Structure.{1}, N.Models (ZFC_not_CH kpair_convention_l) := by
  obtain ⟨M, hZFC, _, e, he⟩ := countable_ground_l
  obtain ⟨B, R, U, _, _, hN⟩ := not_ch_extension_l M hZFC e he
  exact ⟨extension_l M (ZFC.models_zf_l hZFC) B R B U, hN⟩

end YesMetaZFC.Model.Forcing.Internal
