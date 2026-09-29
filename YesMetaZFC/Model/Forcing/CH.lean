import YesMetaZFC.Model.Forcing.CollapseGeneric
import YesMetaZFC.Model.Forcing.InternalChoice
import YesMetaZFC.SetTheory.Continuum
import YesMetaZFC.Model.Forcing.InternalGeneric
import YesMetaZFC.Model.SetTheory.Countable

/-! # ZFC＋CH 的内部塌缩扩张

从地模型自己的 ω、实数幂集与 Hartogs 序数自动构造可数部分函数塌缩。
不增实数与泛型满射共同给出连续统上界；所有旧真初段仍可数，Cantor 定理
因此识别扩张中的第一不可数基数。结论直接使用原 ZFC＋CH 公式理论，
不要求地模型外部良基，也不要求模型自己的 ω 在外部标准。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SmallGraph
universe u
variable (M : SetTheory.Structure.{u})

/-- 自动装配塌缩偏序；其每个地模型泛型扩张都满足原 ZFC＋CH。 -/
theorem ch_forcing_l (hZFC : M.Models ZFC) :
    ∃ B R, Cond_order_d M B R B ∧ (∃ p, M.mem p B ∧ p ≠ B) ∧
      ∀ U, Generic_d M B R B U →
        (extension_l M (ZFC.models_zf_l hZFC) B R B U).Models (ZFC_CH kpair_convention_l) := by
  let hZF := ZFC.models_zf_l hZFC
  let J := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨κ, hκ⟩ := ZF.exists_hartogsNumber hZF J ω
  obtain ⟨A, hA⟩ := ZF.exists_powerSet hZF ω
  obtain ⟨B, R, hB, hR, O, hc⟩ := collapse_closed_l M hZFC hω κ A
  obtain ⟨o, ho⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hoB := (hB o).mpr (coll_empty_l J ho)
  refine ⟨B, R, O, ⟨o, hoB, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hoB)⟩, fun U hU => ?_⟩
  let E := extension_l M hZF B R B U
  have hE : E.Models ZFC := preserves_zfc_l O hZFC hU
  let hEZF := ZFC.models_zf_l hE
  let K := kpair_interpretation_l E hE.1 (KP.exists_pair (ZF.modelsKP hEZF))
  obtain ⟨b, hb⟩ := hU.inhabited
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hZF hU hb
  have he' a y : E.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y := he a y
  have hωE : E.IsOmega (e ω) := image_omega_l (hEN := hE.1) e hi he' hZF
    (internal_foundation_l O hZF hU) hω (fun T => KP.difference_exists_d (ZF.modelsKP hEZF) T (e ω))
  have hκE : E.IsOrdinal (e κ) := image_ordinal_l e hi he' hZF.1
    (internal_foundation_l O hZF hU) hκ.1
  have hAE : E.IsPowerSetOf (e A) (e ω) := by
    intro X
    constructor
    · intro hX y hy
      obtain ⟨a, ha, rfl⟩ := (he' A X).mp hX
      obtain ⟨c, hc, rfl⟩ := (he' a y).mp hy
      exact (image_member_l e hi he').mpr ((hA a).mp ha c hc)
    · intro hX
      obtain ⟨t, _, ht⟩ := value_name_l X
      obtain ⟨w, hw, _, _⟩ := zf_check_l M hZF (hU.proper b hb).1 ω
      obtain ⟨a, s, ha, has, hs⟩ := no_new_reals_l O hZFC hU hω hc hb hw (hv ω w hw) ht hX
      exact (he' A X).mpr ⟨a, (hA a).mpr ha, qval_unique_l (hv a s has) hs⟩
  have hsmall α (hα : E.mem α (e κ)) : E.CardinalLessOrEqual K α (e ω) := by
    obtain ⟨a, ha, rfl⟩ := (he' κ α).mp hα
    obtain ⟨f, hf⟩ := (hκ.2 a (hκ.1.mem ha)).mp ha
    exact ⟨e f, image_injection_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hEZF)) e hi he' hf⟩
  obtain ⟨F, hF, hs⟩ := collapse_surjection_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hEZF))
    O hZFC hU hω hb hB hR (hκ.not_cardinalLessOrEqual (ZF.modelsKP hZF))
    ⟨o, (hA o).mpr (fun x hx => False.elim (ho x hx))⟩ e hi he' hv
  have hCH := ZFC.continuum_bound_l K hE hωE hAE hκE hsmall (ZFC.surjection_bound_l K hE hF hs)
  refine ⟨hE.1, fun s hs => ?_⟩
  rcases hs with hs | rfl
  · exact hE.2 s hs
  · rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    exact (ch_sat_l K hE.1 (⟨Fin.elim0, f⟩ : Env E 0)).mpr hCH

/-- 从任意可数地模型自动构造偏序、泛型滤子及 ZFC＋CH 扩张。 -/
theorem ch_extension_l (hZFC : M.Models ZFC)
    (e : Nat → M.Domain) (he : Function.Surjective e) :
    ∃ B R U, Cond_order_d M B R B ∧ Generic_d M B R B U ∧
      (extension_l M (ZFC.models_zf_l hZFC) B R B U).Models
        (ZFC_CH kpair_convention_l) := by
  obtain ⟨B, R, O, ⟨p, hp, hn⟩, hCH⟩ := ch_forcing_l M hZFC
  obtain ⟨U, hU, _⟩ := internal_generic_l O e he hp hn
  exact ⟨B, R, U, O, hU, hCH U hU⟩

/-- 实际 ZFC＋CH 力迫模型：地模型来自原小图模型的可数初等子结构。 -/
theorem ch_model_l : ∃ N : SetTheory.Structure.{1}, N.Models (ZFC_CH kpair_convention_l) := by
  obtain ⟨M, hZFC, _, e, he⟩ := countable_ground_l
  obtain ⟨B, R, U, _, _, hCH⟩ := ch_extension_l M hZFC e he
  exact ⟨extension_l M (ZFC.models_zf_l hZFC) B R B U, hCH⟩

end YesMetaZFC.Model.Forcing.Internal
