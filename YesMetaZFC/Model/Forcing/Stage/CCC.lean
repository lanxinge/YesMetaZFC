import YesMetaZFC.Model.Forcing.Stage.Embedding

/-! # CCC 沿实际满阶段嵌入搬运 -/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

theorem reg_surj_ccc_l (hZF : M.Models ZF) {ω P R z Q S w F}
    (hc : Ccc_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω P R z)
    (h : Reg_embed_d M P R z Q S w F)
    (hs : ∀ q, M.mem q Q → q ≠ w → ∃ p, Entry_d M p q F) :
    Ccc_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω Q S w := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  intro A ha
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : BinarySchema 1 := { body := entry_m .newest (.bound 1) (.bound 2) }
  have hφ q p : φ.denote ρ q p ↔ Entry_d M p q F := entry_sat_l M hZF.1 _ _ _ _
  obtain ⟨K, hK, hk⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := A) (target := P)
    (fun q hq => by
      obtain ⟨p, hp⟩ := hs q (ha.1 q hq).1 (ha.1 q hq).2
      exact ⟨p, (hφ q p).mpr hp⟩)
    (fun q _ p r hp hr => h.injective p r q ((hφ q p).mp hp) ((hφ q r).mp hr))
    (fun q p _ hp => (h.domain p q ((hφ q p).mp hp)).1)
  have edge {q p} (hp : Entry_d M q p K) := (hφ q p).mp ((hk q p).mp hp).2
  obtain ⟨D, hD⟩ := ZF.exists_range_of_setFunction hZF I hK.1 hK.2.1
  have hKD : M.IsSetInjectionFromTo I K A D := by
    refine ⟨⟨hK.1, hK.2.1, fun q hq => ?_⟩, fun q r p hq hr => h.functional p q r (edge hq) (edge hr)⟩
    obtain ⟨p, _, hp⟩ := hK.2.2 q hq
    exact ⟨p, (hD p).mpr ⟨q, hp⟩, hp⟩
  have hd : Antichain_d M P R z D := by
    refine ⟨fun p hp => ?_, fun p r hp hr hpr => ?_⟩
    · obtain ⟨q, hq⟩ := (hD p).mp hp
      exact ⟨(h.domain p q (edge hq)).1, (h.domain p q (edge hq)).2.1⟩
    · obtain ⟨q, hq⟩ := (hD p).mp hp
      obtain ⟨s, hs⟩ := (hD r).mp hr
      have he := ha.2 q s (hK.input_mem_of_pairMember hq) (hK.input_mem_of_pairMember hs)
        ((h.compat p r q s (edge hq) (edge hs)).mpr hpr)
      exact hK.1.2 q p r hq (he ▸ hs)
  obtain ⟨g, hg⟩ := hc D hd
  exact ZF.exists_compositionInjection hZF I hKD hg

end YesMetaZFC.Model.Forcing.Internal
