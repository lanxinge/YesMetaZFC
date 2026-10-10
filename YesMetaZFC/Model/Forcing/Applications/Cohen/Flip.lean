import YesMetaZFC.Model.Forcing.Applications.Cohen.FlipSyntax
import YesMetaZFC.Model.Forcing.Internal.Automorphism.Forcing

/-! # Cohen 位翻转的实际内部自同构

条目翻转的像是实际集合，反向条目图给出到原条件的单射，因而保留内部有限性。
再次翻转严格还原条件；由此得到满射、序反射和固定空条件的自同构，无需选择公理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
variable {ω X Y S o l p q : M.Domain}

/-- 名称之外，条件的位翻转本身也完整地构造于地模型内部。 -/
theorem cflip_exists_l (hY : Pair_d M Y o l) (hp : Fn_d I ω X Y p) (S : M.Domain) :
    ∃ q, Cflip_d S o l p q ∧ Fn_d I ω X Y q := by
  let ρ : Env M 3 := ((⟨fun _ => S, fun _ => S⟩ : Env M 1).push o).push l
  let φ : BinarySchema 3 := { body := cflip_pair_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ v w : φ.denote ρ v w ↔ Cflip_pair_d S o l v w := by
    exact cflip_pair_sat_l hZF.1 _ _ _ _ _ _
  obtain ⟨q, hq⟩ := ZF.exists_functionalImageOn hZF φ ρ p (fun v hv => by
    obtain ⟨a, b, hvab⟩ := hp.1.1.1 v hv
    obtain ⟨c, _, hc⟩ := cflip_val_total_l hY (hp.1.2 a b ⟨v, hvab, hv⟩).2 S a
    obtain ⟨w, hw⟩ := (I).total a c
    exact ⟨w, (hφ v w).mpr ⟨a, b, c, hvab, hw, hc⟩⟩)
    (fun v _ w t hw ht => cflip_pair_unique_l hZF.1 ((hφ v w).mp hw) ((hφ v t).mp ht))
  have he v : M.mem v q ↔ ∃ w, M.mem w p ∧ Cflip_pair_d S o l w v :=
    (hq v).trans (exists_congr fun w => and_congr_right fun _ => hφ w v)
  have hc : Cflip_d S o l p q := ⟨fun v hv => by
    obtain ⟨w, _, a, b, c, _, hv, _⟩ := (he v).mp hv
    exact ⟨a, c, hv⟩, he⟩
  have hqf : Pfn_d I X Y q := by
    refine ⟨⟨hc.1, ?_⟩, ?_⟩
    · intro a b c hab hac
      obtain ⟨d, had, hdb⟩ := (cflip_entry_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hc a b).mp hab
      obtain ⟨e, hae, hec⟩ := (cflip_entry_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hc a c).mp hac
      have hd := hp.1.1.2 a d e had hae
      exact cflip_val_unique_l hdb (hd ▸ hec)
    · intro a b hab
      obtain ⟨c, hac, hcb⟩ := (cflip_entry_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hc a b).mp hab
      exact ⟨(hp.1.2 a c hac).1, cflip_val_target_l hY (hp.1.2 a c hac).2 hcb⟩
  let η := ρ.push p
  let ψ : BinarySchema 4 := {
    body := .conj (.mem .newest (.bound 2))
      (cflip_pair_m (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest) }
  have hψ w v : ψ.denote η w v ↔ M.mem v p ∧ Cflip_pair_d S o l w v := by
    simp only [BinarySchema.denote, ψ, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, cflip_pair_sat_l hZF.1]
    rfl
  obtain ⟨J, hJ⟩ := ZF.exists_setInjectionFromTo_of_denote hZF I ψ η (source := q) (target := p)
    (fun w hw => by
      obtain ⟨v, hv, hvw⟩ := (he w).mp hw
      exact ⟨v, (hψ w v).mpr ⟨hv, cflip_pair_symm_l hvw⟩⟩)
    (fun w _ v t hv ht => cflip_pair_unique_l hZF.1 ((hψ w v).mp hv).2 ((hψ w t).mp ht).2)
    (fun w v _ hv => ((hψ w v).mp hv).1)
    (fun w t v _ _ hw ht => cflip_pair_unique_l hZF.1
      (cflip_pair_symm_l ((hψ w v).mp hw).2) (cflip_pair_symm_l ((hψ t v).mp ht).2))
  obtain ⟨n, hn, H, hH⟩ := hp.2
  exact ⟨q, hc, hqf, n, hn, ZF.exists_compositionInjection hZF I hJ hH⟩

/-- 两次翻转恢复原集合，证明不将内部有限性换成外部有限性。 -/
theorem cflip_inverse_l (hY : Pair_d M Y o l) (hp : Pfn_d I X Y p)
    (h : Cflip_d S o l p q) : Cflip_d S o l q p := by
  refine ⟨hp.1.1, fun v => ⟨?_, ?_⟩⟩
  · intro hv
    obtain ⟨a, b, hvab⟩ := hp.1.1 v hv
    obtain ⟨c, _, hc⟩ := cflip_val_total_l hY (hp.2 a b ⟨v, hvab, hv⟩).2 S a
    obtain ⟨w, hw⟩ := (I).total a c
    have hh : Cflip_pair_d S o l v w := ⟨a, b, c, hvab, hw, hc⟩
    exact ⟨w, (h.2 w).mpr ⟨v, hv, hh⟩, cflip_pair_symm_l hh⟩
  · rintro ⟨w, hw, hwv⟩
    obtain ⟨t, ht, htw⟩ := (h.2 w).mp hw
    exact cflip_pair_unique_l hZF.1 (cflip_pair_symm_l htw) hwv ▸ ht

omit hZF in
theorem cflip_mono_l {r t} (h : Cflip_d S o l p q) (k : Cflip_d S o l r t)
    (hp : M.MemberSubset p r) : M.MemberSubset q t := by
  intro v hv
  obtain ⟨w, hw, hwv⟩ := (h.2 v).mp hv
  exact (k.2 v).mpr ⟨w, hp w hw, hwv⟩

omit hZF in
theorem cflip_empty_l {e} (he : ∀ x, ¬ M.mem x e) (S o l : M.Domain) : Cflip_d S o l e e :=
  ⟨fun x hx => False.elim (he x hx), fun x =>
    ⟨fun hx => False.elim (he x hx), fun ⟨w, hw, _⟩ => False.elim (he w hw)⟩⟩

/-- 任意二元值有限部分函数偏序都获得指定坐标上的内部翻转自同构。 -/
theorem fn_flip_l {B R} (hY : Pair_d M Y o l)
    (hB : ∀ p, M.mem p B ↔ Fn_d I ω X Y p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p)
    (S : M.Domain) : ∃ F, Aut_d M B R B F ∧
      ∀ p q, Entry_d M p q F ↔ M.mem p B ∧ Cflip_d S o l p q := by
  let ρ : Env M 3 := ((⟨fun _ => S, fun _ => S⟩ : Env M 1).push o).push l
  let φ : BinarySchema 3 := { body := cflip_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ p q : φ.denote ρ p q ↔ Cflip_d S o l p q := cflip_sat_l hZF.1 _ _ _ _ _ _
  have ht p (hp : M.mem p B) : ∃ q, M.mem q B ∧ Cflip_d S o l p q := by
    obtain ⟨q, hq, hqf⟩ := cflip_exists_l hZF hY ((hB p).mp hp) S
    exact ⟨q, (hB q).mpr hqf, hq⟩
  obtain ⟨F, hF, hf⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (fun p hp => (ht p hp).elim fun q hq => ⟨q, (hφ p q).mpr hq.2⟩)
    (fun p _ q r hq hr => cflip_unique_l hZF.1 ((hφ p q).mp hq) ((hφ p r).mp hr))
    (fun p q hp hq => by
      obtain ⟨r, hr, hpr⟩ := ht p hp
      exact cflip_unique_l hZF.1 hpr ((hφ p q).mp hq) ▸ hr)
  have he p q : Entry_d M p q F ↔ M.mem p B ∧ Cflip_d S o l p q :=
    (hf p q).trans (and_congr_right fun _ => hφ p q)
  have dom {p q} (hpq : Entry_d M p q F) : M.mem p B ∧ M.mem q B :=
    ⟨hF.input_mem_of_pairMember hpq, hF.output_mem_of_pairMember hpq⟩
  have flip {p q} (hpq : Entry_d M p q F) := ((he p q).mp hpq).2
  have inv {p q} (hpq : Entry_d M p q F) := cflip_inverse_l hZF hY ((hB p).mp (dom hpq).1).1 (flip hpq)
  refine ⟨F, aut_of_bij_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ⟨⟨hF, ?_⟩, ?_⟩ ?_ ?_, he⟩
  · intro p q r hpr hqr
    exact cflip_unique_l hZF.1 (inv hpr) (inv hqr)
  · intro q hq
    obtain ⟨p, hp, hqp⟩ := ht q hq
    exact ⟨p, hp, (he p q).mpr ⟨hp, cflip_inverse_l hZF hY ((hB q).mp hq).1 hqp⟩⟩
  · intro p q s t hps hqt
    rw [hR p q, hR s t]
    exact ⟨fun h => ⟨(dom hps).2, (dom hqt).2, cflip_mono_l (flip hqt) (flip hps) h.2.2⟩,
      fun h => ⟨(dom hps).1, (dom hqt).1, cflip_mono_l (inv hqt) (inv hps) h.2.2⟩⟩
  · intro p q hpq
    exact iff_of_false (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ (dom hpq).1))
      (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ (dom hpq).2))

/-- 现有参数化 Cohen 呈现直接取得翻转图，并核验它固定最大条件。 -/
theorem cohen_flip_l {κ B R} (h : Cohen_spec_d I κ B R) (S : M.Domain) :
    ∃ o l F, (∀ x, ¬ M.mem x o) ∧ M.SuccessorOf l o ∧ Aut_d M B R B F ∧
      Entry_d M o o F ∧ ∀ p q, Entry_d M p q F ↔ M.mem p B ∧ Cflip_d S o l p q := by
  obtain ⟨ω, o, l, Y, X, hω, ho, hl, hY, _, hB, _, hR⟩ := h
  obtain ⟨F, hF, hf⟩ := fn_flip_l hZF hY hB hR S
  exact ⟨o, l, F, ho, hl, hF, (hf o o).mpr ⟨(hB o).mpr (ZF.fn_empty_l I hZF hω ho),
    cflip_empty_l ho S o l⟩, hf⟩

end YesMetaZFC.Model.Forcing.Internal
