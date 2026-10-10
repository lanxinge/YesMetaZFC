import YesMetaZFC.SetTheory.LargeCardinal.ExtenderShort

/-! # 短扩展器的长度截断

把测度图限制到较短支撑空间，实际得到新的短扩展器。正规性的新增坐标
小于旧坐标，因此仍落在较短长度中；其余测度与共同纤维直接沿限制保持。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ex_restrict_l (hZF : M.Models ZF) {ω κ L F μ : M.Domain}
    (h : Ex_short_d hZF ω κ L F) (hμ : M.IsOrdinal μ) (hκμ : M.mem κ μ) (hμL : M.MemberSubset μ L) :
    ∃ G, Ex_short_d hZF ω κ μ G ∧ ∀ a U, Rd_entry_d a U G ↔
      (∃ n, M.mem n ω ∧ Fn0_d n μ a) ∧ Rd_entry_d a U F := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨S, hS⟩ := ZF.fseq_space_exists_l I hZF h.omega μ
  obtain ⟨G, hg⟩ := ZF.exists_restriction hZF I F S
  have good a : M.mem a S ↔ ∃ n, M.mem n ω ∧ Fn0_d n μ a := (hS a).trans
    (exists_congr fun n => and_congr_right fun _ => ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩)
  have spec a U : Rd_entry_d a U G ↔ (∃ n, M.mem n ω ∧ Fn0_d n μ a) ∧ Rd_entry_d a U F :=
    (hg.2 a U).trans (and_congr_left fun _ => good a)
  have old a U (ha : Rd_entry_d a U G) := ((spec a U).mp ha).2
  have measures : Em_family_d ω κ μ G := by
    refine ⟨fun n a hn ha => ?_, fun a U V hu hv => h.measures.function a U V (old a U hu) (old a V hv), ?_⟩
    · obtain ⟨U, hu⟩ := h.measures.total n a hn (ha.mono_target_l hμL)
      exact ⟨U, (spec a U).mpr ⟨⟨n, hn, ha⟩, hu⟩⟩
    · intro a U ha
      obtain ⟨n, hn, hna⟩ := ((spec a U).mp ha).1
      obtain ⟨m, D, _, hma, hd, hu⟩ := h.measures.measure a U (old a U ha)
      have e := hma.domain_eq_l hZF.1 hna
      subst m
      exact ⟨n, D, hn, hna, hd, hu⟩
  have normal : En_normal_d ω κ μ G := by
    intro n a U D f i α A hn ha haU hd hf hiα hAU below
    obtain ⟨m, b, V, β, B, hm, hmn, hb, hab, hnβ, hβα, hbV, hBV, read⟩ :=
      h.normal n a U D f i α A hn (ha.mono_target_l hμL) (old a U haU) hd hf hiα hAU below
    have hβμ := hμ.transitive α (ha.bound_l hiα).2 β hβα
    have hbμ : Fn0_d m μ b := hb.retarget_l fun r x hrx => by
      rcases (hmn r).mp (hb.bound_l hrx).1 with hr | he
      · obtain ⟨y, hy, hry⟩ := ha.2.1 r hr
        have hry' : Rd_entry_d r y b := hry.elim fun p hp => ⟨p, hp.1, hab p hp.2⟩
        have e := hb.2.2 r (hb.bound_l hrx).1 y (hb.bound_l hry').2 x (hb.bound_l hrx).2 hry' hrx
        exact e ▸ hy
      · have e := hZF.1.eq_of_same_members r n he
        subst r
        exact hb.2.2 n (hb.bound_l hnβ).1 β (hb.bound_l hnβ).2 x (hb.bound_l hrx).2 hnβ hrx ▸ hβμ
    exact ⟨m, b, V, β, B, hm, hmn, hbμ, hab, hnβ, hβα, (spec b V).mpr ⟨⟨m, hm, hbμ⟩, hbV⟩, hBV, read⟩
  have pre : Ex_pre_d hZF ω κ μ G := by
    refine ⟨h.omega, h.critical, h.uncountable, hμ, hκμ,
      ⟨hg.1, fun a U V hu hv => h.graph.2 a U V (old a U hu) (old a V hv)⟩,
      measures, ?_, ?_, ?_, normal, ?_, ?_⟩
    · intro m n q a b U V A hm hn hq ha hab haV hbU hA
      exact h.coherent m n q a b U V A hm hn hq (ha.mono_target_l hμL) (cp0_mono_l hμL hab) (old a V haV) (old b U hbU) hA
    · exact fun n a U D ha hu hd => h.complete n a U D (ha.mono_target_l hμL) (old a U hu) hd
    · exact fun p n a U i r α β hn ha hu hi hr => h.atoms p n a U i r α β hn (ha.mono_target_l hμL) (old a U hu) hi hr
    · exact fun n a U hn ha hu => h.principal n a U hn ha (old a U hu)
    · exact fun a U i α hu hi hα => h.nonprincipal a U i α (old a U hu) hi hα
  refine ⟨G, ⟨pre, fun H f hH hf => ?_⟩, spec⟩
  apply h.countable H f hH
  refine ⟨hf.1.mono_target_l hμL, fun n hn => ?_⟩
  obtain ⟨A, a, U, hA, ha, sub, haU, hAU⟩ := hf.2 n hn
  exact ⟨A, a, U, hA, ha.mono_target_l hμL, sub, old a U haU, hAU⟩

end YesMetaZFC.SetTheory.LargeCardinal
