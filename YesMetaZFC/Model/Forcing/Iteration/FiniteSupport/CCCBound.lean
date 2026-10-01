import YesMetaZFC.Model.Forcing.Iteration.FiniteSupport.CCCSyntax

/-! # 有限尾支撑反链的可数性

对尾支撑大小界归纳，且同时量化所有早期前缀。先取可数个前缀预稠密代表；
其支撑并可数。其余反链元素必须与某代表共享一个尾坐标，否则尾部合并使之
相容。把该坐标移入更长前缀，尾大小界降一，再用可数覆盖收尾。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

theorem row_bounded_ccc_l (hZFC : M.Models ZFC) {γ F H e ω δ P V}
    (h : Row_system_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) γ F H e)
    (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hS : Row_system_supp_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) false ω F)
    (hP : Entry_d M δ P F) (hV : Entry_d M δ V H)
    (hc : ∀ α B R, M.mem α δ → Entry_d M α B F → Entry_d M α R H →
      Ccc_d M (kpair_interpretation_l M hZFC.1
        (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R B) :
    ∀ n, M.mem n ω → Row_bounded_ccc_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) δ F H P V ω n := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 6 := (((((⟨fun _ => δ, fun _ => δ⟩ : Env M 1).push F).push H).push P).push V).push ω
  let φ : UnarySchema 6 := {
    body := row_bounded_ccc_m (.bound 6) (.bound 5) (.bound 4)
      (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ n : φ.denote ρ n ↔ Row_bounded_ccc_d I δ F H P V ω n := row_bounded_ccc_sat_l I hZF.1 _ _ _ _ _ _ _ _
  apply hω.induction (fun n => Row_bounded_ccc_d I δ F H P V ω n)
  · obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨D, fun n => (hD n).trans (and_congr_right fun _ => hφ n)⟩
  · intro n hn α B R A hα hB hR ha hb
    have link := h.links α δ B R P V hB hR hP hV (hδ.1.transitive.memberSubset hα)
    have mem p (hp : M.mem p A) : M.mem p B := by
      have hr := (h.stages δ P V hP hV).rows p (ha.1 p hp).1
      obtain ⟨D, hD, f, hf⟩ := hb p hp
      have dom i s (his : Entry_d M i s p) : M.mem i α := by
        classical
        by_cases hi : M.mem i α
        · exact hi
        · obtain ⟨j, hj, _⟩ := hf.1.2.2 i ((hD i).mpr ⟨⟨s, his⟩, hi⟩)
          exact False.elim (hn j hj)
      obtain ⟨q, hq, hqp⟩ := link.restrict p (ha.1 p hp).1
      have he := hqp.eq hZF.1 ⟨hr.graph, fun i s => ⟨fun his => ⟨dom i s his, his⟩, And.right⟩⟩
      exact he ▸ hq
    apply hc α B R hα hB hR A
    refine ⟨fun p hp => ⟨mem p hp, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ mem p hp)⟩,
      fun p q hp hq hpq => ha.2 p q hp hq ?_⟩
    obtain ⟨r, hrp, hrq⟩ := hpq
    have hr := link.mem r hrp.1
    exact ⟨r, ⟨hr, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) P (he ▸ hr),
      (link.order r p hrp.1 (mem p hp)).mpr hrp.2.2⟩, (link.order r q hrp.1 (mem q hq)).mpr hrq⟩
  · intro n _ ih s hs α B R A hα hB hR ha hb
    have link := h.links α δ B R P V hB hR hP hV (hδ.1.transitive.memberSubset hα)
    let η : Env M 1 := ⟨fun _ => α, fun _ => α⟩
    let ψ : BinarySchema 1 := { body := Formula.isRestriction kpair_convention_l .newest (.bound 1) (.bound 2) }
    have hψ p a : ψ.denote η p a ↔ M.IsRestrictionOf I a p α := Formula.satisfies_isRestriction_iff I _ _ _ _
    obtain ⟨K, hK, hk⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η (source := A) (target := B)
      (fun p hp => by
        obtain ⟨a, _, hap⟩ := link.restrict p (ha.1 p hp).1
        exact ⟨a, (hψ p a).mpr hap⟩)
      (fun p _ a b ha hb => ((hψ p a).mp ha).eq hZF.1 ((hψ p b).mp hb))
      (fun p a hp hap => by
        obtain ⟨b, hb, hbp⟩ := link.restrict p (ha.1 p hp).1
        exact (hbp.eq hZF.1 ((hψ p a).mp hap)) ▸ hb)
    obtain ⟨J, hjA, hjω, hcover⟩ := ccc_family_l (h.stages α B R hB hR).order hZFC (hc α B R hα hB hR) hK
      (fun p a hpa he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hK.output_mem_of_pairMember hpa))
    obtain ⟨C, hC, hcω⟩ := row_countable_coords_l hZFC hω hjω (fun p hp => by
      obtain ⟨D, hD, hd⟩ := hS δ P hP p (ha.1 p (hjA p hp)).1
      exact ⟨D, hD, ZF.finite_countable_l I hZF hω hd⟩)
    obtain ⟨Y, hY⟩ := KP.difference_exists_d (ZF.modelsKP hZF) J A
    let χ : BinarySchema 1 := {
      body := .conj (.existsE (entry_m (.bound 2) .newest (.bound 1)))
        (.neg (.mem (.bound 1) (.bound 2))) }
    have hχ i q : χ.denote η i q ↔ (∃ t, Entry_d M i t q) ∧ ¬ M.mem i α := by
      simp only [BinarySchema.denote, χ, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
        entry_sat_l M hZF.1, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff]
      rfl
    have hyω : M.CardinalLessOrEqual I Y ω := by
      apply ZFC.countable_cover_l I hZFC hω χ η hcω
      · intro i hi D hD
        classical
        by_cases hiα : M.mem i α
        · exact ZF.exists_inclusionInjection hZF I (fun q hq =>
            False.elim (((hχ i q).mp ((hD q).mp hq).2).2 hiα))
        · obtain ⟨p, hp, t, hpt⟩ := (hC i).mp hi
          have hiδ := (h.stages δ P V hP hV).rows p (ha.1 p (hjA p hp)).1 |>.domain i t hpt
          obtain ⟨β, hβ, hiβ⟩ := hδ.2.2 i hiδ
          have hαβ : M.MemberSubset α β := by
            rcases hδ.1.wellOrder.linear.compare α hα β hβ with he | he | he
            · exact fun j hj => (he j).mp hj
            · exact (hδ.1.mem hβ).transitive.memberSubset he
            · exact False.elim (hiα ((hδ.1.mem hα).transitive β he i hiβ))
          have hβγ := h.conditions.1.transitive δ ((h.conditions.2.2 δ).mpr ⟨P, hP⟩) β hβ
          obtain ⟨E, hE⟩ := (h.conditions.2.2 β).mp hβγ
          obtain ⟨W, hW⟩ := (h.relations.2.2 β).mp hβγ
          have sub q (hq : M.mem q D) := ((hY q).mp ((hD q).mp hq).1).1
          exact ih β E W D hβ hE hW ⟨fun q hq => ha.1 q (sub q hq),
            fun q r hq hr hqr => ha.2 q r (sub q hq) (sub r hr) hqr⟩
            (fun q hq => row_tail_delete_l hZF hs hαβ hiβ hiα
              ((hχ i q).mp ((hD q).mp hq).2).1 (hb q (sub q hq)))
      · intro q hq
        obtain ⟨hqA, hqJ⟩ := (hY q).mp hq
        obtain ⟨p, a, b, hpJ, hqa, hpb, hab⟩ := hcover q hqA
        classical
        apply Classical.byContradiction
        intro hn
        have hd : Row_disjoint_d α q p := by
          intro i t v hqt hpv
          by_cases hi : M.mem i α
          · exact hi
          · exact False.elim (hn ⟨i, (hC i).mpr ⟨p, hpJ, v, hpv⟩, (hχ i q).mpr ⟨⟨t, hqt⟩, hi⟩⟩)
        have he := ha.2 q p hqA (hjA p hpJ) (row_amalgam_l hZF h hω hS hB hR hP hV
          (ha.1 q hqA).1 (ha.1 p (hjA p hpJ)).1 (hδ.1.transitive.memberSubset hα) hd
          ⟨a, b, (hψ q a).mp ((hk q a).mp hqa).2, (hψ p b).mp ((hk p b).mp hpb).2, hab⟩)
        exact hqJ (he ▸ hpJ)
    apply ZF.countable_union_two_l I hZF hω hjω hyω
    intro p
    rw [hY p]
    classical
    exact ⟨fun hp => (Classical.em (M.mem p J)).elim Or.inl (fun hn => Or.inr ⟨hp, hn⟩),
      fun hp => hp.elim (hjA p) And.left⟩

end YesMetaZFC.Model.Forcing.Internal
