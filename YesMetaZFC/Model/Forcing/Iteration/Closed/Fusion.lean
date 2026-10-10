import YesMetaZFC.Model.Forcing.Iteration.Closed.Thread
import YesMetaZFC.Model.Forcing.Iteration.Fusion.Basic

/-! # 下界前缀序列的精确融合与整链比较

相邻限制经原公式内部 ω 归纳传播；严格共尾指标允许按阶段重编号。
实际并条件逐前缀低于原链，故由原支撑极限序关系低于整条链。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

private theorem row_cl_coherent_l {ω δ F G b β f A X Q}
    (hω : M.IsOmega ω) (h : Row_system_d I δ F G b) (hA : M.IsCofinalOrdinalSequence I A ω β)
    (hQ : M.IsSetFunctionFromTo I Q ω X) (hv : ∀ i q, Entry_d M i q Q → Row_cl_at_d I F G f A i q)
    (hs : ∀ i j q r ξ, M.SuccessorOf j i → Entry_d M i q Q → Entry_d M j r Q → Entry_d M i ξ A →
      M.IsRestrictionOf I q r ξ) :
    ∀ i j α γ p q, Entry_d M i α A → Entry_d M j γ A → Entry_d M i p Q → Entry_d M j q Q →
      M.MemberSubset α γ → M.IsRestrictionOf I p q α := by
  have hAF := hA.isSetFunctionFromTo
  have rows {i α p} (hiα : Entry_d M i α A) (hip : Entry_d M i p Q) : Row_d M α p := by
    obtain ⟨ξ, B, R, hiξ, hB, hR, hp, _⟩ := hv i p hip
    exact hAF.1.2 i ξ α hiξ hiα ▸ (h.stages ξ B R hB hR).rows p hp
  have self {α γ p} (hr : Row_d M α p) (ha : M.MemberSubset α γ) : M.IsRestrictionOf I p p γ :=
    ⟨hr.graph, fun i s => ⟨fun his => ⟨ha i (hr.domain i s his), his⟩, And.right⟩⟩
  have earlier i α p (hiα : Entry_d M i α A) (hip : Entry_d M i p Q) :
      ∀ j, M.mem j ω → ∀ γ q, Entry_d M j γ A → Entry_d M j q Q → M.mem i j → M.IsRestrictionOf I p q α := by
    let ρ : Env M 5 := ((((⟨fun _ => i, fun _ => i⟩ : Env M 1).push α).push p).push A).push Q
    let φ : UnarySchema 5 := {
      body := .forallE (.forallE (.imp (entry_m (.bound 2) (.bound 1) (.bound 4))
        (.imp (entry_m (.bound 2) .newest (.bound 3)) (.imp (.mem (.bound 7) (.bound 2))
          (Formula.isRestriction kpair_convention_l (.bound 5) .newest (.bound 6)))))) }
    have hφ j : φ.denote ρ j ↔ ∀ γ q, Entry_d M j γ A → Entry_d M j q Q → M.mem i j → M.IsRestrictionOf I p q α := by
      simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
        entry_sat_l M hZF.1, Formula.satisfies_mem_iff, Formula.satisfies_isRestriction_iff I]
      rfl
    apply hω.induction (fun j => ∀ γ q, Entry_d M j γ A → Entry_d M j q Q → M.mem i j → M.IsRestrictionOf I p q α)
    · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨C, fun j => (hC j).trans (and_congr_right fun _ => hφ j)⟩
    · exact fun o ho _ _ _ _ hi => (ho i hi).elim
    · intro j hj ih k hjk γ q hkγ hkq hik
      obtain ⟨ξ, hξβ, hjξ⟩ := hAF.2.2 j hj
      obtain ⟨r, _, hjr⟩ := hQ.2.2 j hj
      have hrq := hs j k r q ξ hjk hjr hkq hjξ
      rcases (hjk i).mp hik with hij | he
      · exact (ih ξ r hjξ hjr hij).comp_l hrq ((hA.1.1.mem hξβ).transitive.memberSubset
          (hA.isIncreasing.2 i (hAF.input_mem_of_pairMember hiα) j hj hij α ξ hiα hjξ))
      · have he := hZF.1.eq_of_same_members i j he
        subst j
        have heα := hAF.1.2 i ξ α hjξ hiα
        have hep := hQ.1.2 i r p hjr hip
        exact heα ▸ hep ▸ hrq
  intro i j α γ p q hiα hjγ hip hjq hαγ
  rcases (hω.isOrdinal hZF).wellOrder.linear.compare i (hQ.input_mem_of_pairMember hip)
      j (hQ.input_mem_of_pairMember hjq) with he | hij | hji
  · have he := hZF.1.eq_of_same_members i j he
    subst j
    exact hQ.1.2 i p q hip hjq ▸ self (rows hiα hip) (fun _ h => h)
  · exact earlier i α p hiα hip j (hQ.input_mem_of_pairMember hjq) γ q hjγ hjq hij
  · have hqp := earlier j γ q hjγ hjq i (hQ.input_mem_of_pairMember hip) α p hiα hip hji
    have he := hqp.eq hZF.1 (self (rows hiα hip) hαγ)
    exact he.symm ▸ self (rows hiα hip) (fun _ h => h)

omit hZF in
/-- 共尾下界前缀的实际融合精确保留每项，并在原极限偏序中低于整条旧链。 -/
theorem row_cl_fuse_l (hZFC : M.Models ZFC) {ω δ F G b β F' G' D V f A X Q}
    (hω : M.IsOmega ω)
    (h : Row_system_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) δ F G b)
    (hD : Entry_d M β D F) (hV : Entry_d M β V G)
    (hF : M.IsRestrictionOf (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) F' F β)
    (hG : M.IsRestrictionOf (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) G' G β)
    (hS : Row_system_supp_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) true ω F)
    (hl : Row_limit_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) true ω β F' G' β D V)
    (hA : M.IsCofinalOrdinalSequence (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) A ω β)
    (hQ : M.IsSetFunctionFromTo (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) Q ω X)
    (hfs : ∀ i r, Entry_d M i r f → M.mem r D)
    (hv : ∀ i q, Entry_d M i q Q → Row_cl_at_d
      (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) F G f A i q)
    (hs : ∀ i j q r ξ, M.SuccessorOf j i → Entry_d M i q Q → Entry_d M j r Q → Entry_d M i ξ A →
      M.IsRestrictionOf (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) q r ξ) :
    ∃ q, M.mem q D ∧
      (∀ i ξ p, Entry_d M i ξ A → Entry_d M i p Q → M.IsRestrictionOf
        (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) p q ξ) ∧
      ∀ i r, Entry_d M i r f → Entry_d M q r V := by
  have hZF := ZFC.models_zf_l hZFC
  let I₀ := kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP hZF))
  have hAF := hA.isSetFunctionFromTo
  have hAI := hA.isSetInjectionFromTo hZF I₀
  have hβδ := (h.conditions.2.2 β).mpr ⟨D, hD⟩
  have coh := row_cl_coherent_l hZF hω h hA hQ hv hs
  obtain ⟨J, hJ⟩ := ZF.exists_range_of_setFunction hZF I₀ hAF.1 hAF.2.1
  have hAJ : M.IsSetFunctionFromTo I₀ A ω J := ⟨hAF.1, hAF.2.1, fun i hi => by
    obtain ⟨ξ, _, hiξ⟩ := hAF.2.2 i hi
    exact ⟨ξ, (hJ ξ).mpr ⟨i, hiξ⟩, hiξ⟩⟩
  have hCount : M.CardinalLessOrEqual I₀ J ω := ZFC.surjection_bound_l I₀ hZFC hAJ (fun ξ hξ => by
    obtain ⟨i, hiξ⟩ := (hJ ξ).mp hξ
    exact ⟨i, hAF.input_mem_of_pairMember hiξ, hiξ⟩)
  have hcof := hA.range_isCofinalSubset hZFC.1 hJ
  let ρ : Env M 2 := (⟨fun _ => A, fun _ => A⟩ : Env M 1).push Q
  let φ : BinarySchema 2 := {
    body := .existsE (.conj (entry_m .newest (.bound 2) (.bound 4)) (entry_m .newest (.bound 1) (.bound 3))) }
  have hφ ξ p : φ.denote ρ ξ p ↔ ∃ i, Entry_d M i ξ A ∧ Entry_d M i p Q := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, entry_sat_l M hZFC.1]
    rfl
  obtain ⟨W, hW, hw⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I₀ φ ρ (source := J) (target := X) (by
    intro ξ hξ
    obtain ⟨i, hiξ⟩ := (hJ ξ).mp hξ
    obtain ⟨p, _, hip⟩ := hQ.2.2 i (hAF.input_mem_of_pairMember hiξ)
    exact ⟨p, (hφ ξ p).mpr ⟨i, hiξ, hip⟩⟩) (by
    intro ξ _ p q hp hq
    obtain ⟨i, hiξ, hip⟩ := (hφ ξ p).mp hp
    obtain ⟨j, hjξ, hjq⟩ := (hφ ξ q).mp hq
    have he := hAI.2 i j ξ hiξ hjξ
    subst j
    exact hQ.1.2 i p q hip hjq) (by
    intro ξ p _ hp
    obtain ⟨_, _, hip⟩ := (hφ ξ p).mp hp
    exact hQ.output_mem_of_pairMember hip)
  have edge ξ p : Entry_d M ξ p W ↔ ∃ i, Entry_d M i ξ A ∧ Entry_d M i p Q := by
    refine (hw ξ p).trans ⟨fun hh => (hφ ξ p).mp hh.2, ?_⟩
    rintro ⟨i, hiξ, hip⟩
    exact ⟨(hJ ξ).mpr ⟨i, hiξ⟩, (hφ ξ p).mpr ⟨i, hiξ, hip⟩⟩
  have info {ξ p} (hp : Entry_d M ξ p W) : ∃ B R,
      Entry_d M ξ B F ∧ Entry_d M ξ R G ∧ M.mem p B ∧ Row_chain_lower_d I₀ ξ R f p := by
    obtain ⟨i, hiξ, hip⟩ := (edge ξ p).mp hp
    obtain ⟨ζ, B, R, hiζ, hB, hR, hp, hpf⟩ := hv i p hip
    have he := hAF.1.2 i ζ ξ hiζ hiξ
    subst ζ
    exact ⟨B, R, hB, hR, hp, hpf⟩
  have wf : Row_fusion_d I₀ β F' J W := ⟨hW.1, hW.2.1, hcof.2.1, fun ξ hξ => (hcof.2.2 ξ).mp hξ,
    (fun ξ p hp => by
      obtain ⟨B, _, hB, _, hpB, _⟩ := info hp
      exact ⟨B, (hF.2 ξ B).mpr ⟨hcof.2.1 ξ (hW.input_mem_of_pairMember hp), hB⟩, hpB⟩),
    fun ξ ζ p q hp hq hξζ => by
      obtain ⟨i, hiξ, hip⟩ := (edge ξ p).mp hp
      obtain ⟨j, hjζ, hjq⟩ := (edge ζ q).mp hq
      exact coh i j ξ ζ p q hiξ hjζ hip hjq hξζ⟩
  have part := row_system_restrict_l hZFC.1 (KP.exists_pair (ZF.modelsKP hZF)) h hA.1.1
    (h.conditions.1.transitive.memberSubset hβδ) hF hG
  obtain ⟨q, hq, _, hpre, _⟩ := row_fusion_l hZFC part hω
    (fun ξ B hB => hS ξ B ((hF.2 ξ B).mp hB).2) hl wf hCount
  refine ⟨q, hq, fun i ξ p hiξ hip => (hpre ξ p ((edge ξ p).mpr ⟨i, hiξ, hip⟩)).1, fun j r hjr => ?_⟩
  refine (hl.relation q r).mpr ⟨hq, hfs j r hjr, fun ζ Rζ hRζ u v hu hv => ?_⟩
  obtain ⟨hζβ, hRζ⟩ := (hG.2 ζ Rζ).mp hRζ
  have hζδ := h.conditions.1.transitive β hβδ ζ hζβ
  obtain ⟨Bζ, hBζ⟩ := (h.conditions.2.2 ζ).mp hζδ
  obtain ⟨ξ, hξJ, hζξ⟩ := (hcof.2.2 ζ).mp hζβ
  obtain ⟨p, _, hξp⟩ := hW.2.2 ξ hξJ
  obtain ⟨Bξ, Rξ, hBξ, hRξ, hpB, hpf⟩ := info hξp
  have hξβ := hcof.2.1 ξ hξJ
  have hζξ := (hA.1.1.mem hξβ).transitive.memberSubset hζξ
  have k := h.links ξ β Bξ Rξ D V hBξ hRξ hD hV (hA.1.1.transitive.memberSubset hξβ)
  obtain ⟨a, ha, har⟩ := k.restrict r (hfs j r hjr)
  exact (h.links ζ ξ Bζ Rζ Bξ Rξ hBζ hRζ hBξ hRξ hζξ).mono p a u v hpB ha
    ((hpre ξ p hξp).1.trans hu hζξ) (har.trans hv hζξ) (hpf j r a hjr har)

end YesMetaZFC.Model.Forcing.Internal
