import YesMetaZFC.Model.Forcing.Proper.Family.Syntax

/-! # 从共同小模型到全阶段内部力迫证书

在实际可数反射模型中，对已构造的同一个 N 同时应用全泛型判据。最后反射
整条存在公式；得到的 Hlift_d 是地模型内原公式的真实证书，不假定提升成立。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

private theorem countable_hlift_l (e : Nat → M.Domain) (he : Function.Surjective e)
    {ω δ F G b A} (hω : M.IsOmega ω) (hF : M.IsSetFunction I F) (hG : M.IsSetFunction I G)
    (ha : M.CardinalLessOrEqual I A ω) : ∃ χ X N w v,
      Hsub_d I ω χ X N ∧ M.MemberSubset A N ∧ M.mem F N ∧ M.mem G N ∧ M.mem δ N ∧ M.mem b N ∧
      Hlift_d M ω δ F G b χ X N w v := by
  obtain ⟨χ, X, c, J, N, d, K, hχ, hωχ, hX, hM, hSub, hElem, hAN, hn, hFN, hGN, hδN, hbN, hg⟩ :=
    ng_family_hull_l (δ := δ) (b := b) hZFC hω hF hG ha
  obtain ⟨w, hw⟩ := check_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF) b ω
  obtain ⟨v, hv⟩ := check_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF) b χ
  refine ⟨χ, X, N, w, v, ⟨hω, hχ, hωχ, hX, hn, c, J, d, K, hM, hSub, hElem⟩,
    hAN, hFN, hGN, hδN, hbN, hw, hv, ?_⟩
  intro i B R q ν μ hi hiN hiB hiR O hb hm hqb hν hμ
  have hwN := check_name_l M (check_range_l M hZF) hb hw
  have hvN := check_name_l M (check_range_l M hZF) hb hv
  let ρ := hsub_env_l w v ν μ
  have hρ : ∀ i, Name_d M B (ρ.bound i) := Fin.cases hμ.1 (Fin.cases hν.1 (Fin.cases hvN (fun _ => hwN)))
  apply forces_countable_l O hZF e he hsub_body_m hsub_body_closed_l ρ hρ hm.1 hm.2.1
  intro U hU hq η hη
  have hbU := hU.upward q b hq hb hqb
  let E := extension_l M hZF B R B U
  let J := kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
  have hE := preserves_zf_l O hZF hU
  obtain ⟨g, Y, Z, ω', c', T', d', S', hval, hmem, hinj, hreg, hH', hY, hZ, hω', _, hn', hM', hSub', hElem'⟩ :=
    hg i B R q hi hiN hiB hiR O hm U hU hq hbU
  have hYeq : Y = η.bound 1 := hE.1.eq_of_same_members _ _
    (fun x => (hY x).trans (ng_value_l O hZF hU hν (hη 1) x).symm)
  have hZeq : Z = η.bound 0 := hE.1.eq_of_same_members _ _
    (fun x => (hZ x).trans (ng_value_l O hZF hU hμ (hη 0) x).symm)
  subst Y Z
  have hωe : E.IsOmega (g ω) := image_omega_l (hEN := hE.1) g hinj hmem hZF
    (internal_foundation_l O hZF hU) hω (fun A => KP.difference_exists_d (ZF.modelsKP hE) A (g ω))
  have heω : g ω = η.bound 3 := qval_unique_l (hval ω w hw) (hη 3)
  have heχ : g χ = η.bound 2 := qval_unique_l (hval χ v hv) (hη 2)
  have hωη : E.IsOmega (η.bound 3) := heω ▸ hωe
  have hωeq : ω' = η.bound 3 := hE.1.eq_of_same_members _ _
    (fun x => ⟨hω'.2 (η.bound 3) hωη.1 x, hωη.2 ω' hω'.1 x⟩)
  subst ω'
  apply (hsub_sat_l J hE.1 η (.bound 3) (.bound 2) (.bound 1) .newest).mpr
  change Hsub_d J (η.bound 3) (η.bound 2) (η.bound 1) (η.bound 0)
  exact ⟨hωη, heχ ▸ hreg, heω ▸ heχ ▸ (image_member_l g hinj hmem).mpr hωχ,
    heχ ▸ hH', hn', c', T', d', S', hM', hSub', hElem'⟩

/-- 一次取得共同 N 及其每个成员阶段、每个主条件的内部 H(χ) 提升力迫证书。 -/
theorem ng_family_forcing_l {ω δ F G b A} (hω : M.IsOmega ω)
    (hF : M.IsSetFunction I F) (hG : M.IsSetFunction I G) (ha : M.CardinalLessOrEqual I A ω) :
    ∃ χ X N w v, Hsub_d I ω χ X N ∧ M.MemberSubset A N ∧
      M.mem F N ∧ M.mem G N ∧ M.mem δ N ∧ M.mem b N ∧ Hlift_d M ω δ F G b χ X N w v := by
  let ρ : Env M 6 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push δ).push F).push G).push b).push A
  let φ : Formula 1 6 := .conj (Formula.isOmega (.bound 5))
    (.conj (Formula.isFunction kpair_convention_l (.bound 3))
    (.conj (Formula.isFunction kpair_convention_l (.bound 2))
      (Formula.cardinalLessOrEqual kpair_convention_l .newest (.bound 5))))
  let ψ : Formula 1 6 := .existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (hsub_m (𝒞 := kpair_convention_l) (.bound 10) (.bound 4) (.bound 3) (.bound 2))
    (.conj (Formula.subset (.bound 5) (.bound 2))
    (.conj (.mem (.bound 8) (.bound 2)) (.conj (.mem (.bound 7) (.bound 2))
    (.conj (.mem (.bound 9) (.bound 2)) (.conj (.mem (.bound 6) (.bound 2))
      (hlift_m (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)))))))))))
  have hφ : φ.FreeClosed := by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]
  have hψ : ψ.FreeClosed := by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed]
  have raw (K : SetTheory.Structure.{u}) (hK : K.Models ZFC) (η : Env K 6) : Formula.satisfies η φ ↔
      let J := kpair_interpretation_l K hK.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hK)))
      K.IsOmega (η.bound 5) ∧ K.IsSetFunction J (η.bound 3) ∧ K.IsSetFunction J (η.bound 2) ∧
        K.CardinalLessOrEqual J (η.bound 0) (η.bound 5) := by
    let J := kpair_interpretation_l K hK.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hK)))
    simp only [φ, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
      Formula.satisfies_isFunction_iff J hK.1, Formula.satisfies_cardinalLessOrEqual_iff J hK.1]
    rfl
  have result (K : SetTheory.Structure.{u}) (hK : K.Models ZFC) (η : Env K 6) : Formula.satisfies η ψ ↔
      let J := kpair_interpretation_l K hK.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hK)))
      ∃ χ X N w v, Hsub_d J (η.bound 5) χ X N ∧ K.MemberSubset (η.bound 0) N ∧
        K.mem (η.bound 3) N ∧ K.mem (η.bound 2) N ∧ K.mem (η.bound 4) N ∧ K.mem (η.bound 1) N ∧
        Hlift_d K (η.bound 5) (η.bound 4) (η.bound 3) (η.bound 2) (η.bound 1) χ X N w v := by
    let J := kpair_interpretation_l K hK.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hK)))
    simp only [ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, hsub_sat_l J hK.1,
      Formula.satisfies_subset_iff, Formula.satisfies_mem_iff, hlift_sat_l hK.1]
    rfl
  apply (result M hZFC ρ).mp
  apply FirstOrderSemantics.countable_consequence_l (Γ := ZFC) φ ψ hφ hψ
    (fun K hK e he η hp => ?_) hZFC ρ ((raw M hZFC ρ).mpr ⟨hω, hF, hG, ha⟩)
  obtain ⟨hω', hF', hG', ha'⟩ := (raw K hK η).mp hp
  exact (result K hK η).mpr (countable_hlift_l hK e he hω' hF' hG' ha')

end YesMetaZFC.Model.Forcing.Internal
