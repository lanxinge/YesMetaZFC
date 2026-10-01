import YesMetaZFC.Model.Forcing.Proper.Family.ClosedLift
import YesMetaZFC.Model.Forcing.Proper.Family.Syntax

/-! # 指定闭集 N 的全阶段内部提升证书

先在实际可数反射模型中应用全泛型判据，再反射完整的闭包前提及力迫结论。
N 和两张运算图均是有限参数的一部分；反射不会替换正在证明的那个 N。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

private theorem countable_closed_l (e : Nat → M.Domain) (he : Function.Surjective e)
    {ω χ H δ F G b N w v} (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ)
    (hωχ : M.mem ω χ) (hH : H_d I χ H) (hNH : M.MemberSubset N H) (hn : M.CardinalLessOrEqual I N ω)
    (hF : M.IsSetFunction I F) (hG : M.IsSetFunction I G)
    (hB : ∀ i B, M.mem i δ → Entry_d M i B F → M.mem B H)
    (hw : Check_d M b ω w) (hv : Check_d M b χ v) (hc : Ng_closed_d I ω δ F G b H N w) :
    Hlift_d M ω δ F G b χ H N w v := by
  refine ⟨hw, hv, ?_⟩
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
    ng_closed_lift_l O hZFC hU hbU hω hχ hωχ hH (hB i B hi hiB) hNH hn hw hF hG hc hi hiN hiB hiR hm hq
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

theorem ng_closed_forcing_l {ω χ H δ F G b N w v} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hNH : M.MemberSubset N H) (hn : M.CardinalLessOrEqual I N ω)
    (hF : M.IsSetFunction I F) (hG : M.IsSetFunction I G)
    (hB : ∀ i B, M.mem i δ → Entry_d M i B F → M.mem B H)
    (hw : Check_d M b ω w) (hv : Check_d M b χ v) (hc : Ng_closed_d I ω δ F G b H N w) :
    Hlift_d M ω δ F G b χ H N w v := by
  let ρ : Env M 10 := (((((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push χ).push H).push δ).push F).push G).push b).push N).push w).push v
  let φ : Formula 1 10 := .conj (Formula.isOmega (.bound 9))
    (.conj (Formula.isRegularCardinal kpair_convention_l (.bound 8)) (.conj (.mem (.bound 9) (.bound 8))
    (.conj (h_m (𝒞 := kpair_convention_l) (.bound 8) (.bound 7))
    (.conj (Formula.subset (.bound 2) (.bound 7))
    (.conj (Formula.cardinalLessOrEqual kpair_convention_l (.bound 2) (.bound 9))
    (.conj (Formula.isFunction kpair_convention_l (.bound 5))
    (.conj (Formula.isFunction kpair_convention_l (.bound 4))
    (.conj (.forallE (.forallE (.imp (.mem (.bound 1) (.bound 8))
      (.imp (entry_m (.bound 1) .newest (.bound 7)) (.mem .newest (.bound 9))))))
    (.conj (check_m (.bound 3) (.bound 9) (.bound 1)) (.conj (check_m (.bound 3) (.bound 8) .newest)
      (ng_closed_m (.bound 9) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 7) (.bound 2) (.bound 1))))))))))))
  let ψ : Formula 1 10 := hlift_m (.bound 9) (.bound 6) (.bound 5) (.bound 4) (.bound 3)
    (.bound 8) (.bound 7) (.bound 2) (.bound 1) .newest
  have hφ : φ.FreeClosed := by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]
  have hψ : ψ.FreeClosed := by simp -implicitDefEqProofs [ψ]
  have raw (K : SetTheory.Structure.{u}) (hK : K.Models ZFC) (η : Env K 10) : Formula.satisfies η φ ↔
      let J := kpair_interpretation_l K hK.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hK)))
      K.IsOmega (η.bound 9) ∧ K.IsRegularCardinal J (η.bound 8) ∧ K.mem (η.bound 9) (η.bound 8) ∧
      H_d J (η.bound 8) (η.bound 7) ∧ K.MemberSubset (η.bound 2) (η.bound 7) ∧
      K.CardinalLessOrEqual J (η.bound 2) (η.bound 9) ∧ K.IsSetFunction J (η.bound 5) ∧ K.IsSetFunction J (η.bound 4) ∧
      (∀ i B, K.mem i (η.bound 6) → Entry_d K i B (η.bound 5) → K.mem B (η.bound 7)) ∧
      Check_d K (η.bound 3) (η.bound 9) (η.bound 1) ∧ Check_d K (η.bound 3) (η.bound 8) (η.bound 0) ∧
      Ng_closed_d J (η.bound 9) (η.bound 6) (η.bound 5) (η.bound 4) (η.bound 3) (η.bound 7) (η.bound 2) (η.bound 1) := by
    let J := kpair_interpretation_l K hK.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hK)))
    simp only [φ, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
      Formula.satisfies_isRegularCardinal_iff J hK.1, Formula.satisfies_mem_iff, h_sat_l J hK.1,
      Formula.satisfies_subset_iff, Formula.satisfies_cardinalLessOrEqual_iff J hK.1,
      Formula.satisfies_isFunction_iff J hK.1, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      entry_sat_l K hK.1, check_sat_l K hK.1, ng_closed_sat_l J hK.1]
    rfl
  apply (hlift_sat_l hZFC.1 ρ (.bound 9) (.bound 6) (.bound 5) (.bound 4) (.bound 3)
    (.bound 8) (.bound 7) (.bound 2) (.bound 1) .newest).mp
  apply FirstOrderSemantics.countable_consequence_l (Γ := ZFC) φ ψ hφ hψ
    (fun K hK e he η hp => ?_) hZFC ρ ((raw M hZFC ρ).mpr ⟨hω, hχ, hωχ, hH, hNH, hn, hF, hG, hB, hw, hv, hc⟩)
  obtain ⟨hω', hχ', hωχ', hH', hNH', hn', hF', hG', hB', hw', hv', hc'⟩ := (raw K hK η).mp hp
  exact (hlift_sat_l hK.1 η (.bound 9) (.bound 6) (.bound 5) (.bound 4) (.bound 3)
    (.bound 8) (.bound 7) (.bound 2) (.bound 1) .newest).mpr
    (countable_closed_l hK e he hω' hχ' hωχ' hH' hNH' hn' hF' hG' hB' hw' hv' hc')

end YesMetaZFC.Model.Forcing.Internal
