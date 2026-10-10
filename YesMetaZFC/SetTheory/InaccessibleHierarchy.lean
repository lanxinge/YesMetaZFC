import YesMetaZFC.SetTheory.Card.PowerBound
import YesMetaZFC.SetTheory.HereditaryClosure
import YesMetaZFC.SetTheory.CumulativeClosure

/-! # 不可达层的遗传大小刻画

按实际序数归纳，以 Vα = ⋃β<α P(Vβ) 一次处理零、后继和极限。
强极限性处理幂集，正则性处理小并，因而 Hδ 与 Vδ 是同一个实际集合。
-/
namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem inaccessible_level_small_l (hZFC : M.Models ZFC) {ω δ α V : M.Domain}
    (hω : M.IsOmega ω) (hωδ : M.mem ω δ) (hr : M.IsRegularCardinal I δ)
    (hs : M.IsStrongLimitCardinal I δ) (hα : M.mem α δ) (hV : V_d I α V) :
    ∃ μ, M.mem μ δ ∧ M.CardinalLessOrEqual I V μ := by
  let hZF := models_zf_l hZFC
  let ρ : Env M 1 := ⟨fun _ => δ, fun _ => δ⟩
  let φ : UnarySchema 1 := { body := .imp (.mem .newest (.bound 1)) (.forallE
    (.imp (v_m 𝒞 (.bound 1) .newest) (Formula.existsMem (.bound 2)
      (Formula.cardinalLessOrEqual 𝒞 (.bound 1) .newest)))) }
  have sat a : φ.denote ρ a ↔ M.mem a δ → ∀ W, V_d I a W →
      ∃ μ, M.mem μ δ ∧ M.CardinalLessOrEqual I W μ := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff, v_sat_l I hZF.1, Formula.satisfies_existsMem_iff,
      Formula.satisfies_cardinalLessOrEqual_iff I hZF.1]; rfl
  apply (sat α).mp (ZF.mem_ind_l M hZF I φ ρ ?_ α) hα V hV
  intro a ih
  apply (sat a).mpr
  intro ha W hW
  let η : Env M 0 := ⟨Fin.elim0, fun _ => a⟩
  let ψ : BinarySchema 0 := { body := .existsE (.conj (v_m 𝒞 (.bound 2) .newest)
    (Formula.isPowerSet (.bound 1) .newest)) }
  have read β P : ψ.denote η β P ↔ ∃ U, V_d I β U ∧ M.IsPowerSetOf P U := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      v_sat_l I hZF.1, Formula.satisfies_isPowerSet_iff]; rfl
  have total β (hβ : M.mem β a) : ∃ P, ψ.denote η β P := by
    obtain ⟨U, hU⟩ := ZF.v_exists_l I hZF ((v_ordinal_l I hW).mem hβ)
    obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF U
    exact ⟨P, (read β P).mpr ⟨U, hU, hP⟩⟩
  have unique β (_ : M.mem β a) P Q (hp : ψ.denote η β P) (hq : ψ.denote η β Q) : P = Q := by
    obtain ⟨U, hU, hp⟩ := (read β P).mp hp
    obtain ⟨T, hT, hq⟩ := (read β Q).mp hq
    have e := ZF.v_unique_l I hZF hT hU
    subst T
    exact hZF.1.eq_of_same_members P Q fun x => (hp x).trans (hq x).symm
  obtain ⟨B, hb⟩ := ZF.exists_functionalImageOn hZF ψ η a total unique
  obtain ⟨G, hg, gs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η total unique
    (fun β P hβ hp => (hb P).mpr ⟨β, hβ, hp⟩)
  have onto : M.IsSetSurjectiveOnto I G a B := fun P hp =>
    ((hb P).mp hp).elim fun β hβ => ⟨β, hβ.1, (gs β P).mpr hβ⟩
  obtain ⟨id, hid⟩ := ZF.exists_identityBijection hZF I a
  have hB := ZF.ordinal_image_bound_l I hZF (v_ordinal_l I hW) ⟨id, hid.1⟩ hg onto
  have union : M.IsUnionOf W B := fun x => (ZF.v_unfold_l I hZF hW x).trans
    ⟨fun ⟨β, U, hβ, hU, hx⟩ => by
      obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF U
      exact ⟨P, (hb P).mpr ⟨β, hβ, (read β P).mpr ⟨U, hU, hP⟩⟩, (hP x).mpr hx⟩,
     fun ⟨P, hp, hx⟩ => by
      obtain ⟨β, hβ, hp⟩ := (hb P).mp hp
      obtain ⟨U, hU, hP⟩ := (read β P).mp hp
      exact ⟨β, U, hβ, hU, (hP x).mp hx⟩⟩
  apply small_union_l I hZFC hω hr hωδ ha hB union
  intro P hp
  obtain ⟨β, hβ, hp⟩ := (hb P).mp hp
  obtain ⟨U, hU, hP⟩ := (read β P).mp hp
  obtain ⟨μ, hμ, hu⟩ := (sat β).mp (ih β hβ) (hr.isCardinal.1.transitive a ha β hβ) U hU
  exact ZF.strong_power_bound_l I hZF hs hμ hu hP

theorem inaccessible_hereditary_l (hZFC : M.Models ZFC) {ω δ V : M.Domain}
    (hω : M.IsOmega ω) (hωδ : M.mem ω δ) (hr : M.IsRegularCardinal I δ)
    (hs : M.IsStrongLimitCardinal I δ) (hV : V_d I δ V) : H_d I δ V := by
  let hZF := models_zf_l hZFC
  intro x
  constructor
  · intro hx
    obtain ⟨α, W, hα, hW, hx⟩ := (ZF.v_limit_mem_l I hZF hV hr.isLimitOrdinal.2.2 x).mp hx
    obtain ⟨μ, hμ, hw⟩ := inaccessible_level_small_l I hZFC hω hωδ hr hs hα hW
    exact ZF.hmem_of_transitive_l I hZF (ZF.v_transitive_l I hZF hW) hx hμ hw
  · rintro ⟨T, μ, ht, hμ, htμ⟩
    exact ZF.rk_transitive_bound_l I hZF ht.1 hr.isCardinal hμ htμ hV x ht.2.1

end YesMetaZFC.SetTheory.ZFC
