import YesMetaZFC.SetTheory.InnerModel.Recursion.Certificate

/-! # 内部成员递归的一致性

两个传递域上的证书在公共输入处具有同一值。归纳只施加于实际的值关系公式，
所以不要求背景成员关系在 Lean 中良基。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rc_value_unique_l (hM : M.Models KPi) {n} (φ : S1_binary n) (ρ : Env M n)
    (hu : ∀ F y z, φ.schema.denote ρ F y → φ.schema.denote ρ F z → y = z)
    {x y z : M.Domain} (hy : Rc_value_d φ ρ x y) (hz : Rc_value_d φ ρ x z) : y = z := by
  obtain ⟨hKP, hi⟩ := KPi.models_iff_l.mp hM
  let ψ : UnarySchema n := {
    body := .forallE (.forallE (.imp
      (.conj (binary_pred_m (rc_value_s φ).schema (fun i => .bound ⟨i.val + 3, by omega⟩) (.bound 2) (.bound 1))
        (binary_pred_m (rc_value_s φ).schema (fun i => .bound ⟨i.val + 3, by omega⟩) (.bound 2) .newest))
      (Formula.extensionalEq (.bound 1) .newest))) }
  have hψ a : ψ.denote ρ a ↔ ∀ b c, Rc_value_d φ ρ a b → Rc_value_d φ ρ a c → b = c := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_conj_iff, binary_pred_sat_l, rc_value_sat_l hKP.1, Formula.satisfies_extensionalEq_iff_eq hKP.1]
    exact ⟨fun h b c hb hc => h b c ⟨hb, hc⟩, fun h b c ⟨hb, hc⟩ => h b c hb hc⟩
  apply (hψ x).mp (hi ψ ρ ?_ x) y z hy hz
  intro a ih
  apply (hψ a).mpr
  rintro b c ⟨T, A, F, hF, ha, hb⟩ ⟨U, B, G, hG, ha', hc⟩
  obtain ⟨R, _, hR, hr⟩ := hF.step a ha
  obtain ⟨S, _, hS, hs⟩ := hG.step a ha'
  have hRF := res0_restriction_l hKP hF.function hR
  have hSG := res0_restriction_l hKP hG.function hS
  have he : R = S := by
    apply hRF.1.eq_of_pairMember_iff hKP.1 hSG.1
    intro t v
    rw [hRF.2, hSG.2]
    apply and_congr_right
    intro ht
    have hf := hF.hereditary a ha t ht
    have hg := hG.hereditary a ha' t ht
    constructor
    · intro hv
      obtain ⟨w, _, hw⟩ := hG.function.2.1 t hg
      have he := (hψ t).mp (ih t ht) v w (hF.value_l hv) (hG.value_l hw)
      exact he.symm ▸ hw
    · intro hv
      obtain ⟨w, _, hw⟩ := hF.function.2.1 t hf
      have he := (hψ t).mp (ih t ht) v w (hG.value_l hv) (hF.value_l hw)
      exact he.symm ▸ hw
  subst S
  obtain ⟨w, _, hw⟩ := hr b (hF.function.bound_l hb).2 hb
  obtain ⟨v, _, hv⟩ := hs c (hG.function.bound_l hc).2 hc
  exact hu R b c ((φ.sat_l ρ R b).mpr ⟨w, hw⟩) ((φ.sat_l ρ R c).mpr ⟨v, hv⟩)

end YesMetaZFC.SetTheory.InnerModel
