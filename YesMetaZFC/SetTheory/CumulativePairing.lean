import YesMetaZFC.SetTheory.CumulativeFunction

/-! # 累积层级不依赖函数图的配对约定

对实际层级公式作内部成员归纳；两侧在每一较早层取同一个幂集并。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 𝒟 : OrderedPairConvention}
  (I : 𝒞.Interpretation M) (J : 𝒟.Interpretation M)

theorem v_pairing_unique_l (hZF : M.Models ZF) {α A B : M.Domain}
    (hA : V_d I α A) (hB : V_d J α B) : A = B := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => α⟩
  let φ : UnarySchema 0 := { body := .forallE (.forallE (.imp
    (v_m 𝒞 (.bound 2) (.bound 1)) (.imp (v_m 𝒟 (.bound 2) .newest)
      (Formula.extensionalEq (.bound 1) .newest)))) }
  have read β : φ.denote ρ β ↔ ∀ A B, V_d I β A → V_d J β B → A = B := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      v_sat_l I hZF.1, v_sat_l J hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  apply (read α).mp (ZF.mem_ind_l M hZF I φ ρ ?_ α) A B hA hB
  intro β ih
  apply (read β).mpr
  intro A B ha hb
  apply hZF.1.eq_of_same_members A B
  intro x
  constructor
  · intro hx
    obtain ⟨γ, U, hγ, hu, sub⟩ := (ZF.v_unfold_l I hZF ha x).mp hx
    obtain ⟨W, hw⟩ := ZF.v_exists_l J hZF ((v_ordinal_l I ha).mem hγ)
    exact (ZF.v_unfold_l J hZF hb x).mpr ⟨γ, W, hγ, hw, (read γ).mp (ih γ hγ) U W hu hw ▸ sub⟩
  · intro hx
    obtain ⟨γ, W, hγ, hw, sub⟩ := (ZF.v_unfold_l J hZF hb x).mp hx
    obtain ⟨U, hu⟩ := ZF.v_exists_l I hZF ((v_ordinal_l J hb).mem hγ)
    exact (ZF.v_unfold_l I hZF ha x).mpr ⟨γ, U, hγ, hu, ((read γ).mp (ih γ hγ) U W hu hw).symm ▸ sub⟩

theorem v_pairing_l (hZF : M.Models ZF) {α A : M.Domain} : V_d I α A ↔ V_d J α A := by
  constructor
  · intro h
    obtain ⟨B, hb⟩ := ZF.v_exists_l J hZF (v_ordinal_l I h)
    exact (v_pairing_unique_l I J hZF h hb).symm ▸ hb
  · intro h
    obtain ⟨B, hb⟩ := ZF.v_exists_l I hZF (v_ordinal_l J h)
    exact v_pairing_unique_l I J hZF hb h ▸ hb

end YesMetaZFC.SetTheory
