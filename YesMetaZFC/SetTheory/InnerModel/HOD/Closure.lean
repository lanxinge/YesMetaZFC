import YesMetaZFC.SetTheory.InnerModel.HOD.Relativization
import YesMetaZFC.SetTheory.InnerModel.OD.Separation

/-! # 遗传参数类的配对、并集与内部幂集 -/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem ha_pair_l (hZF : M.Models ZF) {k A x y} (hx : Ha_d (M := M) k A x) (hy : Ha_d k A y) :
    ∃ p, Ha_d k A p ∧ ∀ z, M.mem z p ↔ z = x ∨ z = y := by
  obtain ⟨p, hp⟩ := KP.exists_pair (ZF.modelsKP hZF) x y
  let φ : UnarySchema 2 := { body := Formula.isUnorderedPair .newest (.bound 1) (.bound 2) }
  let ρ : Env M 2 := ⟨Fin.cases x (fun _ => y), fun _ => x⟩
  have ho : Oa_d k A p := oa_unique_l hZF k A φ ρ (Fin.cases (ha_oa_l hx) (fun _ => ha_oa_l hy))
    (fun q => (pair_sat_l M hZF.1 _ _ _ _).trans
      ⟨fun hq => hZF.1.eq_of_same_members q p (fun z => (hq z).trans (hp z).symm), fun he => he.symm ▸ hp⟩)
  exact ⟨p, ha_of_members_l hZF ho (fun z hz => ((hp z).mp hz).elim (fun he => he.symm ▸ hx) (fun he => he.symm ▸ hy)), hp⟩

theorem ha_union_l (hZF : M.Models ZF) {k A X} (hX : Ha_d (M := M) k A X) :
    ∃ U, Ha_d k A U ∧ ∀ z, M.mem z U ↔ ∃ y, M.mem y X ∧ M.mem z y := by
  obtain ⟨U, hu⟩ := KP.exists_union (ZF.modelsKP hZF) X
  let φ : UnarySchema 1 := { body := Formula.isUnion .newest (.bound 1) }
  let ρ : Env M 1 := ⟨fun _ => X, fun _ => X⟩
  have ho : Oa_d k A U := oa_unique_l hZF k A φ ρ (fun _ => ha_oa_l hX)
    (fun V => (Formula.satisfies_isUnion_iff _ _ _).trans
      ⟨fun hv => hZF.1.eq_of_same_members V U (fun z => (hv z).trans (hu z).symm), fun he => he.symm ▸ hu⟩)
  exact ⟨U, ha_of_members_l hZF ho (fun z hz => (hu z).mp hz |>.elim fun y hy =>
    ha_trans_l (ha_trans_l hX hy.1) hy.2), hu⟩

theorem ha_power_l (hZF : M.Models ZF) {k A X} (hX : Ha_d (M := M) k A X) :
    ∃ S, Ha_d k A S ∧ ∀ z, M.mem z S ↔ M.MemberSubset z X ∧ Ha_d k A z := by
  obtain ⟨P, hp⟩ := ZF.exists_powerSet hZF X
  let φ : UnarySchema 1 := { body := Formula.isPowerSet .newest (.bound 1) }
  let ρ : Env M 1 := ⟨fun _ => X, fun _ => X⟩
  have ho : Oa_d k A P := oa_unique_l hZF k A φ ρ (fun _ => ha_oa_l hX)
    (fun Q => (Formula.satisfies_isPowerSet_iff _ _ _).trans
      ⟨fun hq => hZF.1.eq_of_same_members Q P (fun z => (hq z).trans (hp z).symm), fun he => he.symm ▸ hp⟩)
  let ψ : UnarySchema 1 := { body := ha_m k (.bound 1) .newest }
  obtain ⟨S, hs, hS'⟩ := oa_separation_l hZF k A ψ ⟨fun _ => A, fun _ => A⟩ (fun _ => oa_parameter_l hZF k A) ho
  have hS z : M.mem z S ↔ M.MemberSubset z X ∧ Ha_d k A z :=
    (hS' z).trans (and_congr (hp z) (ha_sat_l hZF.1 _ _ _ _))
  exact ⟨S, ha_of_members_l hZF hs (fun z hz => ((hS z).mp hz).2), hS⟩

end YesMetaZFC.SetTheory.InnerModel
