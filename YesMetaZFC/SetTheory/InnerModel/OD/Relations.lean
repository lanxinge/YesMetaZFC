import YesMetaZFC.SetTheory.InnerModel.OD.Separation
import YesMetaZFC.SetTheory.FunctionConstruction

/-! # OD[A] 中的积与可定义关系集合化 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem ob_product_l (A : M.Domain) {X Y P} (hX : Ob_d A X) (hY : Ob_d A Y)
    (hP : M.IsCartesianProduct I P X Y) : Ob_d A P := by
  let ρ : Env M 2 := (⟨fun _ => Y, fun _ => Y⟩ : Env M 1).push X
  let φ : UnarySchema 2 := {
    body := Formula.isCartesianProduct kpair_convention_l .newest (.bound 1) (.bound 2) }
  exact ob_closed_l hZF A φ ρ (Fin.cases hX (fun _ => hY)) (fun Q =>
    (Formula.satisfies_isCartesianProduct_iff I _ _ _ _).trans
      ⟨fun hQ => hZF.1.eq_of_same_members Q P (fun p => (hQ p).trans (hP p).symm),
        fun he => he.symm ▸ hP⟩)

/-- 任意原二元公式在可定义载体上给出实际 OD[A] 关系集。 -/
theorem ob_relation_l (A : M.Domain) {n} (φ : BinarySchema n) (ρ : Env M n)
    (hρ : ∀ i, Ob_d A (ρ.bound i)) {C} (hC : Ob_d A C) :
    ∃ R, Ob_d A R ∧ M.IsSetRelationOn I R C ∧
      ∀ a b, Rd_entry_d a b R ↔ M.mem a C ∧ M.mem b C ∧ φ.denote ρ a b := by
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I C C
  obtain ⟨R, hRo, hr⟩ := oa_separation_l hZF false A (UnarySchema.relationMember kpair_convention_l φ) ρ
    (fun i => oa_bracket_l.mpr (hρ i)) (oa_bracket_l.mpr (ob_product_l hZF A hC hC hP))
  have mem p : M.mem p R ↔ ∃ a, M.mem a C ∧ ∃ b, M.mem b C ∧
      KPair_d M p a b ∧ φ.denote ρ a b := by
    rw [hr p, hP p, UnarySchema.denote, Formula.satisfies_relationMember_iff I]
    constructor
    · rintro ⟨⟨a, ha, b, hb, hp⟩, c, d, hq, hcd⟩
      obtain ⟨rfl, rfl⟩ := (I).injective hp hq
      exact ⟨a, ha, b, hb, hp, hcd⟩
    · exact fun ⟨a, ha, b, hb, hp, hab⟩ => ⟨⟨a, ha, b, hb, hp⟩, a, b, hp, hab⟩
  have entry a b : Rd_entry_d a b R ↔ M.mem a C ∧ M.mem b C ∧ φ.denote ρ a b := by
    constructor
    · rintro ⟨p, hp, hpR⟩
      obtain ⟨c, hc, d, hd, hq, hcd⟩ := (mem p).mp hpR
      obtain ⟨rfl, rfl⟩ := (I).injective hp hq
      exact ⟨hc, hd, hcd⟩
    · rintro ⟨ha, hb, hab⟩
      obtain ⟨p, hp⟩ := (I).total a b
      exact ⟨p, hp, (mem p).mpr ⟨a, ha, b, hb, hp, hab⟩⟩
  refine ⟨R, oa_bracket_l.mp hRo, ⟨?_, fun a b h => ⟨((entry a b).mp h).1, ((entry a b).mp h).2.1⟩⟩, entry⟩
  intro p hp
  obtain ⟨a, _, b, _, hab, _⟩ := (mem p).mp hp
  exact ⟨a, b, hab⟩

end YesMetaZFC.SetTheory.InnerModel
