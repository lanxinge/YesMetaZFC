import YesMetaZFC.Model.Forcing.Boolean.NameLocalization
import YesMetaZFC.Model.Forcing.Extension.Generic

/-! # 主正则开集的泛型读取与可数反射中的序判据 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {B R z : M.Domain} (O : Cond_order_d M B R z)
include hZF O

theorem ropen_condition_hit_l {p C : M.Domain} (hp : M.mem p B) (hz : p ≠ z)
    (pC : M.mem p C) (minimal : ∀ V, Ropen_d B R z V → M.mem p V → M.MemberSubset C V)
    {G : M.Domain → Prop} (generic : Generic_d M B R z G) :
    (∃ q, G q ∧ M.mem q C) ↔ G p := by
  let ρ : Env M 4 := ⟨fun i => [B,R,z,p].get i,fun _ => B⟩
  let φ : UnarySchema 4 := { body := below_m (.bound 1) (.bound 2) (.bound 3) .newest (.bound 4) }
  obtain ⟨D,members⟩ := ZF.separation_exists_d hZF φ ρ B
  have read q : M.mem q D ↔ Below_d M B R z q p :=
    ((members q).trans (and_congr_right fun _ => below_sat_l M hZF.1 ..)).trans ⟨And.right,fun h => ⟨h.1,h⟩⟩
  obtain ⟨V,regular,values⟩ := ropen_closure_l hZF O D
  have pV := (values p).mpr ⟨hp,hz,fun q hq => ⟨q,below_refl_l O hq.1 hq.2.1,(read q).mpr hq⟩⟩
  constructor
  · rintro ⟨q,hq,qC⟩
    obtain ⟨r,hr,rD⟩ := generic.meets q hq D ((values q).mp (minimal V regular pV q qC)).2.2
    exact generic.upward r p hr hp ((read r).mp rD).2.2
  · exact fun h => ⟨p,h,pC⟩

omit hZF O in
theorem ropen_hit_inter_l {A C V : M.Domain} (left : Ropen_d B R z A) (right : Ropen_d B R z C)
    (inter : ∀ p, M.mem p V ↔ M.mem p A ∧ M.mem p C)
    {G : M.Domain → Prop} (generic : Generic_d M B R z G) :
    (∃ p, G p ∧ M.mem p V) ↔ (∃ p, G p ∧ M.mem p A) ∧ ∃ p, G p ∧ M.mem p C := by
  constructor
  · rintro ⟨p,hp,hV⟩
    exact ⟨⟨p,hp,((inter p).mp hV).1⟩,p,hp,((inter p).mp hV).2⟩
  · rintro ⟨⟨p,hp,pa⟩,q,hq,qc⟩
    obtain ⟨r,hr,rp,rq⟩ := generic.directed p q hp hq
    have pos := generic.proper r hr
    exact ⟨r,hr,(inter r).mpr ⟨left.2.1 p r (generic.proper p hp).1 ⟨pos.1,pos.2,rp⟩ pa,
      right.2.1 q r (generic.proper q hq).1 ⟨pos.1,pos.2,rq⟩ qc⟩⟩

theorem ropen_countable_le_l (f : Nat → M.Domain) (onto : Function.Surjective f) {p C X Y : M.Domain}
    (hp : M.mem p B) (hz : p ≠ z) (pC : M.mem p C)
    (minimal : ∀ V, Ropen_d B R z V → M.mem p V → M.MemberSubset C V)
    (left : Ropen_d B R z X) (right : Ropen_d B R z Y) (sub : M.MemberSubset X C)
    (test : ∀ G, Generic_d M B R z G → G p → (∃ q, G q ∧ M.mem q X) → ∃ q, G q ∧ M.mem q Y) :
    M.MemberSubset X Y := by
  intro x hx
  apply Classical.byContradiction
  intro hn
  obtain ⟨q,hq,neg⟩ := regular_neg_witness_l right.2 (left.1 x hx).1 (left.1 x hx).2 hn
  obtain ⟨G,generic,qG⟩ := internal_generic_l O f onto hq.1 hq.2.1
  have qX := left.2.1 x q (left.1 x hx).1 hq hx
  have pG := (ropen_condition_hit_l hZF O hp hz pC minimal generic).mp ⟨q,qG,sub q qX⟩
  obtain ⟨r,rG,rY⟩ := test G generic pG ⟨q,qG,qX⟩
  obtain ⟨s,sG,sq,sr⟩ := generic.directed q r qG rG
  have pos := generic.proper s sG
  exact neg s ⟨pos.1,pos.2,sq⟩ (right.2.1 r s (generic.proper r rG).1 ⟨pos.1,pos.2,sr⟩ rY)

end YesMetaZFC.Model.Forcing.Internal
