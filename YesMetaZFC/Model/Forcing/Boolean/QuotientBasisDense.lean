import YesMetaZFC.Model.Forcing.Boolean.QuotientBasis

/-! # 旧稠密集在商的旧条件表示上仍稠密 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
variable {j : M.Domain → N.Domain} (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
variable {P R z C Γ E : M.Domain} {D B S F : N.Domain}
include hM hN inj full

theorem Qb_d.dense_set_l (k : Qb_d j C R Γ D B S F) (O : Cond_order_d M P R z)
    (cone : Ropen_d P R z C) (graph : ∀ p Y, Entry_d M p Y Γ → Rpr_d P R z p Y)
    (trace : Qtrace_d j P R z Γ D)
    (dense : ∀ p, M.mem p C → ∃ q, Below_d M P R z q p ∧ M.mem q E) :
    ∀ p, N.mem p B → Dense_d N B S B (fun q => N.mem q (j E)) p := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  intro p _ r hr
  obtain ⟨q,hq,rfl,Y,qY,YD⟩ := (k.carrier r).mp hr.1
  let ρ : Env M 3 := ⟨fun i => [E,R,q].get i,fun _ => E⟩
  let φ : UnarySchema 3 := { body := .conj (.mem .newest (.bound 1)) (entry_m .newest (.bound 3) (.bound 2)) }
  obtain ⟨E₀,members⟩ := ZF.separation_exists_d hM φ ρ C
  have read s : M.mem s E₀ ↔ M.mem s C ∧ M.mem s E ∧ Entry_d M s q R := by
    apply (members s).trans (and_congr_right fun _ => ?_)
    simp only [φ,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,entry_sat_l M hM.1]
    rfl
  obtain ⟨s,Z,sE,_,sZ,ZD⟩ := trace E₀ Y YD (by
    intro t tY
    have pos := (graph q Y qY).1.1 t tY
    obtain ⟨v,vt,vq⟩ := (graph q Y qY).dense_l hM O tY t (below_refl_l O pos.1 pos.2)
    have vc := cone.2.1 q v (cone.1 q hq).1 ⟨vt.1,vt.2.1,vq⟩ hq
    obtain ⟨s,sv,sE⟩ := dense v vc
    have sc := cone.2.1 v s vt.1 sv vc
    exact ⟨s,below_trans_l O pos.1 sv vt,(read s).mpr ⟨sc,sE,O.trans s v q sv.1 vt.1 (cone.1 q hq).1 sv.2.2 vq⟩⟩)
  obtain ⟨sc,se,sq⟩ := (read s).mp sE
  have sb := (k.old_l inj s).mpr ⟨sc,Z,sZ,ZD⟩
  exact ⟨j s,⟨sb,fun eq => KP.mem_irrefl_d (ZF.modelsKP hN) B (eq ▸ sb),
    (k.order (j s) (j q)).mpr ⟨sb,hr.1,(entry s q R).mp sq⟩⟩,(image_member_l j inj full).mpr se⟩

end YesMetaZFC.Model.Forcing.Internal
