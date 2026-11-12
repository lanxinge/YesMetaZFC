import YesMetaZFC.Model.Forcing.Boolean.ConditionValue

/-! # 原泛型在局部正则开完备化中的实际泛型

内部稠密族先取并集，再回到原条件序命中；因此结论量化完备化上的全部旧稠密集。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
include hZF

theorem ropen_condition_refine_l {B R z p U X t : M.Domain} (O : Cond_order_d M B R z)
    (hp : M.mem p B) (hz : p ≠ z)
    (minimal : ∀ V, Ropen_d B R z V → M.mem p V → M.MemberSubset U V)
    (regular : Ropen_d B R z X) (sub : M.MemberSubset X U) (ht : M.mem t X) :
    ∃ s, Below_d M B R z s p ∧ M.mem s X := by
  let ρ : Env M 4 := ⟨fun i => [B,R,z,p].get i,fun _ => B⟩
  let φ : UnarySchema 4 := { body := below_m (.bound 1) (.bound 2) (.bound 3) .newest (.bound 4) }
  obtain ⟨D,mem⟩ := ZF.separation_exists_d hZF φ ρ B
  have read q : M.mem q D ↔ Below_d M B R z q p :=
    ((mem q).trans (and_congr_right fun _ => below_sat_l M hZF.1 ..)).trans ⟨And.right,fun h => ⟨h.1,h⟩⟩
  obtain ⟨V,hV,values⟩ := ropen_closure_l hZF O D
  have pV := (values p).mpr ⟨hp,hz,fun q hq => ⟨q,below_refl_l O hq.1 hq.2.1,(read q).mpr hq⟩⟩
  have ht' := regular.1 t ht
  obtain ⟨s,st,sD⟩ := ((values t).mp (minimal V hV pV t (sub t ht))).2.2 t (below_refl_l O ht'.1 ht'.2)
  exact ⟨s,(read s).mp sD,regular.2.1 t s ht'.1 st ht⟩

theorem ropen_local_generic_l {B R z C K S e : M.Domain} (O : Cond_order_d M B R z)
    (family : ∀ X, M.mem X K ↔ Ropen_d B R z X ∧ M.MemberSubset X C)
    (order : ∀ X Y, M.mem X K → M.mem Y K → (Entry_d M X Y S ↔ M.MemberSubset X Y))
    (empty : ∀ p, ¬ M.mem p e) (cone : Ropen_d B R z C)
    {G : M.Domain → Prop} (generic : Generic_d M B R z G) (hitC : ∃ p, G p ∧ M.mem p C) :
    Generic_d M K S e (fun X => M.mem X K ∧ ∃ p, G p ∧ M.mem p X) := by
  have hc := (family C).mpr ⟨cone,fun _ h => h⟩
  have nonempty {X} (nz : X ≠ e) : ∃ p, M.mem p X := by
    apply Classical.byContradiction
    intro no
    exact nz (hZF.1.eq_of_same_members X e (fun p => ⟨fun hp => (no ⟨p,hp⟩).elim,fun hp => (empty p hp).elim⟩))
  have inter {X Y} (hx : M.mem X K) (hy : M.mem Y K) :
      ∃ Z, M.mem Z K ∧ ∀ p, M.mem p Z ↔ M.mem p X ∧ M.mem p Y := by
    obtain ⟨Z,hZ,values⟩ := ropen_inter_l hZF ((family X).mp hx).1 ((family Y).mp hy).1
    exact ⟨Z,(family Z).mpr ⟨hZ,fun p hp => ((family X).mp hx).2 p ((values p).mp hp).1⟩,values⟩
  refine ⟨?_,⟨C,hc,hitC⟩,?_,?_,?_⟩
  · rintro X ⟨hx,p,_,px⟩
    exact ⟨hx,fun eq => empty p (eq ▸ px)⟩
  · rintro X Y ⟨hx,p,hp,px⟩ hy xy
    exact ⟨hy,p,hp,(order X Y hx hy).mp xy p px⟩
  · rintro X Y ⟨hx,hitX⟩ ⟨hy,hitY⟩
    obtain ⟨Z,hz,values⟩ := inter hx hy
    exact ⟨Z,⟨hz,(ropen_hit_inter_l ((family X).mp hx).1 ((family Y).mp hy).1 values generic).mpr ⟨hitX,hitY⟩⟩,
      (order Z X hz hx).mpr (fun p hp => ((values p).mp hp).1),
      (order Z Y hz hy).mpr (fun p hp => ((values p).mp hp).2)⟩
  · rintro X ⟨hx,r,hr,rx⟩ D dense
    obtain ⟨E,cut⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) D K
    obtain ⟨U,union⟩ := KP.exists_union (ZF.modelsKP hZF) E
    have density : Dense_d M B R z (fun q => M.mem q U) r := by
      intro q hq
      have qx := ((family X).mp hx).1.2.1 r q (generic.proper r hr).1 hq rx
      obtain ⟨A,regular,qa,minimal⟩ := ropen_condition_l hZF O hq.1 hq.2.1
      have ax := minimal X ((family X).mp hx).1 qx
      have ha := (family A).mpr ⟨regular,fun p hp => ((family X).mp hx).2 p (ax p hp)⟩
      have nz : A ≠ e := fun eq => empty q (eq ▸ qa)
      obtain ⟨Z,hz,zd⟩ := dense A ⟨ha,nz,(order A X ha hx).mpr ax⟩
      obtain ⟨t,ht⟩ := nonempty hz.2.1
      obtain ⟨s,hs,sz⟩ := ropen_condition_refine_l hZF O hq.1 hq.2.1 minimal
        ((family Z).mp hz.1).1 ((order Z A hz.1 ha).mp hz.2.2) ht
      exact ⟨s,hs,(union s).mpr ⟨Z,(cut Z).mpr ⟨zd,hz.1⟩,sz⟩⟩
    obtain ⟨q,hq,qu⟩ := generic.meets r hr U density
    obtain ⟨Z,hz,qz⟩ := (union q).mp qu
    exact ⟨Z,⟨((cut Z).mp hz).2,q,hq,qz⟩,((cut Z).mp hz).1⟩

end YesMetaZFC.Model.Forcing.Internal
