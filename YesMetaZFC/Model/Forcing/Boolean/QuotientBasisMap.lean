import YesMetaZFC.Model.Forcing.Boolean.QuotientBasisDense
import YesMetaZFC.Model.Forcing.Boolean.DenseCompletion

/-! # 商的旧条件表示到布尔商的实际稠密映射

共同布尔加强先取旧共同加强条件的稠密族，再用迹定理保持其首阶段接受性。
因此主正则开图在商中仍反映相容性，适用于尚未分离的原条件序。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
variable {j : M.Domain → N.Domain} (inj : Function.Injective j)
  (full : ∀ a y, N.mem y (j a) ↔ ∃ x, M.mem x a ∧ j x = y)
variable {P R z C L V Γ : M.Domain} {D B S F W : N.Domain}
local notation "I" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
local notation "J" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hN))
include hM hN inj full

theorem Qb_d.map_l (k : Qb_d j C R Γ D B S F) (O : Cond_order_d M P R z)
    (cone : Ropen_d P R z C)
    (family : ∀ X, M.mem X L ↔ Ropen_d P R z X ∧ M.MemberSubset X C)
    (order : ∀ X Y, M.mem X L → M.mem Y L → (Entry_d M X Y V ↔ M.MemberSubset X Y))
    (fn : M.IsSetFunctionFromTo I Γ C L) (graph : ∀ p X, Entry_d M p X Γ → Rpr_d P R z p X)
    (old : ∀ x, N.mem x D → ∃ X, M.mem X L ∧ j X = x)
    (relation : ∀ x y, Entry_d N x y W ↔ N.mem x D ∧ N.mem y D ∧ Entry_d N x y (j V))
    (function : N.IsSetFunctionFromTo J F B D) (trace : Qtrace_d j P R z Γ D) : Dmap_d B S B D W D F := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  have imageFn := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) j inj full fn
  have values {v x} (vx : Entry_d N v x F) : ∃ p X, M.mem p C ∧ Entry_d M p X Γ ∧ j p = v ∧ j X = x := by
    obtain ⟨p,hp,rfl,_⟩ := (k.carrier v).mp ((k.graph v x).mp vx).1
    obtain ⟨X,_,rfl⟩ := (full L x).mp (imageFn.output_mem_of_pairMember ((k.graph (j p) x).mp vx).2)
    exact ⟨p,X,hp,(entry p X Γ).mpr ((k.graph (j p) (j X)).mp vx).2,rfl,rfl⟩
  refine ⟨fun p hp _ => (function.2.2 p hp).imp fun x hx => hx.2,?_,function.1.2,?_,?_,?_⟩
  · intro p x px
    have hp := function.input_mem_of_pairMember px
    have hx := function.output_mem_of_pairMember px
    exact ⟨⟨hp,fun eq => KP.mem_irrefl_d (ZF.modelsKP hN) B (eq ▸ hp)⟩,hx,
      fun eq => KP.mem_irrefl_d (ZF.modelsKP hN) D (eq ▸ hx)⟩
  · intro p q x y px qy pq
    obtain ⟨a,X,ha,aX,rfl,rfl⟩ := values px
    obtain ⟨b,Y,hb,bY,rfl,rfl⟩ := values qy
    have ab := (entry a b R).mpr ((k.order (j a) (j b)).mp pq).2.2
    exact (relation (j X) (j Y)).mpr ⟨function.output_mem_of_pairMember px,function.output_mem_of_pairMember qy,
      (entry X Y V).mp ((order X Y (fn.output_mem_of_pairMember aX) (fn.output_mem_of_pairMember bY)).mpr
        ((graph a X aX).mono_l (graph b Y bY) ⟨(cone.1 a ha).1,(cone.1 a ha).2,ab⟩))⟩
  · intro p q x y px qy cmp
    obtain ⟨a,X,ha,aX,rfl,rfl⟩ := values px
    obtain ⟨b,Y,hb,bY,rfl,rfl⟩ := values qy
    obtain ⟨r,hr,ry⟩ := cmp
    obtain ⟨Z,hZ,rfl⟩ := old r hr.1
    have ZX := (order Z X hZ (fn.output_mem_of_pairMember aX)).mp ((entry Z X V).mpr ((relation (j Z) (j X)).mp hr.2.2).2.2)
    have ZY := (order Z Y hZ (fn.output_mem_of_pairMember bY)).mp ((entry Z Y V).mpr ((relation (j Z) (j Y)).mp ry).2.2)
    let ρ : Env M 3 := ⟨fun i => [R,a,b].get i,fun _ => R⟩
    let φ : UnarySchema 3 := { body := .conj (entry_m .newest (.bound 2) (.bound 1)) (entry_m .newest (.bound 3) (.bound 1)) }
    obtain ⟨E,members⟩ := ZF.separation_exists_d hM φ ρ C
    have read r : M.mem r E ↔ M.mem r C ∧ Entry_d M r a R ∧ Entry_d M r b R := by
      apply (members r).trans (and_congr_right fun _ => ?_)
      simp only [φ,Formula.satisfies_conj_iff,entry_sat_l M hM.1]; rfl
    obtain ⟨s,W,sE,_,sW,WD⟩ := trace E Z hr.1 (by
      intro r rz
      have pos := ((family Z).mp hZ).1.1 r rz
      obtain ⟨s,sr,sa⟩ := (graph a X aX).dense_l hM O (ZX r rz) r (below_refl_l O pos.1 pos.2)
      have sy := (graph b Y bY).1.2.1 r s pos.1 sr (ZY r rz)
      obtain ⟨t,ts,tb⟩ := (graph b Y bY).dense_l hM O sy s (below_refl_l O sr.1 sr.2.1)
      have ta := O.trans t s a ts.1 sr.1 (cone.1 a ha).1 ts.2.2 sa
      exact ⟨t,below_trans_l O pos.1 ts sr,(read t).mpr
        ⟨cone.2.1 a t (cone.1 a ha).1 ⟨ts.1,ts.2.1,ta⟩ ha,ta,tb⟩⟩)
    obtain ⟨sc,sa,sb⟩ := (read s).mp sE
    have hs := (k.old_l inj s).mpr ⟨sc,W,sW,WD⟩
    exact ⟨j s,⟨hs,fun eq => KP.mem_irrefl_d (ZF.modelsKP hN) B (eq ▸ hs),
      (k.order (j s) (j a)).mpr ⟨hs,function.input_mem_of_pairMember px,(entry s a R).mp sa⟩⟩,
      (k.order (j s) (j b)).mpr ⟨hs,function.input_mem_of_pairMember qy,(entry s b R).mp sb⟩⟩
  · intro x hx _
    obtain ⟨X,hX,rfl⟩ := old x hx
    obtain ⟨p,Y,px,_,pY,YD⟩ := trace X X hx (fun p hp =>
      ⟨p,below_refl_l O (((family X).mp hX).1.1 p hp).1 (((family X).mp hX).1.1 p hp).2,hp⟩)
    have hp := (k.old_l inj p).mpr ⟨fn.input_mem_of_pairMember pY,Y,pY,YD⟩
    exact ⟨j p,j Y,(k.graph (j p) (j Y)).mpr ⟨hp,(entry p Y Γ).mp pY⟩,
      (relation (j Y) (j X)).mpr ⟨YD,hx,(entry Y X V).mp ((order Y X (fn.output_mem_of_pairMember pY) hX).mpr
        ((graph p Y pY).2.2 X ((family X).mp hX).1 px))⟩⟩

end YesMetaZFC.Model.Forcing.Internal
