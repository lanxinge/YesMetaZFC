import YesMetaZFC.Model.Forcing.Boolean.PrincipalGraph
import YesMetaZFC.Model.Forcing.Boolean.DenseGround

/-! # 原泛型扩张与局部正则开扩张的识别

正则开区域 C 自身是原条件序的局部稠密子序。其恒等包含和主正则开映射
分别给出两侧扩张同构；两张图的泛型回拉均恰为 G 在 C 上的限制。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem ropen_extension_l {B R z C L V d : M.Domain} (O : Cond_order_d M B R z)
    (cone : Ropen_d B R z C)
    (family : ∀ X, M.mem X L ↔ Ropen_d B R z X ∧ M.MemberSubset X C)
    (order : ∀ X Y, M.mem X L → M.mem Y L → (Entry_d M X Y V ↔ M.MemberSubset X Y))
    (target : BooleanZF.Boolean_d I L V d) (empty : ∀ p, ¬ M.mem p d)
    {G : M.Domain → Prop} (generic : Generic_d M B R z G) (hit : ∃ p, G p ∧ M.mem p C) :
    Miso_over_d (extension_l M hZF B R z G)
      (extension_l M hZF L V d (fun X => M.mem X L ∧ ∃ p, G p ∧ M.mem p X))
      (Gval_d M B R z G) (Gval_d M L V d (fun X => M.mem X L ∧ ∃ p, G p ∧ M.mem p X)) := by
  have OC : Cond_order_d M C R z := {
    refl := fun p hp => O.refl p (cone.1 p hp).1
    trans := fun p q r hp hq hr => O.trans p q r (cone.1 p hp).1 (cone.1 q hq).1 (cone.1 r hr).1
    zero := fun p hp => O.zero p (cone.1 p hp).1 }
  obtain ⟨F,graph,_⟩ := reg_embed_id_l hZF OC
  have inc : Reg_map_d M C R z B R z F := by
    refine ⟨fun p hp nz => ⟨p,(graph p p).mpr ⟨hp,nz,rfl⟩⟩,?_,?_,?_,?_⟩
    · intro p q pq
      obtain ⟨hp,nz,eq⟩ := (graph p q).mp pq
      subst q
      exact ⟨hp,nz,(cone.1 p hp).1,nz⟩
    · intro p q x y px qy pq
      obtain ⟨_,_,eq⟩ := (graph p x).mp px
      subst x
      obtain ⟨_,_,eq⟩ := (graph q y).mp qy
      subst y
      exact pq
    · intro p q x y px qy cmp
      obtain ⟨hp,_,eq⟩ := (graph p x).mp px
      subst x
      obtain ⟨_,_,eq⟩ := (graph q y).mp qy
      subst y
      obtain ⟨r,hr,rq⟩ := cmp
      exact ⟨r,⟨cone.2.1 p r (cone.1 p hp).1 hr hp,hr.2.1,hr.2.2⟩,rq⟩
    · intro x hx nz p y py xy
      obtain ⟨hp,_,eq⟩ := (graph p y).mp py
      subst y
      have xc := cone.2.1 p x (cone.1 p hp).1 ⟨hx,nz,xy⟩ hp
      refine ⟨x,xc,nz,fun r v rv rx => ?_⟩
      obtain ⟨hr,rnz,eq⟩ := (graph r v).mp rv
      subst v
      exact ⟨r,⟨(cone.1 r hr).1,rnz,rx⟩,O.refl r (cone.1 r hr).1⟩
  obtain ⟨p,hp,pC⟩ := hit
  have dense q (hq : Below_d M B R z q p) : ∃ a x, Entry_d M a x F ∧ Entry_d M x q R :=
    ⟨q,q,(graph q q).mpr ⟨cone.2.1 p q (generic.proper p hp).1 hq pC,hq.2.1,rfl⟩,O.refl q hq.1⟩
  have left := inc.dense_ground_l hZF OC O
    (fun q r s qr qs => ((graph q r).mp qr).2.2.trans ((graph q s).mp qs).2.2.symm) generic hp dense
  obtain ⟨J,fn,principal⟩ := rpr_graph_l hZF O cone family
  have OL := cond_order_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) target
  have map : Dmap_d C R z L V d J := by
    refine ⟨fun q hq _ => (fn.2.2 q hq).imp fun X hX => hX.2,?_,fn.1.2,?_,?_,?_⟩
    · intro q X qX
      obtain ⟨hq,h⟩ := (principal q X).mp qX
      exact ⟨⟨hq,(cone.1 q hq).2⟩,fn.output_mem_of_pairMember qX,fun eq => empty q (eq ▸ h.2.1)⟩
    · intro q r X Y qX rY qr
      have hq := (principal q X).mp qX
      have hr := (principal r Y).mp rY
      exact (order X Y (fn.output_mem_of_pairMember qX) (fn.output_mem_of_pairMember rY)).mpr
        (hq.2.mono_l hr.2 ⟨(cone.1 q hq.1).1,(cone.1 q hq.1).2,qr⟩)
    · intro q r X Y qX rY cmp
      obtain ⟨Z,hZ,ZY⟩ := cmp
      have nonempty : ∃ t, M.mem t Z := by
        apply Classical.byContradiction
        intro no
        exact hZ.2.1 (hZF.1.eq_of_same_members Z d (fun t => ⟨fun ht => (no ⟨t,ht⟩).elim,fun ht => (empty t ht).elim⟩))
      obtain ⟨t,ht⟩ := nonempty
      have tx := (order Z X hZ.1 (fn.output_mem_of_pairMember qX)).mp hZ.2.2 t ht
      have ty := (order Z Y hZ.1 (fn.output_mem_of_pairMember rY)).mp ZY t ht
      have ht' := ((family Z).mp hZ.1).1.1 t ht
      obtain ⟨s,st,sq⟩ := ((principal q X).mp qX).2.dense_l hZF O tx t (below_refl_l O ht'.1 ht'.2)
      have sy := ((principal r Y).mp rY).2.1.2.1 t s ht'.1 st ty
      obtain ⟨v,vs,vr⟩ := ((principal r Y).mp rY).2.dense_l hZF O sy s (below_refl_l O st.1 st.2.1)
      have vq := O.trans v s q vs.1 st.1 (cone.1 q ((principal q X).mp qX).1).1 vs.2.2 sq
      have vc := cone.2.1 q v (cone.1 q ((principal q X).mp qX).1).1 ⟨vs.1,vs.2.1,vq⟩ ((principal q X).mp qX).1
      exact ⟨v,⟨vc,vs.2.1,vq⟩,vr⟩
    · intro X hx nz
      have nonempty : ∃ q, M.mem q X := by
        apply Classical.byContradiction
        intro no
        exact nz (hZF.1.eq_of_same_members X d (fun q => ⟨fun hq => (no ⟨q,hq⟩).elim,fun hq => (empty q hq).elim⟩))
      obtain ⟨q,qx⟩ := nonempty
      have qc := ((family X).mp hx).2 q qx
      obtain ⟨Y,hy,qY⟩ := fn.2.2 q qc
      exact ⟨q,Y,qY,(order Y X hy hx).mpr (((principal q Y).mp qY).2.2.2 X ((family X).mp hx).1 qx)⟩
  have large := ropen_local_generic_l hZF O family order empty cone generic ⟨p,hp,pC⟩
  have same : Pull_generic_d M F G = Pull_generic_d M J (fun X => M.mem X L ∧ ∃ q, G q ∧ M.mem q X) := by
    funext q
    apply propext
    constructor
    · rintro ⟨r,qr,hr⟩
      obtain ⟨hq,_,eq⟩ := (graph q r).mp qr
      subst r
      obtain ⟨X,hx,qX⟩ := fn.2.2 q hq
      exact ⟨X,qX,hx,q,hr,((principal q X).mp qX).2.2.1⟩
    · rintro ⟨X,qX,_,hitX⟩
      obtain ⟨hq,pr⟩ := (principal q X).mp qX
      have qG := (ropen_condition_hit_l hZF O (cone.1 q hq).1 (cone.1 q hq).2 pr.2.1 pr.2.2 generic).mp hitX
      exact ⟨q,(graph q q).mpr ⟨hq,(cone.1 q hq).2,rfl⟩,qG⟩
  have right : Miso_over_d (extension_l M hZF C R z (Pull_generic_d M F G))
      (extension_l M hZF L V d (fun X => M.mem X L ∧ ∃ q, G q ∧ M.mem q X))
      (Gval_d M C R z (Pull_generic_d M F G))
      (Gval_d M L V d (fun X => M.mem X L ∧ ∃ q, G q ∧ M.mem q X)) := by
    rw [same]
    exact map.ground_l hZF OC OL large
  exact left.symm_l.trans_l right

end YesMetaZFC.Model.Forcing.Internal
