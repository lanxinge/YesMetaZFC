import YesMetaZFC.Model.Forcing.Boolean.QuotientCoupling

/-! # 共同条件序到原布尔代数的局部稠密映射 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
variable {Q T w u A S e L V d J P N c C R F : M.Domain}

theorem Qcp_d.mem_l (k : Qcp_d hZF Q T w c L V d J P N C R F) {v q x} (pair : KPair_d M v q x) :
    M.mem v C ↔ Qc_cond_d Q T w c d P q x := by
  apply Iff.trans ?_ (k.conditions q x)
  exact ⟨fun hv => ⟨v,pair,hv⟩,fun ⟨t,ht,hC⟩ => kpair_unique_l M hZF.1 ht pair ▸ hC⟩

theorem Qcp_d.le_l (k : Qcp_d hZF Q T w c L V d J P N C R F) {v v' q x q' x'}
    (hv : M.mem v C) (hv' : M.mem v' C) (pair : KPair_d M v q x) (pair' : KPair_d M v' q' x') :
    Entry_d M v v' R ↔ Entry_d M q q' T ∧ Entry_d M x x' V := by
  apply (k.order v v').trans
  constructor
  · rintro ⟨_,_,r,y,r',y',ry,ry',rr,yy⟩
    obtain ⟨rq,yx⟩ := kpair_injective_l M ry pair
    obtain ⟨rq',yx'⟩ := kpair_injective_l M ry' pair'
    exact rq ▸ yx ▸ rq' ▸ yx' ▸ ⟨rr,yy⟩
  · exact fun h => ⟨hv,hv',q,x,q',x',pair,pair',h⟩

theorem Qcp_d.value_l (k : Qcp_d hZF Q T w c L V d J P N C R F) {v q x b}
    (pair : KPair_d M v q x) (vb : Entry_d M v b F) :
    ∃ a y, Entry_d M q a N ∧ Entry_d M a y J ∧ BooleanZF.Meet_d I L V x y b := by
  obtain ⟨_,r,t,a,y,rt,ra,ay,meet⟩ := (k.values v b).mp vb
  obtain ⟨rq,tx⟩ := kpair_injective_l M rt pair
  exact rq ▸ tx ▸ ⟨a,y,ra,ay,meet⟩

theorem Qcp_d.order_l (k : Qcp_d hZF Q T w c L V d J P N C R F)
    (h : Qc_d hZF Q T w u A S e L V d J P N) : Cond_order_d M C R C := by
  have typed v (hv : M.mem v C) : ∃ q x, KPair_d M v q x ∧ M.mem q Q ∧ M.mem x L := by
    obtain ⟨q,x,pair⟩ := k.graph v hv
    obtain ⟨hq,_,a,xa,_⟩ := (k.mem_l hZF pair).mp hv
    exact ⟨q,x,pair,hq.1,h.projection.input_mem_of_pairMember xa⟩
  refine ⟨?_,?_,?_⟩
  · intro v hv
    obtain ⟨q,x,pair,hq,hx⟩ := typed v hv
    exact (k.le_l hZF hv hv pair pair).mpr ⟨h.small.refl q hq,h.target.order.refl x hx⟩
  · intro a b t ha hb ht ab bt
    obtain ⟨q,x,pair,hq,hx⟩ := typed a ha
    obtain ⟨q',x',pair',hq',hx'⟩ := typed b hb
    obtain ⟨q'',x'',pair'',hq'',hx''⟩ := typed t ht
    have h₁ := (k.le_l hZF ha hb pair pair').mp ab
    have h₂ := (k.le_l hZF hb ht pair' pair'').mp bt
    exact (k.le_l hZF ha ht pair pair'').mpr
      ⟨h.small.trans q q' q'' hq hq' hq'' h₁.1 h₂.1,h.target.order.trans x x' x'' hx hx' hx'' h₁.2 h₂.2⟩
  · intro v _ vc
    exact (KP.mem_irrefl_d (ZF.modelsKP hZF) C ((k.order v C).mp vc).2.1).elim

theorem Qc_d.refine_l (h : Qc_d hZF Q T w u A S e L V d J P N) {x q a y}
    (hx : M.mem x L) (nz : x ≠ d) (qa : Entry_d M q a N) (ay : Entry_d M a y J) (xy : Entry_d M x y V) :
    ∃ r b, Below_d M Q T w r q ∧ Entry_d M x b P ∧ M.mem r b := by
  obtain ⟨b,hb,xb⟩ := h.projection.2.2 x hx
  have ba := ((h.adjoint x b xb).2.2 a y ay).mp xy
  have sub := (h.order b a hb (h.hom.function.input_mem_of_pairMember ay)).mp ba
  have nonempty : ∃ t, M.mem t b := by
    apply Classical.byContradiction
    intro no
    exact (h.adjoint x b xb).positive_l I h.source h.target h.hom.zero nz
      (hZF.1.eq_of_same_members b e (fun t => ⟨fun ht => (no ⟨t,ht⟩).elim,fun ht => (h.empty t ht).elim⟩))
  obtain ⟨t,tb⟩ := nonempty
  have pos := ((h.family b).mp hb).1.1 t tb
  obtain ⟨r,rt,rq⟩ := ((h.graph q a).mp qa).2.dense_l hZF h.small (sub t tb) t (below_refl_l h.small pos.1 pos.2)
  exact ⟨r,b,⟨rt.1,rt.2.1,rq⟩,xb,((h.family b).mp hb).1.2.1 t r pos.1 rt tb⟩

theorem Qcp_d.mono_l (k : Qcp_d hZF Q T w c L V d J P N C R F)
    (h : Qc_d hZF Q T w u A S e L V d J P N) {v v' b b'}
    (vb : Entry_d M v b F) (vb' : Entry_d M v' b' F) (vv' : Entry_d M v v' R) : Entry_d M b b' V := by
  have hv := k.function.input_mem_of_pairMember vb
  have hv' := k.function.input_mem_of_pairMember vb'
  obtain ⟨q,x,pair⟩ := k.graph v hv
  obtain ⟨q',x',pair'⟩ := k.graph v' hv'
  obtain ⟨a,y,qa,ay,meet⟩ := k.value_l hZF pair vb
  obtain ⟨a',y',qa',ay',meet'⟩ := k.value_l hZF pair' vb'
  have coord := (k.le_l hZF hv hv' pair pair').mp vv'
  have hq := ((h.graph q a).mp qa).2
  have hq' := ((h.graph q' a').mp qa').2
  have aa := (h.order a a' (h.principal.output_mem_of_pairMember qa) (h.principal.output_mem_of_pairMember qa')).mpr
    (hq.mono_l hq' ⟨(hq.1.1 q hq.2.1).1,(hq.1.1 q hq.2.1).2,coord.1⟩)
  have yy := h.hom.mono_l I h.source h.target ay ay' aa
  obtain ⟨_,_,b₀,xb,_⟩ := (k.mem_l hZF pair).mp hv
  obtain ⟨_,_,b₁,xb',_⟩ := (k.mem_l hZF pair').mp hv'
  exact meet.mono_l I h.target.order (h.projection.input_mem_of_pairMember xb)
    (h.hom.function.output_mem_of_pairMember ay) (h.projection.input_mem_of_pairMember xb')
    (h.hom.function.output_mem_of_pairMember ay') meet' coord.2 yy

theorem Qcp_d.dense_l (k : Qcp_d hZF Q T w c L V d J P N C R F)
    (h : Qc_d hZF Q T w u A S e L V d J P N) {a y x}
    (ca : Entry_d M c a N) (ay : Entry_d M a y J) (hx : M.mem x L) (nz : x ≠ d) (xy : Entry_d M x y V) :
    ∃ v b, Entry_d M v b F ∧ Entry_d M b x V := by
  obtain ⟨q,b,hq,xb,qb⟩ := h.refine_l hZF hx nz ca ay xy
  obtain ⟨v,pair⟩ := (I).total q x
  have hv := (k.mem_l hZF pair).mpr ⟨hq,nz,b,xb,qb⟩
  obtain ⟨m,_,vm⟩ := k.function.2.2 v hv
  obtain ⟨_,_,_,_,meet⟩ := k.value_l hZF pair vm
  exact ⟨v,m,vm,(BooleanZF.meet_bounds_d I h.target.order meet).1⟩

theorem Qcp_d.support_l (k : Qcp_d hZF Q T w c L V d J P N C R F)
    (h : Qc_d hZF Q T w u A S e L V d J P N) {a y v b}
    (ca : Entry_d M c a N) (ay : Entry_d M a y J) (vb : Entry_d M v b F) : Entry_d M b y V := by
  obtain ⟨q,x,pair⟩ := k.graph v (k.function.input_mem_of_pairMember vb)
  obtain ⟨hq,_,_⟩ := (k.mem_l hZF pair).mp (k.function.input_mem_of_pairMember vb)
  obtain ⟨a',y',qa,ay',meet⟩ := k.value_l hZF pair vb
  have aa := (h.order a' a (h.principal.output_mem_of_pairMember qa) (h.principal.output_mem_of_pairMember ca)).mpr
    (((h.graph q a').mp qa).2.mono_l ((h.graph c a).mp ca).2 hq)
  exact h.target.order.trans b y' y meet.1 (h.hom.function.output_mem_of_pairMember ay')
    (h.hom.function.output_mem_of_pairMember ay) (BooleanZF.meet_bounds_d I h.target.order meet).2
    (h.hom.mono_l I h.source h.target ay' ay aa)

theorem Qcp_d.regular_l (k : Qcp_d hZF Q T w c L V d J P N C R F)
    (h : Qc_d hZF Q T w u A S e L V d J P N) {a y}
    (ca : Entry_d M c a N) (ay : Entry_d M a y J) : Reg_map_d M C R C L V d F := by
  have domain v b (vb : Entry_d M v b F) : M.mem v C ∧ v ≠ C ∧ M.mem b L ∧ b ≠ d := by
    have hv := k.function.input_mem_of_pairMember vb
    obtain ⟨q,x,pair⟩ := k.graph v hv
    obtain ⟨_,_,t,xt,qt⟩ := (k.mem_l hZF pair).mp hv
    obtain ⟨r,s,qr,rs,meet⟩ := k.value_l hZF pair vb
    have cmp := h.point_cmp_l hZF (h.projection.output_mem_of_pairMember xt) (h.principal.output_mem_of_pairMember qr)
      qt ((h.graph q r).mp qr).2.2.1
    have nz := (boolean_cmp_meet_l hZF h.target meet).mp ((badj_cmp_l hZF h.source h.target h.hom (h.adjoint x t xt) rs).mpr cmp)
    exact ⟨hv,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ hv),meet.1,nz⟩
  refine ⟨fun v hv _ => (k.function.2.2 v hv).imp fun b hb => hb.2,domain,
    fun _ _ _ _ => k.mono_l hZF h,?_,?_⟩
  · intro v v' b b' vb vb' cmp
    have hv := (domain v b vb).1
    have hv' := (domain v' b' vb').1
    obtain ⟨q,x,pair⟩ := k.graph v hv
    obtain ⟨q',x',pair'⟩ := k.graph v' hv'
    have hx : M.mem x L := by
      obtain ⟨_,_,a,xa,_⟩ := (k.mem_l hZF pair).mp hv
      exact h.projection.input_mem_of_pairMember xa
    have hx' : M.mem x' L := by
      obtain ⟨_,_,a,xa,_⟩ := (k.mem_l hZF pair').mp hv'
      exact h.projection.input_mem_of_pairMember xa
    obtain ⟨r,s,qr,rs,meet⟩ := k.value_l hZF pair vb
    obtain ⟨r',s',qr',rs',meet'⟩ := k.value_l hZF pair' vb'
    obtain ⟨z,hz,zb'⟩ := cmp
    have bounds := BooleanZF.meet_bounds_d I h.target.order meet
    have bounds' := BooleanZF.meet_bounds_d I h.target.order meet'
    have zs := h.target.order.trans z b s hz.1 meet.1 (h.hom.function.output_mem_of_pairMember rs) hz.2.2 bounds.2
    obtain ⟨t,a,ht,za,ta⟩ := h.refine_l hZF hz.1 hz.2.1 qr rs zs
    have zs' := h.target.order.trans z b' s' hz.1 meet'.1 (h.hom.function.output_mem_of_pairMember rs') zb' bounds'.2
    have ar' := ((h.adjoint z a za).2.2 r' s' rs').mp zs'
    have tr' := (h.order a r' (h.projection.output_mem_of_pairMember za) (h.principal.output_mem_of_pairMember qr')).mp ar' t ta
    obtain ⟨t',tt',tq'⟩ := ((h.graph q' r').mp qr').2.dense_l hZF h.small tr' t (below_refl_l h.small ht.1 ht.2.1)
    have tq := h.small.trans t' t q tt'.1 ht.1 ((k.mem_l hZF pair).mp hv).1.1 tt'.2.2 ht.2.2
    have tc := h.small.trans t' q c tt'.1 ((k.mem_l hZF pair).mp hv).1.1
      (h.cone.1 c (h.principal.input_mem_of_pairMember ca)).1 tq ((k.mem_l hZF pair).mp hv).1.2.2
    have t'a := ((h.family a).mp (h.projection.output_mem_of_pairMember za)).1.2.1 t t' ht.1 tt' ta
    obtain ⟨v'',pair''⟩ := (I).total t' z
    have hv'' := (k.mem_l hZF pair'').mpr ⟨⟨tt'.1,tt'.2.1,tc⟩,hz.2.1,a,za,t'a⟩
    refine ⟨v'',⟨hv'',fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ hv''),
      (k.le_l hZF hv'' hv pair'' pair).mpr ⟨tq,?_⟩⟩,(k.le_l hZF hv'' hv' pair'' pair').mpr ⟨tq',?_⟩⟩
    · exact h.target.order.trans z b x hz.1 meet.1 hx hz.2.2 bounds.1
    · exact h.target.order.trans z b' x' hz.1 meet'.1 hx' zb' bounds'.1
  · intro x hx nz v b vb xb
    have xy := h.target.order.trans x b y hx (domain v b vb).2.2.1 (h.hom.function.output_mem_of_pairMember ay)
      xb (k.support_l hZF h ca ay vb)
    obtain ⟨r,s,rs,sx⟩ := k.dense_l hZF h ca ay hx nz xy
    have hr := domain r s rs
    refine ⟨r,hr.1,hr.2.1,fun t z tz tr => ?_⟩
    have ht := domain t z tz
    exact ⟨z,⟨ht.2.2.1,ht.2.2.2,h.target.order.trans z s x ht.2.2.1 hr.2.2.1 hx
      (k.mono_l hZF h tz rs tr) sx⟩,h.target.order.refl z ht.2.2.1⟩

end YesMetaZFC.Model.Forcing.Internal
