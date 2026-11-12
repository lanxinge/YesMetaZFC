import YesMetaZFC.Model.Forcing.Boolean.DenseMap
import YesMetaZFC.Model.Forcing.Stage.Extension

/-! # 内部稠密映射诱导泛型扩张同构

反向名字将目标标签 q 替换为满足 f(p)≤q 的源标签。再次正向搬运后，
每个标签恰被其下方的稠密像族替换，内部双模拟证明名字值不变，因而得到满射。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} {P R z Q S w F : M.Domain}

theorem Dmap_d.regular_l (h : Dmap_d P R z Q S w F) (L : Cond_order_d M Q S w) :
    Reg_map_d M P R z Q S w F := by
  refine ⟨h.total,(fun p x px => ⟨(h.domain p x px).1.1,(h.domain p x px).1.2,(h.domain p x px).2⟩),
    h.mono,h.compat,?_⟩
  intro x hx nz _ _ _ _
  obtain ⟨p,y,py,yx⟩ := h.dense x hx nz
  refine ⟨p,(h.domain p y py).1.1,(h.domain p y py).1.2,fun r v rv rp => ?_⟩
  have hv := (h.domain r v rv).2
  exact ⟨v,⟨hv.1,hv.2,L.trans v y x hv.1 (h.domain p y py).2.1 hx (h.mono r p v y rv py rp) yx⟩,
    L.refl v hv.1⟩

theorem Reg_map_d.reverse_l (h : Reg_map_d M P R z Q S w F) (hZF : M.Models ZF)
    (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w) :
    ∃ E H, (∀ q p, Entry_d M q p E ↔ M.mem q Q ∧ q ≠ w ∧ ∃ y, Entry_d M p y F ∧ Entry_d M y q S) ∧
      (∀ q r, Entry_d M q r H ↔ ∃ p, Entry_d M q p E ∧ Entry_d M p r F) ∧
      ∀ q r, Entry_d M q r H → M.mem q Q ∧ Below_d M Q S w r q := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 4 := ⟨fun i => [Q,w,F,S].get i,fun _ => Q⟩
  let φ : BinarySchema 4 := { body := set[6] ⟪
    ⌜(.bound 1 : Term 6)⌝ₛ ∈ ⌜(.bound 2 : Term 6)⌝ₛ ∧ ⌜(.bound 1 : Term 6)⌝ₛ ≠ ⌜(.bound 3 : Term 6)⌝ₛ ∧
    (∃ y, ⌜entry_m⌝ₚ(⌜(.newest : Term 6)⌝ₛ,y,⌜(.bound 4 : Term 6)⌝ₛ) ∧
      ⌜entry_m⌝ₚ(y,⌜(.bound 1 : Term 6)⌝ₛ,⌜(.bound 5 : Term 6)⌝ₛ))⟫ }
  have sat q p : φ.denote ρ q p ↔ M.mem q Q ∧ q ≠ w ∧ ∃ y, Entry_d M p y F ∧ Entry_d M y q S := by
    simp only [BinarySchema.denote,φ,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
      Formula.extensionalNe,Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Formula.satisfies_exists_iff,entry_sat_l M hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨A,union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) Q P
  obtain ⟨E,_,entries⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ A
  have reverse q p : Entry_d M q p E ↔ M.mem q Q ∧ q ≠ w ∧ ∃ y, Entry_d M p y F ∧ Entry_d M y q S := by
    apply (entries q p).trans
    rw [sat]
    exact ⟨fun v => v.2.2,fun ⟨hq,nz,y,py,yq⟩ =>
      ⟨(union q).mpr (Or.inl hq),(union p).mpr (Or.inr (h.domain p y py).1),hq,nz,y,py,yq⟩⟩
  let η : Env M 2 := ⟨Fin.cases E (fun _ => F),fun _ => E⟩
  let ψ : BinarySchema 2 := { body := .existsE (.conj (entry_m (.bound 2) .newest (.bound 3))
    (entry_m .newest (.bound 1) (.bound 4))) }
  have composed q r : ψ.denote η q r ↔ ∃ p, Entry_d M q p E ∧ Entry_d M p r F := by
    simp only [BinarySchema.denote,ψ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,entry_sat_l M hZF.1]
    rfl
  obtain ⟨H,_,members⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ η Q
  have graph q r : Entry_d M q r H ↔ ∃ p, Entry_d M q p E ∧ Entry_d M p r F := by
    apply (members q r).trans
    rw [composed]
    exact ⟨fun v => v.2.2,fun ⟨p,qp,pr⟩ => ⟨((reverse q p).mp qp).1,(h.domain p r pr).2.2.1,p,qp,pr⟩⟩
  refine ⟨E,H,reverse,graph,fun q r qr => ?_⟩
  obtain ⟨p,qp,pr⟩ := (graph q r).mp qr
  obtain ⟨hq,_,y,py,yq⟩ := (reverse q p).mp qp
  have hp := (h.domain p r pr).1
  have hr := (h.domain p r pr).2.2
  exact ⟨hq,hr.1,hr.2,L.trans r y q hr.1 (h.domain p y py).2.2.1 hq
    (h.mono p p r y pr py (O.refl p hp)) yq⟩

theorem Reg_map_d.dense_hit_l (h : Reg_map_d M P R z Q S w F) (hZF : M.Models ZF)
    (L : Cond_order_d M Q S w) {V : M.Domain → Prop} (generic : Generic_d M Q S w V)
    {b} (hb : V b) (dense : ∀ q, Below_d M Q S w q b → ∃ p r, Entry_d M p r F ∧ Entry_d M r q S) :
    ∃ p, Pull_generic_d M F V p := by
  obtain ⟨D,members⟩ := image_down_set_l hZF F Q S P
  obtain ⟨y,hy,yD⟩ := generic.meets b hb D (by
    intro q hq
    obtain ⟨p,r,pr,rq⟩ := dense q hq
    have hr := (h.domain p r pr).2.2
    exact ⟨r,⟨hr.1,hr.2,rq⟩,(members r).mpr ⟨hr.1,p,r,(h.domain p r pr).1,pr,L.refl r hr.1⟩⟩)
  obtain ⟨_,p,q,_,pq,yq⟩ := (members y).mp yD
  exact ⟨p,q,pq,generic.upward y q hy (h.domain p q pq).2.2.1 yq⟩

theorem Reg_map_d.dense_extension_l (h : Reg_map_d M P R z Q S w F) (hZF : M.Models ZF)
    (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w)
    {V : M.Domain → Prop} (generic : Generic_d M Q S w V) {b} (hb : V b)
    (dense : ∀ q, Below_d M Q S w q b → ∃ p r, Entry_d M p r F ∧ Entry_d M r q S) :
    ∃ f : (extension_l M hZF P R z (Pull_generic_d M F V)).Domain → (extension_l M hZF Q S w V).Domain,
      (∀ a s t, Qval_d M P R z (Pull_generic_d M F V) s a → Nmap_d M F s t → Qval_d M Q S w V t (f a)) ∧
      (∀ a b, a ∈ b ↔ f a ∈ f b) ∧ Function.Injective f ∧ Function.Surjective f := by
  obtain ⟨f,values,full,inj⟩ := stage_extension_l O L hZF h generic (h.dense_hit_l hZF L generic hb dense)
  obtain ⟨E,H,reverse,comp,bound⟩ := h.reverse_l hZF O L
  have refineLabels q (hq : M.mem q Q) (nz : q ≠ w) r (rq : Below_d M Q S w r q) (rb : Below_d M Q S w r b) :
      ∃ s v, Entry_d M q s H ∧ Below_d M Q S w v r ∧ Entry_d M v s S := by
    obtain ⟨p,s,ps,sr⟩ := dense r rb
    have hs := (h.domain p s ps).2.2
    have sq := L.trans s r q hs.1 rq.1 hq sr rq.2.2
    exact ⟨s,s,(comp q s).mpr ⟨p,(reverse q p).mpr ⟨hq,nz,s,ps,sq⟩,ps⟩,⟨hs.1,hs.2,sr⟩,L.refl s hs.1⟩
  refine ⟨f,values,?_,inj,?_⟩
  · intro a b
    exact ((full b (f a)).trans ⟨fun ⟨c,cb,eq⟩ => inj eq ▸ cb,fun ab => ⟨a,ab,rfl⟩⟩).symm
  · intro y
    obtain ⟨t,nt,ty⟩ := value_name_l y
    obtain ⟨s,ts⟩ := nmap_exists_l M hZF E t
    have ns := nmap_name_l M hZF (fun q p qp => by
      obtain ⟨_,_,r,pr,_⟩ := (reverse q p).mp qp
      exact (h.domain p r pr).1) ts
    obtain ⟨a,sa⟩ := name_value_l (R := R) (z := z) (U := Pull_generic_d M F V) ns
    obtain ⟨u,su⟩ := nmap_exists_l M hZF F s
    have tu := nmap_comp_l hZF comp ts su
    have pos := (generic.proper b hb).1
    have eq := nmap_refine_below_l L hZF pos bound refineLabels nt tu pos (L.refl b pos)
    exact ⟨a,((qval_eq_l L hZF generic ty (values a s u sa su)).mp ⟨b,hb,eq⟩).symm⟩

theorem Dmap_d.extension_l (h : Dmap_d P R z Q S w F) (hZF : M.Models ZF)
    (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w)
    {V : M.Domain → Prop} (generic : Generic_d M Q S w V) :
    ∃ f : (extension_l M hZF P R z (Pull_generic_d M F V)).Domain → (extension_l M hZF Q S w V).Domain,
      (∀ a s t, Qval_d M P R z (Pull_generic_d M F V) s a → Nmap_d M F s t → Qval_d M Q S w V t (f a)) ∧
      (∀ a b, a ∈ b ↔ f a ∈ f b) ∧ Function.Injective f ∧ Function.Surjective f := by
  obtain ⟨b,hb⟩ := generic.inhabited
  exact (h.regular_l L).dense_extension_l hZF O L generic hb (fun q hq => h.dense q hq.1 hq.2.1)

/-- 到正锥的稠密图视为到原条件序的局部映射，保留同一张实际图。 -/
theorem Dmap_d.cone_regular_l {C a : M.Domain} (h : Dmap_d P R z C S w F)
    (L : Cond_order_d M Q S w) (ha : M.mem a Q)
    (cone : ∀ q, M.mem q C ↔ Below_d M Q S w q a) : Reg_map_d M P R z Q S w F := by
  have out {p q} (pq : Entry_d M p q F) : Below_d M Q S w q a := (cone q).mp (h.domain p q pq).2.1
  refine ⟨h.total,(fun p q pq => ⟨(h.domain p q pq).1.1,(h.domain p q pq).1.2,(out pq).1,(out pq).2.1⟩),
    h.mono,?_,?_⟩
  · intro p q x y px qy cmp
    obtain ⟨r,hr,ry⟩ := cmp
    exact h.compat p q x y px qy ⟨r,⟨(cone r).mpr (below_trans_l L ha hr (out px)),hr.2.1,hr.2.2⟩,ry⟩
  · intro x hx nz p y py xy
    have xc := (cone x).mpr ⟨hx,nz,L.trans x y a hx (out py).1 ha xy (out py).2.2⟩
    obtain ⟨r,v,rv,vx⟩ := h.dense x xc nz
    refine ⟨r,(h.domain r v rv).1.1,(h.domain r v rv).1.2,fun s t st sr => ?_⟩
    have ht := out st
    exact ⟨t,⟨ht.1,ht.2.1,L.trans t v x ht.1 (out rv).1 hx (h.mono s r t v st rv sr) vx⟩,L.refl t ht.1⟩

end YesMetaZFC.Model.Forcing.Internal
