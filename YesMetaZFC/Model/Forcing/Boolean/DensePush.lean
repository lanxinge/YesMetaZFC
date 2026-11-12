import YesMetaZFC.Model.Forcing.Boolean.DenseLocal
import YesMetaZFC.Model.Forcing.Truth.Definability

/-! # 沿实际稠密图正向生成泛型并恢复原滤子

源泛型的像取向上闭包，局部稠密提升保证它遇到目标模型的全部稠密要求。
回拉原泛型后再正向生成，得到原滤子本身；初等运输保留同一构造。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}}

def Push_generic_d (Q S F : M.Domain) (G : M.Domain → Prop) (q : M.Domain) : Prop :=
  M.mem q Q ∧ ∃ p x, G p ∧ Entry_d M p x F ∧ Entry_d M x q S

variable (hZF : M.Models ZF) {P R z Q S w F a : M.Domain}
  (h : Dmap_at_d P R z Q S w F a) (L : Cond_order_d M Q S w)
include hZF h L

theorem Dmap_at_d.push_generic_l (ha : M.mem a Q) {G : M.Domain → Prop}
    (generic : Generic_d M P R z G) : Generic_d M Q S w (Push_generic_d Q S F G) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rintro q ⟨hq,p,x,_,px,xq⟩
    exact ⟨hq,fun eq => (h.domain p x px).2.2.2 (L.zero x (h.domain p x px).2.2.1 (eq ▸ xq))⟩
  · obtain ⟨p,hp⟩ := generic.inhabited
    obtain ⟨x,px⟩ := h.total p (generic.proper p hp).1 (generic.proper p hp).2
    exact ⟨x,(h.domain p x px).2.2.1,p,x,hp,px,L.refl x (h.domain p x px).2.2.1⟩
  · rintro q r ⟨hq,p,x,hp,px,xq⟩ hr qr
    exact ⟨hr,p,x,hp,px,L.trans x q r (h.domain p x px).2.2.1 hq hr xq qr⟩
  · rintro q r ⟨hq,p,x,hp,px,xq⟩ ⟨hr,t,y,ht,ty,yr⟩
    obtain ⟨s,hs,sp,st⟩ := generic.directed p t hp ht
    obtain ⟨v,sv⟩ := h.total s (generic.proper s hs).1 (generic.proper s hs).2
    have hv := (h.domain s v sv).2.2.1
    exact ⟨v,⟨hv,s,v,hs,sv,L.refl v hv⟩,
      L.trans v x q hv (h.domain p x px).2.2.1 hq (h.mono s p v x sv px sp) xq,
      L.trans v y r hv (h.domain t y ty).2.2.1 hr (h.mono s t v y sv ty st) yr⟩
  · rintro q ⟨hq,p,x,hp,px,xq⟩ D dense
    let ρ : Env M 4 := ⟨fun i => [F,D,S,Q].get i,fun _ => D⟩
    let φ : UnarySchema 4 := { body := .existsE (.existsE (.conj
      (entry_m (.bound 2) (.bound 1) (.bound 3)) (.conj (.mem .newest (.bound 6))
        (.conj (.mem .newest (.bound 4)) (entry_m (.bound 1) .newest (.bound 5)))))) }
    have sat r : φ.denote ρ r ↔ ∃ y t, Entry_d M r y F ∧ M.mem t Q ∧ M.mem t D ∧ Entry_d M y t S := by
      simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
        entry_sat_l M hZF.1,Formula.satisfies_mem_iff]; rfl
    obtain ⟨r,hr,y,t,ry,ht,td,yt⟩ := generic_pick_l hZF generic ⟨4,φ,ρ,sat⟩ hp (by
      intro r rp
      obtain ⟨s,rs⟩ := h.total r rp.1 rp.2.1
      have hs := (h.domain r s rs).2.2
      have sq := L.trans s x q hs.1 (h.domain p x px).2.2.1 hq (h.mono r p s x rs px rp.2.2) xq
      obtain ⟨t,ts,td⟩ := dense s ⟨hs.1,hs.2,sq⟩
      obtain ⟨v,y,vr,vy,yt⟩ := h.lower_l L ha rs ts
      exact ⟨v,vr,y,t,vy,ts.1,td,yt.2.2⟩)
    exact ⟨t,⟨ht,r,y,hr,ry,yt⟩,td⟩

/-- 同一泛型先回拉、再取像的向上闭包，精确恢复全部原条件。 -/
theorem Dmap_at_d.push_pull_l {H : M.Domain → Prop} (generic : Generic_d M Q S w H) (ha : H a) :
    Push_generic_d Q S F (Pull_generic_d M F H) = H := by
  funext q
  apply propext
  constructor
  · rintro ⟨hq,p,x,⟨y,py,hy⟩,px,xq⟩
    have eq := h.functional p y x py px
    exact generic.upward x q (eq ▸ hy) hq xq
  · intro hq
    obtain ⟨r,hr,rq,ra⟩ := generic.directed q a hq ha
    let ρ : Env M 3 := ⟨fun i => [F,S,q].get i,fun _ => q⟩
    let φ : UnarySchema 3 := { body := .existsE (.conj
      (entry_m .newest (.bound 1) (.bound 2)) (entry_m (.bound 1) (.bound 4) (.bound 3))) }
    have sat x : φ.denote ρ x ↔ ∃ p, Entry_d M p x F ∧ Entry_d M x q S := by
      simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,entry_sat_l M hZF.1]; rfl
    obtain ⟨x,hx,p,px,xq⟩ := generic_pick_l hZF generic ⟨3,φ,ρ,sat⟩ hr (by
      intro t tr
      have ht := below_trans_l L (generic.proper a ha).1 tr ⟨(generic.proper r hr).1,(generic.proper r hr).2,ra⟩
      obtain ⟨p,x,px,xt⟩ := h.dense t ht
      have xq := L.trans x r q (h.domain p x px).2.2.1 (generic.proper r hr).1 (generic.proper q hq).1
        (L.trans x t r (h.domain p x px).2.2.1 tr.1 (generic.proper r hr).1 xt tr.2.2) rq
      exact ⟨x,⟨(h.domain p x px).2.2.1,(h.domain p x px).2.2.2,xt⟩,p,px,xq⟩)
    exact ⟨(generic.proper q hq).1,p,x,⟨x,px,hx⟩,px,xq⟩

omit hZF L in
/-- 目标条件有原像时，正向滤子运输与初等像交换；图不必整体逐点固定。 -/
theorem Dmap_at_d.push_image_l {N : Structure.{v}} (hM : Extensional M) (hN : Extensional N)
    (e : M.Domain → N.Domain) (elem : Pe_d e) {G : M.Domain → Prop}
    (proper : ∀ p, G p → M.mem p P ∧ p ≠ z)
    (covers : ∀ q, N.mem q (e Q) → ∃ p, M.mem p Q ∧ e p = q) :
    Push_generic_d (e Q) (e S) (e F) (Em_generic_d e G) = Em_generic_d e (Push_generic_d Q S F G) := by
  have moved := h.image_l hM hN e elem
  have edge := em_entry_l hM hN e elem
  funext q
  apply propext
  constructor
  · rintro ⟨hq,p,x,⟨r,hr,rfl⟩,px,xq⟩
    obtain ⟨t,ht,rfl⟩ := covers q hq
    obtain ⟨y,ry⟩ := h.total r (proper r hr).1 (proper r hr).2
    have eq := moved.functional (e r) x (e y) px ((edge r y F).mp ry)
    exact ⟨t,⟨ht,r,y,hr,ry,(edge y t S).mpr (eq ▸ xq)⟩,rfl⟩
  · rintro ⟨q,⟨hq,p,x,hp,px,xq⟩,rfl⟩
    exact ⟨(em_member_l e elem q Q).mp hq,e p,e x,⟨p,hp,rfl⟩,(edge p x F).mp px,(edge x q S).mp xq⟩

omit hZF L in
theorem Dmap_at_d.pull_image_l {N : Structure.{v}} (hM : Extensional M) (hN : Extensional N)
    (e : M.Domain → N.Domain) (elem : Pe_d e) (H : M.Domain → Prop)
    (covers : ∀ p, N.mem p (e P) → ∃ q, M.mem q P ∧ e q = p) :
    Pull_generic_d N (e F) (Em_generic_d e H) = Em_generic_d e (Pull_generic_d M F H) := by
  have moved := h.image_l hM hN e elem
  have edge := em_entry_l hM hN e elem
  funext p
  apply propext
  constructor
  · rintro ⟨x,px,q,hq,rfl⟩
    obtain ⟨r,_,rfl⟩ := covers p (moved.domain p (e q) px).1
    exact ⟨r,⟨q,(edge r q F).mpr px,hq⟩,rfl⟩
  · rintro ⟨p,⟨q,pq,hq⟩,rfl⟩
    exact ⟨e q,(edge p q F).mp pq,q,hq,rfl⟩

end YesMetaZFC.Model.Forcing.Internal
