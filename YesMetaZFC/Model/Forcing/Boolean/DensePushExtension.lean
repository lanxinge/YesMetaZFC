import YesMetaZFC.Model.Forcing.Boolean.DensePush
import YesMetaZFC.Model.Forcing.Order.GlobalDense

/-! # 给定源泛型的稠密像扩张

像的向上闭包回拉后仍为原泛型：相容性反射和泛型的极大性排除新接受条件。
因而正向构造目标泛型时，原稠密图的扩张同构仍保持全部地参数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
include hZF

theorem Dmap_d.pull_push_l {P R z Q S w F : M.Domain} (h : Dmap_d P R z Q S w F)
    (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w) {G : M.Domain → Prop}
    (generic : Generic_d M P R z G) : Pull_generic_d M F (Push_generic_d Q S F G) = G := by
  funext p
  apply propext
  constructor
  · rintro ⟨x,px,hx,q,y,gq,qy,yx⟩
    apply (generic.mem_iff_compatible_l hZF O (h.domain p x px).1.1).mpr
    intro r gr
    obtain ⟨s,gs,sr,sq⟩ := generic.directed r q gr gq
    obtain ⟨t,st⟩ := h.total s (generic.proper s gs).1 (generic.proper s gs).2
    obtain ⟨v,rv⟩ := h.total r (generic.proper r gr).1 (generic.proper r gr).2
    have ht := (h.domain s t st).2
    exact h.compat r p v x rv px ⟨t,⟨ht.1,ht.2,h.mono s r t v st rv sr⟩,
      L.trans t y x ht.1 (h.domain q y qy).2.1 hx (h.mono s q t y st qy sq) yx⟩
  · intro gp
    obtain ⟨x,px⟩ := h.total p (generic.proper p gp).1 (generic.proper p gp).2
    have hx := (h.domain p x px).2.1
    exact ⟨x,px,hx,p,x,gp,px,L.refl x hx⟩

theorem Dmap_d.push_extension_l {P R z Q S w F a : M.Domain} (h : Dmap_d P R z Q S w F)
    (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w) (ha : M.mem a Q)
    (top : ∀ q, M.mem q Q → Entry_d M q a S) {G : M.Domain → Prop} (generic : Generic_d M P R z G) :
    Generic_d M Q S w (Push_generic_d Q S F G) ∧
      Miso_over_d (Internal.extension_l M hZF P R z G) (Internal.extension_l M hZF Q S w (Push_generic_d Q S F G))
        (Gval_d M P R z G) (Gval_d M Q S w (Push_generic_d Q S F G)) := by
  have localMap : Dmap_at_d P R z Q S w F a :=
    ⟨h.regular_l L,h.functional,fun p q pq =>
      ⟨(h.domain p q pq).2.1,(h.domain p q pq).2.2,top q (h.domain p q pq).2.1⟩,
      fun q hq => h.dense q hq.1 hq.2.1⟩
  have target := localMap.push_generic_l hZF L ha generic
  have iso := h.ground_l hZF O L target
  rw [h.pull_push_l hZF O L generic] at iso
  exact ⟨target,iso⟩

end YesMetaZFC.Model.Forcing.Internal
