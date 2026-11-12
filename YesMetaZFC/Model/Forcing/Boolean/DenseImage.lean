import YesMetaZFC.Model.Forcing.Boolean.DenseRegular

/-! # 稠密回拉的满射性

对源正则开集，先在目标中取其像的向下闭包，再正则化。
不相容性反射证明回拉恰好恢复原集。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
include hZF

theorem Dmap_d.ropen_image_l {P R z Q S w F V : M.Domain} (h : Dmap_d P R z Q S w F)
    (L : Cond_order_d M Q S w) (regular : Ropen_d P R z V) : ∃ U, Ropen_d Q S w U ∧ Rpull_d P z F U V := by
  let ρ : Env M 4 := ⟨fun i => [S,w,F,V].get i,fun _ => Q⟩
  let φ : UnarySchema 4 := { body := set[5] ⟪⌜(.newest : Term 5)⌝ₛ ≠ ⌜(.bound 2 : Term 5)⌝ₛ ∧
    (∃ p ∈ ⌜(.bound 4 : Term 5)⌝ₛ, ∃ y, ⌜entry_m⌝ₚ(p,y,⌜(.bound 3 : Term 5)⌝ₛ) ∧
      ⌜entry_m⌝ₚ(⌜(.newest : Term 5)⌝ₛ,y,⌜(.bound 1 : Term 5)⌝ₛ))⟫ }
  obtain ⟨D,members⟩ := ZF.separation_exists_d hZF φ ρ Q
  have member x : M.mem x D ↔ M.mem x Q ∧ x ≠ w ∧ ∃ p y, M.mem p V ∧ Entry_d M p y F ∧ Entry_d M x y S := by
    apply (members x).trans (and_congr_right fun _ => ?_)
    simp only [φ,Formula.satisfies_conj_iff,Formula.extensionalNe,Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_existsMem_iff,Formula.satisfies_exists_iff,
      entry_sat_l M hZF.1,Definitional.Term.eval_weaken]
    exact and_congr_right fun _ => ⟨fun ⟨p,hp,y,py,xy⟩ => ⟨p,y,hp,py,xy⟩,
      fun ⟨p,y,hp,py,xy⟩ => ⟨p,hp,y,py,xy⟩⟩
  have lower : Lower_d M Q S w (fun x => M.mem x D) := by
    intro x y hx hy hd
    obtain ⟨_,_,p,v,hp,pv,xv⟩ := (member x).mp hd
    exact (member y).mpr ⟨hy.1,hy.2.1,p,v,hp,pv,L.trans y x v hy.1 hx (h.domain p v pv).2.1 hy.2.2 xv⟩
  obtain ⟨U,closed,values⟩ := ropen_closure_l hZF L D
  refine ⟨U,closed,fun p => ⟨?_,?_⟩⟩
  · intro hp
    have pos := regular.1 p hp
    obtain ⟨x,px⟩ := h.total p pos.1 pos.2
    have hx := (h.domain p x px).2
    have xd := (member x).mpr ⟨hx.1,hx.2,p,x,hp,px,L.refl x hx.1⟩
    exact ⟨pos.1,pos.2,x,px,(values x).mpr ⟨hx.1,hx.2,dense_intro_l L lower hx.1 xd⟩⟩
  · rintro ⟨hp,hz,x,px,hx⟩
    apply regular.2.2 p hp hz
    intro r hr
    obtain ⟨y,ry⟩ := h.total r hr.1 hr.2.1
    have hy := (h.domain r y ry).2
    have yu := closed.2.1 x y (h.domain p x px).2.1 ⟨hy.1,hy.2,h.mono r p y x ry px hr.2.2⟩ hx
    obtain ⟨t,ty,td⟩ := ((values y).mp yu).2.2 y (below_refl_l L hy.1 hy.2)
    obtain ⟨_,_,s,v,sv,sv',tv⟩ := (member t).mp td
    obtain ⟨u,ur,us⟩ := h.compat r s y v ry sv' ⟨t,ty,tv⟩
    exact ⟨u,ur,regular.2.1 s u (regular.1 s sv).1 ⟨ur.1,ur.2.1,us⟩ sv⟩

end YesMetaZFC.Model.Forcing.Internal
