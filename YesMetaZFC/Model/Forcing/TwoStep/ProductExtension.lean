import YesMetaZFC.Model.Forcing.TwoStep.Product
import YesMetaZFC.Model.Forcing.Check.Order
import YesMetaZFC.Model.Forcing.TwoStep.Names.Isomorphism
import YesMetaZFC.Model.Forcing.TwoStep.Names.Check

/-! # 积泛型与二次扩张的同一地参数识别

首阶段泛型 H 和 M[H] 上的旧条件泛型 G 产生实际积泛型 H×G。
稠密 check 图与二步展开合成同构，原模型每个参数沿两条路径得到相同值。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def Prod_generic_d {Q T q : M.Domain} {H : M.Domain → Prop}
    (C : M.Domain) (j : M.Domain → (extension_l M hZF Q T q H).Domain)
    (G : (extension_l M hZF Q T q H).Domain → Prop) (c : M.Domain) : Prop :=
  M.mem c C ∧ ∃ a b, KPair_d M c a b ∧ H a ∧ G (j b)

theorem Prod_d.extension_l {Q T P U C R b : M.Domain}
    (product : Prod_d hZF Q T P U C R)
    (O : Cond_order_d M Q T Q) (L : Cond_order_d M P U P) (OP : Cond_order_d M C R C)
    (top : ∀ q, M.mem q Q → Entry_d M q b T)
    {H : M.Domain → Prop} (small : Generic_d M Q T Q H) (hb : H b)
    (j : M.Domain → (Internal.extension_l M hZF Q T Q H).Domain)
    (checks : ∀ x t, Check_d M b x t → Qval_d M Q T Q H t (j x))
    {J : (Internal.extension_l M hZF Q T Q H).Domain}
    (order : ∀ x y, (Internal.extension_l M hZF Q T Q H).mem x (j P) →
      (Internal.extension_l M hZF Q T Q H).mem y (j P) →
      (Entry_d (Internal.extension_l M hZF Q T Q H) x y (j U) ↔
        Entry_d (Internal.extension_l M hZF Q T Q H) x y J))
    (K : Cond_order_d (Internal.extension_l M hZF Q T Q H) (j P) J (j P))
    {G : (Internal.extension_l M hZF Q T Q H).Domain → Prop}
    (generic : Generic_d (Internal.extension_l M hZF Q T Q H) (j P) J (j P) G) :
    Generic_d M C R C (Prod_generic_d hZF C j G) ∧
      Miso_over_d (Internal.extension_l M hZF C R C (Prod_generic_d hZF C j G))
        (Internal.extension_l (Internal.extension_l M hZF Q T Q H) (preserves_zf_l O hZF small) (j P) J (j P) G)
        (Gval_d M C R C (Prod_generic_d hZF C j G))
        (fun x => Gval_d (Internal.extension_l M hZF Q T Q H) (j P) J (j P) G (j x)) := by
  have hbQ := (small.proper b hb).1
  obtain ⟨A,name,na,_⟩ := zf_check_l M hZF hbQ P
  obtain ⟨ν,relation,nν,_⟩ := zf_check_l M hZF hbQ U
  have pre := check_preord_force_l O hZF hbQ name relation ⟨L.refl,L.trans⟩
    (below_refl_l O hbQ (small.proper b hb).2)
  obtain ⟨W,D,E,_,step,OD⟩ := two_step_l O hZF na nν hbQ pre
  have compose := (two_step_compose_l O hZF small step OD hb (checks P A name) (checks U ν relation) ((generic_order_l order G).mpr generic)).1
  obtain ⟨F,_,graph,map⟩ := product.step_map_l hZF O L hbQ top name relation step OD
  have same : Pull_generic_d M F (Compose_generic_d M Q T Q D H G) = Prod_generic_d hZF C j G := by
    funext v
    apply propext
    constructor
    · rintro ⟨t,vt,_,q,s,x,pair,hq,sx,hx⟩
      obtain ⟨hv,q',p,s',out,check,pair'⟩ := (graph v t).mp vt
      obtain ⟨eq₁,eq₂⟩ := kpair_injective_l M pair pair'
      subst q' s'
      have eq := qval_unique_l (checks p s check) sx
      exact ⟨hv,q,p,out,hq,eq.symm ▸ hx⟩
    · rintro ⟨hv,q,p,pair,hq,hp⟩
      obtain ⟨t,vt⟩ := map.total v hv (fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ hv))
      obtain ⟨_,q',p',s,pair',check,out⟩ := (graph v t).mp vt
      obtain ⟨eq₁,eq₂⟩ := kpair_injective_l M pair pair'
      subst q' p'
      exact ⟨t,vt,(map.domain v t vt).2.1,q,s,j p,out,hq,checks p s check,hp⟩
  have reg := map.regular_l OD
  obtain ⟨d,hd⟩ := compose.inhabited
  have hit := reg.dense_hit_l hZF OD compose hd (fun q hq => map.dense q hq.1 hq.2.1)
  have productGeneric := reg_generic_l OP OD hZF reg compose hit
  have first := map.ground_l hZF OP OD compose
  obtain ⟨f,values,mem,inj,onto⟩ := two_step_iso_l O hZF small step OD
    (checks P A name) (checks U ν relation) order K generic hb
  have ground := curry_ground_l O hZF small step K generic compose f values inj hb j checks
  have result := first.trans_l ⟨f,mem,inj,onto,ground⟩
  exact ⟨same ▸ productGeneric,same ▸ result⟩

end YesMetaZFC.Model.Forcing.Internal
