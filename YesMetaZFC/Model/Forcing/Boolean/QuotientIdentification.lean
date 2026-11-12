import YesMetaZFC.Model.Forcing.Boolean.QuotientStepMap
import YesMetaZFC.Model.Forcing.Boolean.DenseGround
import YesMetaZFC.Model.Forcing.Boolean.QuotientGeneric
import YesMetaZFC.Model.Forcing.TwoStep.Generic.Composition

/-! # 原布尔扩张与商二步扩张的识别

共同条件 (q,x) 被两侧泛型接受，都恰好等价于 H(q) 且 G(x)。
两张实际比较图的回拉滤子相同，局部稠密同构因此识别两侧的全部名称商。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
variable {Q T w u A S e L V d J P N c C R F b τ ν W D E : M.Domain}

theorem Qcp_d.accept_l (k : Qcp_d hZF Q T w c L V d J P N C R F)
    (h : Qc_d hZF Q T w u A S e L V d J P N)
    {H G : M.Domain → Prop} (small : Generic_d M Q T w H) (big : Generic_d M L V d G)
    (read : ∀ a y, Entry_d M a y J → (G y ↔ ∃ q, H q ∧ M.mem q a))
    {v q x y} (pair : KPair_d M v q x) (vy : Entry_d M v y F) : G y ↔ H q ∧ G x := by
  have hv := k.function.input_mem_of_pairMember vy
  obtain ⟨hq,_,b,xb,_⟩ := (k.mem_l hZF pair).mp hv
  have hx := h.projection.input_mem_of_pairMember xb
  obtain ⟨a,z,qa,az,meet⟩ := k.value_l hZF pair vy
  have hz := h.hom.function.output_mem_of_pairMember az
  have pr := ((h.graph q a).mp qa).2
  have bounds := BooleanZF.meet_bounds_d I h.target.order meet
  constructor
  · intro gy
    have gz := big.upward y z gy hz bounds.2
    exact ⟨(ropen_condition_hit_l hZF h.small hq.1 hq.2.1 pr.2.1 pr.2.2 small).mp ((read a z az).mp gz),
      big.upward y x gy hx bounds.1⟩
  · rintro ⟨hq,gx⟩
    have gz := (read a z az).mpr ⟨q,hq,pr.2.1⟩
    obtain ⟨r,gr,rx,rz⟩ := big.directed x z gx gz
    exact big.upward r y gr meet.1 ((meet.2 r (big.proper r gr).1).mpr ⟨rx,rz⟩)

theorem Qc_d.identification_l (h : Qc_d hZF Q T w u A S e L V d J P N)
    {H G : M.Domain → Prop} (small : Generic_d M Q T w H) (big : Generic_d M L V d G)
    (read : ∀ a y, Entry_d M a y J → (G y ↔ ∃ q, H q ∧ M.mem q a))
    (hc : H c) (cu : M.mem c u) (hb : M.mem b Q) (cb : Entry_d M c b T)
    (name : Qname_d Q b L d P τ) (relation : Check_d M b V ν)
    (j : M.Domain → (extension_l M hZF Q T w H).Domain) (inj : Function.Injective j)
    (checks : ∀ x t, Check_d M b x t → Qval_d M Q T w H t (j x))
    (step : Two_step_d M Q T w c τ ν W D E) (OD : Cond_order_d M D E D)
    (compose : Generic_d M D E D (Compose_generic_d M Q T w D H (Qgeneric_d j G))) :
    Miso_over_d (extension_l M hZF L V d G)
      (extension_l M hZF D E D (Compose_generic_d M Q T w D H (Qgeneric_d j G)))
      (Gval_d M L V d G) (Gval_d M D E D (Compose_generic_d M Q T w D H (Qgeneric_d j G))) := by
  obtain ⟨C,R,F,k⟩ := h.conditions_l hZF c
  have OC := k.order_l hZF h
  have OL := cond_order_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) h.target
  obtain ⟨a,ha,ca⟩ := h.principal.2.2 c cu
  obtain ⟨y,hy,ay⟩ := h.hom.function.2.2 a ha
  have gy := (read a y ay).mpr ⟨c,hc,((h.graph c a).mp ca).2.2.1⟩
  have regular := k.regular_l hZF h ca ay
  have left := regular.dense_ground_l hZF OC OL k.function.1.2 big gy
    (fun x hx => k.dense_l hZF h ca ay hx.1 hx.2.1 hx.2.2)
  obtain ⟨K,fn,graph,map⟩ := k.step_map_l hZF h hb cb name relation step OD
  have same : Pull_generic_d M F G = Pull_generic_d M K (Compose_generic_d M Q T w D H (Qgeneric_d j G)) := by
    funext v
    apply propext
    constructor
    · rintro ⟨x,vx,gx⟩
      have hv := k.function.input_mem_of_pairMember vx
      obtain ⟨t,ht,vt⟩ := fn.2.2 v hv
      obtain ⟨_,q,y,s,pair,check,out⟩ := (graph v t).mp vt
      have accepted := (k.accept_l hZF h small big read pair vx).mp gx
      exact ⟨t,vt,ht,q,s,j y,out,accepted.1,checks y s check,y,accepted.2,rfl⟩
    · rintro ⟨t,vt,_,q,s,z,pair,hq,value,x,gx,xz⟩
      obtain ⟨hv,q',x',s',out,check,pair'⟩ := (graph v t).mp vt
      obtain ⟨eq₁,eq₂⟩ := kpair_injective_l M pair pair'
      subst q' s'
      have x'x : x' = x := inj ((qval_unique_l (checks x' s check) value).trans xz.symm)
      subst x'
      obtain ⟨y,_,vy⟩ := k.function.2.2 v hv
      exact ⟨y,vy,(k.accept_l hZF h small big read out vy).mpr ⟨hq,gx⟩⟩
  have right : Miso_over_d (extension_l M hZF C R C (Pull_generic_d M F G))
      (extension_l M hZF D E D (Compose_generic_d M Q T w D H (Qgeneric_d j G)))
      (Gval_d M C R C (Pull_generic_d M F G))
      (Gval_d M D E D (Compose_generic_d M Q T w D H (Qgeneric_d j G))) := by
    rw [same]
    exact map.ground_l hZF OC OD compose
  exact left.symm_l.trans_l right

end YesMetaZFC.Model.Forcing.Internal
