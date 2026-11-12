import YesMetaZFC.Model.Forcing.Order.ProductRight
import YesMetaZFC.Model.Forcing.Boolean.DenseGround
import YesMetaZFC.Model.Forcing.TwoStep.Order
import YesMetaZFC.Model.Forcing.Check.Order

/-! # 地模型积与常值二步迭代

(q,p) 映为 (q,check(p))。名字成员匹配给出每个二步条件以下的旧条件，
旧关系的规范名字反映顺序，因此这张实际图稠密且保持、反映序。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Prod_d.step_map_l {Q T P U C R b A ν W D E : M.Domain}
    (product : Prod_d hZF Q T P U C R)
    (O : Cond_order_d M Q T Q) (L : Cond_order_d M P U P)
    (hb : M.mem b Q) (top : ∀ q, M.mem q Q → Entry_d M q b T)
    (name : Check_d M b P A) (relation : Check_d M b U ν)
    (step : Two_step_d M Q T Q b A ν W D E) (OD : Cond_order_d M D E D) :
    ∃ F, M.IsSetFunctionFromTo I F C D ∧
      (∀ v t, Entry_d M v t F ↔ M.mem v C ∧ ∃ q p s,
        KPair_d M v q p ∧ Check_d M b p s ∧ KPair_d M t q s) ∧ Dmap_d C R C D E D F := by
  have below {q} (hq : M.mem q Q) : Below_d M Q T Q q b :=
    ⟨hq,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) Q (eq ▸ hq),top q hq⟩
  have coeff {v q p} (hv : M.mem v C) (pair : KPair_d M v q p) : M.mem q Q ∧ M.mem p P := by
    obtain ⟨q',hq,p',hp,pair'⟩ := (product.pair v).mp hv
    obtain ⟨eq₁,eq₂⟩ := kpair_injective_l M pair' pair
    exact ⟨eq₁ ▸ hq,eq₂ ▸ hp⟩
  have mapped {v q p s t} (hv : M.mem v C) (pair : KPair_d M v q p)
      (check : Check_d M b p s) (out : KPair_d M t q s) : M.mem t D := by
    have hp := coeff hv pair
    have entry := (check_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) name s b).mpr
      ⟨rfl,p,hp.2,check⟩
    exact (two_step_mem_l step out).mpr ⟨(supp_entry_l M step.closed step.root entry).1,
      below hp.1,check_mem_force_l O hZF hb check name hp.1 (top q hp.1) hp.2⟩
  let ρ : Env M 1 := ⟨fun _ => b,fun _ => b⟩
  let φ : BinarySchema 1 := { body := set[3] ⟪∃ q p s,
    ⌜kpair_m⌝ₚ(⌜(.bound 1 : Term 3)⌝ₛ,q,p) ∧ ⌜check_m⌝ₚ(⌜(.bound 2 : Term 3)⌝ₛ,p,s) ∧
      ⌜kpair_m⌝ₚ(⌜(.newest : Term 3)⌝ₛ,q,s)⟫ }
  have sat v t : φ.denote ρ v t ↔ ∃ q p s, KPair_d M v q p ∧ Check_d M b p s ∧ KPair_d M t q s := by
    simp only [BinarySchema.denote,φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1,check_sat_l M hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨F,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := C) (target := D)
    (fun v hv => by
      obtain ⟨q,_,p,_,pair⟩ := (product.pair v).mp hv
      obtain ⟨s,check,_,_⟩ := zf_check_l M hZF hb p
      obtain ⟨t,out⟩ := (I).total q s
      exact ⟨t,(sat v t).mpr ⟨q,p,s,pair,check,out⟩⟩)
    (by
      intro v _ t t' ht ht'
      obtain ⟨q,p,s,pair,check,out⟩ := (sat v t).mp ht
      obtain ⟨q',p',s',pair',check',out'⟩ := (sat v t').mp ht'
      obtain ⟨eq₁,eq₂⟩ := kpair_injective_l M pair pair'
      subst q' p'
      have eq := check_unique_l M hZF.1 (check_ind_l M hZF) b p s s' check check'
      subst s'
      exact kpair_unique_l M hZF.1 out out')
    (by
      intro v t hv ht
      obtain ⟨q,p,s,pair,check,out⟩ := (sat v t).mp ht
      exact mapped hv pair check out)
  have graph v t := (values v t).trans (and_congr_right fun _ => sat v t)
  have domain v t (vt : Entry_d M v t F) : (M.mem v C ∧ v ≠ C) ∧ M.mem t D ∧ t ≠ D :=
    ⟨⟨fn.input_mem_of_pairMember vt,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ fn.input_mem_of_pairMember vt)⟩,
      fn.output_mem_of_pairMember vt,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) D (eq ▸ fn.output_mem_of_pairMember vt)⟩
  refine ⟨F,fn,graph,dmap_of_order_l OD (fun v hv _ => (fn.2.2 v hv).imp fun t ht => ht.2) domain fn.1.2 ?_ ?_⟩
  · intro v v' t t' vt vt'
    obtain ⟨hv,q,p,s,pair,check,out⟩ := (graph v t).mp vt
    obtain ⟨hv',q',p',s',pair',check',out'⟩ := (graph v' t').mp vt'
    have hq := (coeff hv pair).1
    apply (two_step_le_l step (fn.output_mem_of_pairMember vt) (fn.output_mem_of_pairMember vt') out out').trans
    constructor
    · rintro ⟨qq,force⟩
      exact (product.order v v').mpr ⟨hv,hv',q,p,q',p',pair,pair',qq.2.2,
        check_rel_reflect_l O hZF hb relation check check' (below hq) force⟩
    · intro vv
      obtain ⟨_,_,r,x,r',x',px,px',rr,xx⟩ := (product.order v v').mp vv
      obtain ⟨eq₁,eq₂⟩ := kpair_injective_l M px pair
      obtain ⟨eq₃,eq₄⟩ := kpair_injective_l M px' pair'
      subst r x r' x'
      exact ⟨⟨hq,(below hq).2.1,rr⟩,check_rel_force_l O hZF hb relation check check' (below hq) xx⟩
  · intro t ht _
    obtain ⟨q,s,pair,sW,hq,member⟩ := (step.conditions t).mp ht
    have ns : Name_d M Q s := ⟨W,sW,step.closed⟩
    obtain ⟨r,a,k,rq,ak,_,eq⟩ := member.2 q (below_refl_l O hq.1 hq.2.1)
    obtain ⟨_,p,hp,check⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
      (KP.exists_pair (ZF.modelsKP hZF)) name a k).mp ak
    have na := check_name_l M (check_range_l M hZF) hb check
    obtain ⟨v,out⟩ := (I).total r p
    have hv := (product.pair v).mpr ⟨r,rq.1,p,hp,out⟩
    obtain ⟨t',ht',vt⟩ := fn.2.2 v hv
    obtain ⟨_,r',p',a',out',check',pair'⟩ := (graph v t').mp vt
    obtain ⟨rr,pp⟩ := kpair_injective_l M out out'
    subst r' p'
    have aa := check_unique_l M hZF.1 (check_ind_l M hZF) b p a a' check check'
    subst a'
    have nv := check_name_l M (check_range_l M hZF) hb relation
    have refl := check_rel_force_l O hZF hb relation check check (below rq.1) (L.refl p hp)
    have rel := (rel_force_congr_l O hZF nv na na na ns rq.1 rq.2.1
      (eq_force_refl_l O hZF rq.1 na) (eq_force_symm_l hZF ns na eq)).mp refl
    exact ⟨v,t',vt,(two_step_le_l step ht' ht pair' pair).mpr ⟨rq,rel⟩⟩

end YesMetaZFC.Model.Forcing.Internal
