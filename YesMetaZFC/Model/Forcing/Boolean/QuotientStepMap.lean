import YesMetaZFC.Model.Forcing.Boolean.QuotientComparison
import YesMetaZFC.Model.Forcing.TwoStep.Order
import YesMetaZFC.Model.Forcing.Check.Order

/-! # 共同条件序到实际二步迭代的稠密映射

(q,x) 映为 (q,check(x))。任意二步名称条件经一次成员匹配，可加强到这样的旧条件。
旧关系的检查名字反映真实顺序，因而此映射保持并反映序。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
variable {Q T w u A S e L V d J P N c C R F b τ ν W D E : M.Domain}

theorem Qcp_d.step_map_l (k : Qcp_d hZF Q T w c L V d J P N C R F)
    (h : Qc_d hZF Q T w u A S e L V d J P N) (hb : M.mem b Q) (cb : Entry_d M c b T)
    (name : Qname_d Q b L d P τ) (relation : Check_d M b V ν)
    (step : Two_step_d M Q T w c τ ν W D E) (OD : Cond_order_d M D E D) :
    ∃ K, M.IsSetFunctionFromTo I K C D ∧
      (∀ v t, Entry_d M v t K ↔ M.mem v C ∧ ∃ q x s,
        KPair_d M v q x ∧ Check_d M b x s ∧ KPair_d M t q s) ∧ Dmap_d C R C D E D K := by
  have regular a (ha : M.mem a A) := ((h.family a).mp ha).1
  have below {q} (hq : Below_d M Q T w q c) : Below_d M Q T w q b :=
    ⟨hq.1,hq.2.1,h.small.trans q c b hq.1 step.base hb hq.2.2 cb⟩
  have mapped {v q x s t} (hv : M.mem v C) (pair : KPair_d M v q x)
      (check : Check_d M b x s) (out : KPair_d M t q s) : M.mem t D := by
    obtain ⟨hq,nz,a,xa,qa⟩ := (k.mem_l hZF pair).mp hv
    have xs := (name.2 s q).mpr ⟨hq.1,x,a,h.projection.input_mem_of_pairMember xa,nz,check,xa,qa⟩
    exact (two_step_mem_l step out).mpr ⟨(supp_entry_l M step.closed step.root xs).1,hq,
      (name.force_l hZF h.small hb h.projection regular xa check (below hq)).mpr ⟨nz,qa⟩⟩
  let ρ : Env M 1 := ⟨fun _ => b,fun _ => b⟩
  let φ : BinarySchema 1 := { body := set[3] ⟪ ∃ q, ∃ x, ∃ s,
    ⌜kpair_m⌝ₚ(⌜(.bound 1 : Term 3)⌝ₛ,q,x) ∧ ⌜check_m⌝ₚ(⌜(.bound 2 : Term 3)⌝ₛ,x,s) ∧
    ⌜kpair_m⌝ₚ(⌜(.newest : Term 3)⌝ₛ,q,s)⟫ }
  have sat v t : φ.denote ρ v t ↔ ∃ q x s, KPair_d M v q x ∧ Check_d M b x s ∧ KPair_d M t q s := by
    simp only [BinarySchema.denote,φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1,check_sat_l M hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨K,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := C) (target := D) (fun v hv => by
    obtain ⟨q,x,pair⟩ := k.graph v hv
    obtain ⟨s,check,_,_⟩ := zf_check_l M hZF hb x
    obtain ⟨t,out⟩ := (I).total q s
    exact ⟨t,(sat v t).mpr ⟨q,x,s,pair,check,out⟩⟩) (by
      intro v _ t t' ht ht'
      obtain ⟨q,x,s,pair,check,out⟩ := (sat v t).mp ht
      obtain ⟨q',x',s',pair',check',out'⟩ := (sat v t').mp ht'
      obtain ⟨eq₁,eq₂⟩ := kpair_injective_l M pair pair'
      subst q' x'
      have eq := check_unique_l M hZF.1 (check_ind_l M hZF) b x s s' check check'
      subst s'
      exact kpair_unique_l M hZF.1 out out') (by
      intro v t hv ht
      obtain ⟨q,x,s,pair,check,out⟩ := (sat v t).mp ht
      exact mapped hv pair check out)
  have graph v t := (values v t).trans (and_congr_right fun _ => sat v t)
  have domain v t (vt : Entry_d M v t K) : (M.mem v C ∧ v ≠ C) ∧ M.mem t D ∧ t ≠ D :=
    ⟨⟨fn.input_mem_of_pairMember vt,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ fn.input_mem_of_pairMember vt)⟩,
      fn.output_mem_of_pairMember vt,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) D (eq ▸ fn.output_mem_of_pairMember vt)⟩
  refine ⟨K,fn,graph,dmap_of_order_l OD (fun v hv _ => (fn.2.2 v hv).imp fun t ht => ht.2) domain fn.1.2 ?_ ?_⟩
  · intro v v' t t' vt vt'
    obtain ⟨hv,q,x,s,pair,check,out⟩ := (graph v t).mp vt
    obtain ⟨hv',q',x',s',pair',check',out'⟩ := (graph v' t').mp vt'
    have hq := ((k.mem_l hZF pair).mp hv).1
    apply (two_step_le_l step (fn.output_mem_of_pairMember vt) (fn.output_mem_of_pairMember vt') out out').trans
    apply Iff.trans ?_ (k.le_l hZF hv hv' pair pair').symm
    exact ⟨fun ⟨qq,force⟩ => ⟨qq.2.2,check_rel_reflect_l h.small hZF hb relation check check' (below hq) force⟩,
      fun ⟨qq,xx⟩ => ⟨⟨hq.1,hq.2.1,qq⟩,check_rel_force_l h.small hZF hb relation check check' (below hq) xx⟩⟩
  · intro t ht _
    obtain ⟨q,s,pair,sW,hq,member⟩ := (step.conditions t).mp ht
    have ns : Name_d M Q s := ⟨W,sW,step.closed⟩
    obtain ⟨r,a,p,rq,ap,rp,eq⟩ := member.2 q (below_refl_l h.small hq.1 hq.2.1)
    obtain ⟨hp,x,b',hx,nz,check,xb,pb⟩ := (name.2 a p).mp ap
    have na := check_name_l M (check_range_l M hZF) hb check
    have rc := below_trans_l h.small step.base rq hq
    have rb' := (regular b' (h.projection.output_mem_of_pairMember xb)).2.1 p r hp ⟨rq.1,rq.2.1,rp⟩ pb
    obtain ⟨v,out⟩ := (I).total r x
    have hv := (k.mem_l hZF out).mpr ⟨rc,nz,b',xb,rb'⟩
    obtain ⟨t',ht',vt⟩ := fn.2.2 v hv
    obtain ⟨_,r',x',a',out',check',pair'⟩ := (graph v t').mp vt
    obtain ⟨rr,xx⟩ := kpair_injective_l M out out'
    subst r' x'
    have aa := check_unique_l M hZF.1 (check_ind_l M hZF) b x a a' check check'
    subst a'
    have nv := check_name_l M (check_range_l M hZF) hb relation
    have refl := check_rel_force_l h.small hZF hb relation check check (below rc) (h.target.order.refl x hx)
    have rel := (rel_force_congr_l h.small hZF nv na na na ns rq.1 rq.2.1
      (eq_force_refl_l h.small hZF rq.1 na) (eq_force_symm_l hZF ns na eq)).mp refl
    exact ⟨v,t',vt,(two_step_le_l step ht' ht pair' pair).mpr ⟨rq,rel⟩⟩

end YesMetaZFC.Model.Forcing.Internal
