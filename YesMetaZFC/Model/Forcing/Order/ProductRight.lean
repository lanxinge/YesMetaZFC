import YesMetaZFC.Model.Forcing.TwoStep.Basic
import YesMetaZFC.SetTheory.FunctionConstruction
import YesMetaZFC.Model.Forcing.Stage.Extension
import YesMetaZFC.Model.Forcing.Stage.NameMap.Check
import YesMetaZFC.Model.Forcing.Ground.Collapse

/-! # 两个地模型条件序的内部积

条件和序关系都是实际集合图，两个坐标同时加强。
排除值取整个条件域，基础公理保证没有条件等于它。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

structure Prod_d (Q T P U C R : M.Domain) : Prop where
  pair : M.IsCartesianProduct I C Q P
  order : ∀ c d, Entry_d M c d R ↔ M.mem c C ∧ M.mem d C ∧
    ∃ q p r s, KPair_d M c q p ∧ KPair_d M d r s ∧ Entry_d M q r T ∧ Entry_d M p s U

theorem Prod_d.components_l {Q T P U C R c q p : M.Domain} (h : Prod_d hZF Q T P U C R)
    (hc : M.mem c C) (pair : KPair_d M c q p) : M.mem q Q ∧ M.mem p P := by
  obtain ⟨q',hq,p',hp,pair'⟩ := (h.pair c).mp hc
  obtain ⟨rfl,rfl⟩ := kpair_injective_l M pair pair'
  exact ⟨hq,hp⟩

theorem Prod_d.pair_order_l {Q T P U C R c d q p r s : M.Domain} (h : Prod_d hZF Q T P U C R)
    (hc : M.mem c C) (hd : M.mem d C) (cp : KPair_d M c q p) (ds : KPair_d M d r s) :
    Entry_d M c d R ↔ Entry_d M q r T ∧ Entry_d M p s U := by
  constructor
  · intro cd
    obtain ⟨_,_,q',p',r',s',cp',ds',qr,ps⟩ := (h.order c d).mp cd
    obtain ⟨rfl,rfl⟩ := kpair_injective_l M cp' cp
    obtain ⟨rfl,rfl⟩ := kpair_injective_l M ds' ds
    exact ⟨qr,ps⟩
  · exact fun h' => (h.order c d).mpr ⟨hc,hd,q,p,r,s,cp,ds,h'⟩

theorem product_order_l {Q T P U : M.Domain}
    (O : Cond_order_d M Q T Q) (L : Cond_order_d M P U P) :
    ∃ C R, Prod_d hZF Q T P U C R ∧ Cond_order_d M C R C := by
  obtain ⟨C,pair⟩ := ZF.exists_cartesianProduct hZF I Q P
  let ρ : Env M 2 := ⟨Fin.cases T (fun _ => U),fun _ => T⟩
  let φ : BinarySchema 2 := {
    body := set[4] ⟪∃ q p r s,
      ⌜kpair_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,q,p) ∧ ⌜kpair_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,r,s) ∧
      ⌜entry_m⌝ₚ(q,r,⌜(.bound 2 : Term 4)⌝ₛ) ∧ ⌜entry_m⌝ₚ(p,s,⌜(.bound 3 : Term 4)⌝ₛ)⟫ }
  have sat c d : φ.denote ρ c d ↔
      ∃ q p r s, KPair_d M c q p ∧ KPair_d M d r s ∧ Entry_d M q r T ∧ Entry_d M p s U := by
    simp only [BinarySchema.denote,φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1,entry_sat_l M hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨R,_,graph⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ C
  have order c d := (graph c d).trans (and_congr_right fun _ => and_congr_right fun _ => sat c d)
  have coeff {c q p} (hc : M.mem c C) (cp : KPair_d M c q p) : M.mem q Q ∧ M.mem p P := by
    obtain ⟨q',hq,p',hp,cp'⟩ := (pair c).mp hc
    obtain ⟨rfl,rfl⟩ := kpair_injective_l M cp cp'
    exact ⟨hq,hp⟩
  refine ⟨C,R,⟨pair,order⟩,⟨?_,?_,?_⟩⟩
  · intro c hc
    obtain ⟨q,hq,p,hp,cp⟩ := (pair c).mp hc
    exact (order c c).mpr ⟨hc,hc,q,p,q,p,cp,cp,O.refl q hq,L.refl p hp⟩
  · intro c d e hc hd he cd de
    obtain ⟨_,_,q,p,r,s,cp,dr,qr,ps⟩ := (order c d).mp cd
    obtain ⟨_,_,r',s',v,w,dr',ev,rv,sw⟩ := (order d e).mp de
    obtain ⟨eqr,eqs⟩ := kpair_injective_l M dr' dr
    subst r' s'
    exact (order c e).mpr ⟨hc,he,q,p,v,w,cp,ev,
      O.trans q r v (coeff hc cp).1 (coeff hd dr).1 (coeff he ev).1 qr rv,
      L.trans p s w (coeff hc cp).2 (coeff hd dr).2 (coeff he ev).2 ps sw⟩
  · intro c _ cC
    exact (KP.mem_irrefl_d (ZF.modelsKP hZF) C ((order c C).mp cC).2.1).elim

theorem Prod_d.top_l {Q T P U C R b a c : M.Domain}
    (h : Prod_d hZF Q T P U C R) (hb : M.mem b Q) (ha : M.mem a P)
    (qt : ∀ q, M.mem q Q → Entry_d M q b T) (pt : ∀ p, M.mem p P → Entry_d M p a U)
    (pair : KPair_d M c b a) : M.mem c C ∧ ∀ d, M.mem d C → Entry_d M d c R := by
  have hc := (h.pair c).mpr ⟨b,hb,a,ha,pair⟩
  refine ⟨hc,fun d hd => ?_⟩
  obtain ⟨q,hq,p,hp,dp⟩ := (h.pair d).mp hd
  exact (h.order d c).mpr ⟨hd,hc,q,p,b,a,dp,pair,qt q hq,pt p hp⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 同一实际积条件序的一阶规格 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

def prod_m {n} (Q T P U C R : Term n) : Formula 1 n := set[n] ⟪
  ⌜(Formula.isCartesianProduct kpair_convention_l)⌝ₚ(⌜C⌝ₛ,⌜Q⌝ₛ,⌜P⌝ₛ) ∧
  (∀ c d, ⌜entry_m⌝ₚ(c,d,⌜R⌝ₛ) ↔ c ∈ ⌜C⌝ₛ ∧ d ∈ ⌜C⌝ₛ ∧
    (∃ q p r s, ⌜kpair_m⌝ₚ(c,q,p) ∧ ⌜kpair_m⌝ₚ(d,r,s) ∧
      ⌜entry_m⌝ₚ(q,r,⌜T⌝ₛ) ∧ ⌜entry_m⌝ₚ(p,s,⌜U⌝ₛ)))⟫
derive_free_closed prod_m

theorem prod_sat_l {n} (ρ : Env M n) (Q T P U C R : Term n) :
    Formula.satisfies ρ (prod_m Q T P U C R) ↔
      Prod_d hZF (Q.eval ρ) (T.eval ρ) (P.eval ρ) (U.eval ρ) (C.eval ρ) (R.eval ρ) := by
  simp only [prod_m,Formula.satisfies_conj_iff,Formula.satisfies_isCartesianProduct_iff I,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,entry_sat_l M hZF.1,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,kpair_sat_l M hZF.1,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b⟩ => ⟨a,b⟩,fun h => ⟨h.pair,h.order⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 积偏序右坐标的实际正则嵌入

右条件 p 映到〈左顶,p〉。任意积条件的右坐标是约减，保持左坐标即可
与每个加强相容。积泛型回拉后，两个扩张之间的成员满映射固定全部地参数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Prod_d.right_map_l {Q T P U C R b : M.Domain} (product : Prod_d hZF Q T P U C R)
    (O : Cond_order_d M Q T Q) (L : Cond_order_d M P U P) (hb : M.mem b Q)
    (top : ∀ q, M.mem q Q → Entry_d M q b T) :
    ∃ F, M.IsSetFunctionFromTo I F P C ∧
      (∀ p c, Entry_d M p c F ↔ M.mem p P ∧ KPair_d M c b p) ∧ Reg_map_d M P U P C R C F := by
  let ρ : Env M 1 := ⟨fun _ => b,fun _ => b⟩
  let φ : BinarySchema 1 := { body := kpair_m .newest (.bound 2) (.bound 1) }
  have sat p c : φ.denote ρ p c ↔ KPair_d M c b p := kpair_sat_l M hZF.1 ..
  obtain ⟨F,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := P) (target := C)
    (fun p _ => ((I).total b p).imp fun c pair => (sat p c).mpr pair)
    (fun p _ c d hc hd => (I).unique ((sat p c).mp hc) ((sat p d).mp hd))
    (fun p c hp hc => (product.pair c).mpr ⟨b,hb,p,hp,(sat p c).mp hc⟩)
  have graph p c := (values p c).trans (and_congr_right fun _ => sat p c)
  have nz {x A : M.Domain} (hx : M.mem x A) : x ≠ A := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) A (eq ▸ hx)
  refine ⟨F,fn,graph,⟨fun p hp _ => (fn.2.2 p hp).imp fun _ h => h.2,?_,?_,?_,?_⟩⟩
  · intro p c pc
    exact ⟨fn.input_mem_of_pairMember pc,nz (fn.input_mem_of_pairMember pc),fn.output_mem_of_pairMember pc,nz (fn.output_mem_of_pairMember pc)⟩
  · intro p q c d pc qd pq
    exact (product.pair_order_l hZF (fn.output_mem_of_pairMember pc) (fn.output_mem_of_pairMember qd)
      ((graph p c).mp pc).2 ((graph q d).mp qd).2).mpr ⟨O.refl b hb,pq⟩
  · intro p q c d pc qd compat
    obtain ⟨v,vc,vd⟩ := compat
    obtain ⟨r,hr,s,hs,pair⟩ := (product.pair v).mp vc.1
    exact ⟨s,⟨hs,nz hs,((product.pair_order_l hZF vc.1 (fn.output_mem_of_pairMember pc)
      pair ((graph p c).mp pc).2).mp vc.2.2).2⟩,
      ((product.pair_order_l hZF vc.1 (fn.output_mem_of_pairMember qd) pair ((graph q d).mp qd).2).mp vd).2⟩
  · intro c hc _ _ _ _ _
    obtain ⟨q,hq,p,hp,pair⟩ := (product.pair c).mp hc
    refine ⟨p,hp,nz hp,fun r d rd rp => ?_⟩
    have hr := fn.input_mem_of_pairMember rd
    obtain ⟨v,vr⟩ := (I).total q r
    have hv := (product.pair v).mpr ⟨q,hq,r,hr,vr⟩
    exact ⟨v,⟨hv,nz hv,(product.pair_order_l hZF hv hc vr pair).mpr ⟨O.refl q hq,rp⟩⟩,
      (product.pair_order_l hZF hv (fn.output_mem_of_pairMember rd) vr ((graph r d).mp rd).2).mpr ⟨top q hq,L.refl r hr⟩⟩

/-- 任意积泛型实际包含右坐标像，故右因子扩张嵌入积扩张并固定地模型。 -/
theorem Prod_d.right_extension_l {Q T P U C R b : M.Domain} (product : Prod_d hZF Q T P U C R)
    (O : Cond_order_d M Q T Q) (L : Cond_order_d M P U P) (K : Cond_order_d M C R C)
    (hb : M.mem b Q) (top : ∀ q, M.mem q Q → Entry_d M q b T)
    {G : M.Domain → Prop} (generic : Generic_d M C R C G) :
    ∃ H : M.Domain → Prop, Generic_d M P U P H ∧
      ∃ e : (extension_l M hZF P U P H).Domain → (extension_l M hZF C R C G).Domain,
        Function.Injective e ∧ (∀ a y, y ∈ e a ↔ ∃ x, x ∈ a ∧ e x = y) ∧
        ∀ x a, Gval_d M P U P H x a → Gval_d M C R C G x (e a) := by
  obtain ⟨F,fn,graph,map⟩ := product.right_map_l hZF O L hb top
  obtain ⟨c,hc⟩ := generic.inhabited
  obtain ⟨q,hq,p,hp,pair⟩ := (product.pair c).mp (generic.proper c hc).1
  obtain ⟨d,hd,pd⟩ := fn.2.2 p hp
  have cd := (product.pair_order_l hZF (generic.proper c hc).1 hd pair ((graph p d).mp pd).2).mpr ⟨top q hq,L.refl p hp⟩
  have hit : ∃ p, Pull_generic_d M F G p := ⟨p,d,pd,generic.upward c d hc hd cd⟩
  obtain ⟨e,values,full,inj⟩ := stage_extension_l L K hZF map generic hit
  refine ⟨Pull_generic_d M F G,reg_generic_l L K hZF map generic hit,e,inj,full,?_⟩
  rintro x a ⟨p,s,⟨q,pq,hq⟩,check,value⟩
  obtain ⟨t,ct,_,_⟩ := zf_check_l M hZF (generic.proper q hq).1 x
  have moved := nmap_check_l hZF (fun r => ⟨fun pr => fn.1.2 p r q pr pq,fun eq => eq.symm ▸ pq⟩) check ct
  exact ⟨q,t,hq,ct,values a s t value moved⟩

end YesMetaZFC.Model.Forcing.Internal
