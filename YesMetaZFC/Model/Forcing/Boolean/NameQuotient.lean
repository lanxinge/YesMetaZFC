import YesMetaZFC.Model.Forcing.Boolean.NameComplete
import YesMetaZFC.Model.Forcing.Boolean.QuotientIteration
import YesMetaZFC.Model.Forcing.Boolean.QuotientIdentification
import YesMetaZFC.Model.Forcing.Boolean.QuotientTrace
import YesMetaZFC.Model.Forcing.TwoStep.Names.Check

/-! # 名字同态的核约化与实际中间商

小泛型由原名字精确读取，主核给出忠实区间。商载体在该小泛型的规范扩张中
构造。规范投影将商条件刻画为首阶段泛型接受的投影值，实际加权名字解释为
同一个商载体。原大泛型命中的正则开集诱导商泛型，命中中间模型全部稠密集。
共同条件序识别原大扩张与组合二步扩张，名称摊平再给出 M[G]≅M[H][K]。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Nh_d.quotient_l {B R z b p Q T w 𝒟 τ K S e C L V d F : M.Domain}
    (h : Nh_d hZF B R z b p Q T w 𝒟 τ K S e C L V d F)
    {G : M.Domain → Prop} (generic : Generic_d M B R z G) (hp : G p) :
    ∃ H : M.Domain → Prop, ∃ small : Generic_d M Q T w H,
      (∀ q, H q ↔ ∃ a, Check_d M b q a ∧ ∃ r, G r ∧ Mem_force_d M B R z r a τ) ∧
      ∃ A J, M.MemberSubset A K ∧ (∃ a, M.mem a A ∧ ∃ q, H q ∧ M.mem q a) ∧
        M.IsRestrictionOf I J F A ∧ BooleanZF.Cba_d I A S e ∧
        BooleanZF.Cbh_d I A S e L V d J ∧ M.IsSetInjectionFromTo I J A L ∧
        ∃ P, M.IsSetFunctionFromTo I P L A ∧
          (∀ X a, Entry_d M X a P ↔ BooleanZF.Badj_d I A S L V J X a) ∧
        ∃ c, H c ∧ ∃ j : M.Domain → (extension_l M hZF Q T w H).Domain, Function.Injective j ∧
          (∀ a y, (extension_l M hZF Q T w H).mem y (j a) ↔ ∃ c, M.mem c a ∧ j c = y) ∧
          (∀ a t, Check_d M c a t → Qval_d M Q T w H t (j a)) ∧
          ∃ D : (extension_l M hZF Q T w H).Domain,
            Qread_d j H A L V d J D ∧ Cond_order_d (extension_l M hZF Q T w H) D (j V) (j d) ∧
            (∀ X a, Entry_d M X a P →
              ((extension_l M hZF Q T w H).mem (j X) D ↔ X ≠ d ∧ ∃ q, H q ∧ M.mem q a)) ∧
            Generic_d (extension_l M hZF Q T w H) D (j V) (j d)
              (Qgeneric_d j (fun X => M.mem X L ∧ ∃ q, G q ∧ M.mem q X)) ∧
            ∃ Γ, M.IsSetFunctionFromTo I Γ C L ∧
              (∀ q X, Entry_d M q X Γ → Rpr_d B R z q X) ∧ Qtrace_d j B R z Γ D ∧
            ∃ ξ ν, Qname_d Q c L d P ξ ∧ Qval_d M Q T w H ξ D ∧ Qval_d M Q T w H ν (j V) ∧
            let U := Qgeneric_d j (fun X => M.mem X L ∧ ∃ q, G q ∧ M.mem q X)
            ∃ b' W C' S' J', H b' ∧ Two_step_d M Q T w b' ξ ν W C' S' ∧ Cond_order_d M C' S' C' ∧
              (∀ x y, Entry_d (extension_l M hZF Q T w H) x y J' ↔
                (extension_l M hZF Q T w H).mem x D ∧ (extension_l M hZF Q T w H).mem y D ∧
                Entry_d (extension_l M hZF Q T w H) x y (j V)) ∧
              Cond_order_d (extension_l M hZF Q T w H) D J' D ∧
              Generic_d (extension_l M hZF Q T w H) D J' D U ∧
              Generic_d M C' S' C' (Compose_generic_d M Q T w C' H U) ∧
              (∀ q, First_generic_d M Q T (Compose_generic_d M Q T w C' H U) q ↔ H q) ∧
              ∃ f : (extension_l M hZF C' S' C' (Compose_generic_d M Q T w C' H U)).Domain →
                  (extension_l (extension_l M hZF Q T w H) (preserves_zf_l h.small hZF small) D J' D U).Domain,
                (∀ a t, Qval_d M C' S' C' (Compose_generic_d M Q T w C' H U) t a →
                  Curry_val_d M hZF Q T w C' H D J' U t (f a)) ∧
                (∀ a b, a ∈ b ↔ f a ∈ f b) ∧ Function.Injective f ∧ Function.Surjective f ∧
                Miso_over_d (extension_l M hZF B R z G)
                  (extension_l (extension_l M hZF Q T w H) (preserves_zf_l h.small hZF small) D J' D U)
                  (Gval_d M B R z G) (fun x => Gval_d (extension_l M hZF Q T w H) D J' D U (j x)) := by
  obtain ⟨H,small,original,read⟩ := h.read_l hZF generic hp
  obtain ⟨_,k,u,A,J,_,_,zero,neg,carrier,cut,algebra,hom,inj,_,_,_⟩ :=
    (h.complete_l hZF).kernel_l I hZF h.source h.target.toBoolean_d
  have sub : M.MemberSubset A K := fun a ha => ((carrier a).mp ha).1
  -- 核在实际泛型中被拒绝，故其补被接受；忠实区间中确有被接受的元素。
  have hitU : ∃ q, H q ∧ M.mem q u :=
    (ropen_hit_neg_l hZF h.small h.family h.order small h.source.toBoolean_d h.empty
      (h.function.input_mem_of_pairMember zero) neg).mpr (fun hit => by
        obtain ⟨q,_,qd⟩ := (read k d zero).mpr hit
        exact h.localEmpty q qd)
  have hu := (carrier u).mpr ⟨neg.1,h.source.order.refl u neg.1⟩
  have interval : BooleanZF.Bi_d I K S u A := ⟨neg.1,carrier⟩
  obtain ⟨P,projection,adjoint⟩ := hom.adjoint_l I hZF algebra h.target.toBoolean_d
  obtain ⟨c,hc,j,ji,full,checks,D,quotient⟩ := quotient_intermediate_l hZF (V := V) (d := d) h.small small hom.function
  have hE := extension_ext_l h.small hZF small
  have order := quotient.order_l hZF hE ji full (cond_order_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) h.target.toBoolean_d)
  have criterion X a (xa : Entry_d M X a P) := quotient.projection_l hZF h.small h.family h.order
    h.source.toBoolean_d h.empty small ji interval hitU h.target.toBoolean_d hom.toBh_d ((adjoint X a).mp xa)
  obtain ⟨ξ,name⟩ := qname_exists_l hZF (small.proper c hc).1 L d P
  obtain ⟨D',value⟩ := name_value_l (R := T) (z := w) (U := H) name.1
  have eq : D' = D := hE.eq_of_same_members D' D (fun y => by
    apply (name.value_l hZF h.small small value j checks y).trans
    constructor
    · rintro ⟨X,a,_,nz,xa,hit,rfl⟩
      exact (criterion X a xa).mpr ⟨nz,hit⟩
    · intro hy
      obtain ⟨X,hx,_,rfl,_⟩ := (quotient y).mp hy
      obtain ⟨a,_,xa⟩ := projection.2.2 X hx
      have accepted := (criterion X a xa).mp hy
      exact ⟨X,a,hx,accepted.1,xa,accepted.2,rfl⟩)
  subst D'
  have targetGeneric := ropen_local_generic_l hZF h.big h.localFamily h.localOrder h.localEmpty h.cone generic ⟨p,hp,h.point⟩
  have correspondence a X (ax : Entry_d M a X J) :
      (M.mem X L ∧ ∃ q, G q ∧ M.mem q X) ↔ ∃ q, H q ∧ M.mem q a := by
    have eq := read a X ((cut.2 a X).mp ax).2
    exact ⟨fun hit => eq.mp hit.2,fun hit => ⟨hom.function.output_mem_of_pairMember ax,eq.mpr hit⟩⟩
  have quotientGeneric := quotient_generic_l hZF h.small h.family h.order h.source.toBoolean_d h.empty interval h.target.toBoolean_d
    hom.toBh_d projection (fun X a xa => (adjoint X a).mp xa) small targetGeneric correspondence
    hitU hc name j ji full checks quotient value
  obtain ⟨Γ,basis,principalBasis⟩ := rpr_graph_l hZF h.big h.cone h.localFamily
  have basisGraph q X (qX : Entry_d M q X Γ) := ((principalBasis q X).mp qX).2
  have trace : Qtrace_d j B R z Γ D := by
    intro E X hX dense
    have hx : M.mem X L := by
      obtain ⟨Y,hY,_,eq,_⟩ := (quotient (j X)).mp hX
      exact ji eq ▸ hY
    obtain ⟨a,_,Xa⟩ := projection.2.2 X hx
    obtain ⟨q,Y,b,qE,qX,qY,nz,Yb,hit,_⟩ := quotient_trace_l hZF h.localFamily h.localOrder h.target.order h.localEmpty
      basis basisGraph h.small h.family h.order h.source.toBoolean_d interval hom.function projection
      (fun X a xa => (adjoint X a).mp xa) small Xa ((criterion X a Xa).mp hX).2 dense
    exact ⟨q,Y,qE,qX,qY,(criterion Y b Yb).mpr ⟨nz,hit⟩⟩
  obtain ⟨ν,relation,_,_⟩ := zf_check_l M hZF (small.proper c hc).1 V
  -- 主核约化的真实区间给出共同条件序所需的全部数据。
  have family a : M.mem a A ↔ Ropen_d Q T w a ∧ M.MemberSubset a u := by
    apply (carrier a).trans
    constructor
    · rintro ⟨ha,au⟩
      exact ⟨(h.family a).mp ha,((h.order a u).mp au).2.2⟩
    · rintro ⟨ha,au⟩
      exact ⟨(h.family a).mpr ha,(h.order a u).mpr ⟨(h.family a).mpr ha,neg.1,au⟩⟩
  have orderA a b (ha : M.mem a A) (hb : M.mem b A) : Entry_d M a b S ↔ M.MemberSubset a b :=
    (h.order a b).trans ⟨fun ab => ab.2.2,fun ab => ⟨sub a ha,sub b hb,ab⟩⟩
  obtain ⟨N,principal,principalGraph⟩ := rpr_graph_l hZF h.small ((h.family u).mp neg.1) family
  have coupling : Qc_d hZF Q T w u A S e L V d J P N :=
    ⟨h.small,(h.family u).mp neg.1,family,orderA,h.empty,algebra.toBoolean_d,h.target.toBoolean_d,
      hom.toBh_d,projection,(fun X a xa => (adjoint X a).mp xa),principal,principalGraph⟩
  -- 二步呈现同时局部化到检查名字的基点和被接受的忠实区间。
  obtain ⟨r,hr,ru⟩ := hitU
  have hitU : ∃ q, H q ∧ M.mem q u := ⟨r,hr,ru⟩
  obtain ⟨c₀,hc₀,c₀c,c₀r⟩ := small.directed c r hc hr
  have hc₀' := small.proper c₀ hc₀
  have c₀u := ((h.family u).mp neg.1).2.1 r c₀ (small.proper r hr).1 ⟨hc₀'.1,hc₀'.2,c₀r⟩ ru
  have excluded x (hx : (extension_l M hZF Q T w H).mem x D) : x ≠ j d := by
    obtain ⟨X,_,nz,rfl,_⟩ := (quotient x).mp hx
    exact fun eq => nz (ji eq)
  obtain ⟨b',W,C',S',J',hb',bound,step,OC,edges,OJ,genericJ,compose,recover,f,fval,fmem,fi,fs⟩ :=
    quotient_iteration_l hZF h.small small hc₀ order quotientGeneric excluded value (checks V ν relation)
  have b'u := ((h.family u).mp neg.1).2.1 c₀ b' hc₀'.1 bound c₀u
  have b'c := h.small.trans b' c₀ c bound.1 hc₀'.1 (small.proper c hc).1 bound.2.2 c₀c
  have first := ropen_extension_l hZF h.big h.cone h.localFamily h.localOrder h.target.toBoolean_d
    h.localEmpty generic ⟨p,hp,h.point⟩
  have second := coupling.identification_l hZF small targetGeneric correspondence hb' b'u (small.proper c hc).1 b'c
    name relation j ji checks step OC compose
  refine ⟨H,small,original,A,J,sub,⟨u,hu,hitU⟩,cut,algebra,hom,inj,P,projection,adjoint,
    c,hc,j,ji,full,checks,D,quotient,order,criterion,quotientGeneric,Γ,basis,basisGraph,trace,ξ,ν,name,value,checks V ν relation,
    b',W,C',S',J',hb',step,OC,edges,OJ,genericJ,compose,recover,f,fval,fmem,fi,fs,?_⟩
  exact (first.trans_l second).trans_l ⟨f,fmem,fi,fs,
    curry_ground_l h.small hZF small step OJ genericJ compose f fval fi hc j checks⟩

end YesMetaZFC.Model.Forcing.Internal
