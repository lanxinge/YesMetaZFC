import YesMetaZFC.Model.Forcing.Boolean.NameMap
import YesMetaZFC.SetTheory.Boolean.ProjectionKernel

/-! # 实际条件下的名字真值局部化与核处理

条件 p 的主正则开集 U 自动构造。相交到 U 的完全同态具有核上确界 ¬U，
通用核定理实际给出其忠实限制；名字图沿该同态复合后，在包含 p 的每个
原泛型中保留原来的成员读取。未在这里预设名字图本身是完全同态。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
include hZF

theorem ropen_condition_l {B R z p : M.Domain} (O : Cond_order_d M B R z) (hp : M.mem p B) (hz : p ≠ z) :
    ∃ U, Ropen_d B R z U ∧ M.mem p U ∧
      ∀ V, Ropen_d B R z V → M.mem p V → M.MemberSubset U V := by
  let ρ : Env M 4 := ⟨fun i => [B,R,z,p].get i,fun _ => B⟩
  let φ : UnarySchema 4 := { body := below_m (.bound 1) (.bound 2) (.bound 3) .newest (.bound 4) }
  obtain ⟨D,members⟩ := ZF.separation_exists_d hZF φ ρ B
  have read q : M.mem q D ↔ Below_d M B R z q p :=
    ((members q).trans (and_congr_right fun _ => below_sat_l M hZF.1 ..)).trans
      ⟨And.right,fun h => ⟨h.1,h⟩⟩
  have lower : Lower_d M B R z (fun q => M.mem q D) :=
    fun r q _ hq hr => (read q).mpr (below_trans_l O hp hq ((read r).mp hr))
  obtain ⟨U,regular,values⟩ := ropen_closure_l hZF O D
  refine ⟨U,regular,(values p).mpr ⟨hp,hz,dense_intro_l O lower hp ((read p).mpr (below_refl_l O hp hz))⟩,?_⟩
  intro V valid hV q hq
  obtain ⟨hq,hz,dense⟩ := (values q).mp hq
  apply valid.2.2 q hq hz
  intro r hr
  obtain ⟨s,hs,hD⟩ := dense r hr
  exact ⟨s,hs,valid.2.1 p s hp ((read s).mp hD) hV⟩

theorem bv_local_kernel_l {B R z p : M.Domain} (O : Cond_order_d M B R z)
    (hp : M.mem p B) (hz : p ≠ z) (b τ Q : M.Domain) :
    ∃ K S e U A P N k J F,
      (∀ V, M.mem V K ↔ Ropen_d B R z V) ∧ (∀ r, ¬ M.mem r e) ∧
      (∀ V W, Entry_d M V W S ↔ M.mem V K ∧ M.mem W K ∧ M.MemberSubset V W) ∧
      BooleanZF.Cba_d I K S e ∧ M.mem p U ∧
      (∀ V, Ropen_d B R z V → M.mem p V → M.MemberSubset U V) ∧
      BooleanZF.Bi_d I K S U A ∧ BooleanZF.Cba_d I A S e ∧ BooleanZF.Cbh_d I K S e A S e P ∧
      (∀ V, M.mem V N ↔ M.mem V K ∧ Entry_d M V e P) ∧ BooleanZF.Bsup_d I K S N k ∧
      BooleanZF.Imp_d I K S U e k ∧
      (∀ V, M.mem V K → (Entry_d M V e P ↔ Entry_d M V k S)) ∧
      M.IsRestrictionOf I J P A ∧ BooleanZF.Cbh_d I A S e A S e J ∧ M.IsSetBijectionFromTo I J A A ∧
      M.IsSetFunctionFromTo I F Q A ∧
      (∀ q V, Entry_d M q V F ↔ M.mem q Q ∧ ∃ W, Bv_mem_d B R z b τ q W ∧ BooleanZF.Meet_d I K S W U V) ∧
      ∀ G, Generic_d M B R z G → G b → G p → ∀ H : (extension_l M hZF B R z G).Domain,
        Qval_d M B R z G τ H → ∃ j : M.Domain → (extension_l M hZF B R z G).Domain,
          Function.Injective j ∧ (∀ a y, (extension_l M hZF B R z G).mem y (j a) ↔ ∃ c, M.mem c a ∧ j c = y) ∧
          (∀ a t, Check_d M b a t → Qval_d M B R z G t (j a)) ∧
          ∀ q V, Entry_d M q V F → ((∃ r, G r ∧ M.mem r V) ↔ (extension_l M hZF B R z G).mem (j q) H) := by
  obtain ⟨K,S,e,F₀,family,empty,order,algebra,fn₀,values₀,read₀⟩ := bv_name_map_l hZF O b τ Q
  obtain ⟨U,regular,pU,minimal⟩ := ropen_condition_l hZF O hp hz
  have hU := (family U).mpr regular
  obtain ⟨A,P,N,k,J,interval,localAlgebra,project,projectValues,kernel,sup,complement,principal,restriction,reduced,bij⟩ :=
    algebra.project_kernel_l I hZF hU
  obtain ⟨F,fn,compose⟩ := ZF.exists_compositionFunction hZF I fn₀ project.function
  have graph q V : Entry_d M q V F ↔ M.mem q Q ∧ ∃ W,
      Bv_mem_d B R z b τ q W ∧ BooleanZF.Meet_d I K S W U V := by
    apply (compose q V).trans
    refine and_congr_right fun hq => ?_
    constructor
    · rintro ⟨W,qW,WV⟩
      exact ⟨W,((values₀ q W).mp qW).2,((projectValues W V).mp WV).2⟩
    · rintro ⟨W,value,meet⟩
      have qW := (values₀ q W).mpr ⟨hq,value⟩
      exact ⟨W,qW,(projectValues W V).mpr ⟨fn₀.output_mem_of_pairMember qW,meet⟩⟩
  refine ⟨K,S,e,U,A,P,N,k,J,F,family,empty,order,algebra,pU,minimal,interval,localAlgebra,project,
    kernel,sup,complement,principal,restriction,reduced,bij,fn,graph,?_⟩
  intro G generic hb hpG H valueH
  obtain ⟨j,inj,full,checks,reads⟩ := read₀ G generic hb H valueH
  refine ⟨j,inj,full,checks,?_⟩
  intro q V qV
  obtain ⟨_,W,qW,WV⟩ := (compose q V).mp qV
  have hW := fn₀.output_mem_of_pairMember qW
  have meet := ropen_meet_values_l hZF family order algebra.toBoolean_d hW hU ((projectValues W V).mp WV).2
  apply Iff.trans ?_ (reads q W qW)
  constructor
  · rintro ⟨r,hr,hV⟩
    exact ⟨r,hr,((meet r).mp hV).1⟩
  · rintro ⟨r,hr,hrW⟩
    obtain ⟨s,hs,sr,sp⟩ := generic.directed r p hr hpG
    have proper := generic.proper s hs
    exact ⟨s,hs,(meet s).mpr ⟨((family W).mp hW).2.1 r s (generic.proper r hr).1 ⟨proper.1,proper.2,sr⟩ hrW,
      regular.2.1 p s hp ⟨proper.1,proper.2,sp⟩ pU⟩⟩

end YesMetaZFC.Model.Forcing.Internal
