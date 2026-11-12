import YesMetaZFC.Model.Forcing.Boolean.GenericName
import YesMetaZFC.Model.Forcing.Boolean.HitValue
import YesMetaZFC.Model.Forcing.Boolean.RegularValues
import YesMetaZFC.Model.Forcing.Boolean.ConditionValue
import YesMetaZFC.SetTheory.Boolean.CompleteSyntax

/-! # 原泛型名字所诱导的实际完备化图

源是小条件序的内部正则开完备化，目标是大条件 p 的主区间。
每个源正则开集的值为其命中真值与 p 的主正则开集之交。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

structure Nh_d (B R z b p Q T w 𝒟 τ K S e C L V d F : M.Domain) : Prop where
  big : Cond_order_d M B R z
  small : Cond_order_d M Q T w
  base : M.mem b B
  positive : M.mem p B ∧ p ≠ z
  below : Entry_d M p b R
  power : M.IsPowerSetOf 𝒟 Q
  name : Gn_d B R z b Q T w 𝒟 τ p
  family : ∀ U, M.mem U K ↔ Ropen_d Q T w U
  empty : ∀ q, ¬ M.mem q e
  order : ∀ U W, Entry_d M U W S ↔ M.mem U K ∧ M.mem W K ∧ M.MemberSubset U W
  source : BooleanZF.Cba_d I K S e
  cone : Ropen_d B R z C
  point : M.mem p C
  minimal : ∀ U, Ropen_d B R z U → M.mem p U → M.MemberSubset C U
  localFamily : ∀ X, M.mem X L ↔ Ropen_d B R z X ∧ M.MemberSubset X C
  localEmpty : ∀ q, ¬ M.mem q d
  localOrder : ∀ X Y, M.mem X L → M.mem Y L → (Entry_d M X Y V ↔ M.MemberSubset X Y)
  target : BooleanZF.Cba_d I L V d
  function : M.IsSetFunctionFromTo I F K L
  graph : ∀ U X, Entry_d M U X F → ∃ W, Bv_hit_d B R z b τ U W ∧
    ∀ q, M.mem q X ↔ M.mem q W ∧ M.mem q C

theorem nh_exists_l {B R z b p Q T w 𝒟 τ : M.Domain} (O : Cond_order_d M B R z)
    (small : Cond_order_d M Q T w) (hb : M.mem b B) (hp : M.mem p B) (hz : p ≠ z)
    (pb : Entry_d M p b R) (power : M.IsPowerSetOf 𝒟 Q) (name : Gn_d B R z b Q T w 𝒟 τ p) :
    ∃ K S e C L V d F, Nh_d hZF B R z b p Q T w 𝒟 τ K S e C L V d F := by
  obtain ⟨K,S,e,family,empty,order,source⟩ := ropen_completion_l hZF small
  obtain ⟨J,V,d,largeFamily,largeEmpty,largeOrder,large⟩ := ropen_completion_l hZF O
  obtain ⟨C,cone,point,minimal⟩ := ropen_condition_l hZF O hp hz
  obtain ⟨L,interval⟩ := BooleanZF.bi_exists_l I hZF J V C ((largeFamily C).mpr cone)
  have target := interval.complete_l I large
  obtain ⟨P,projection,project⟩ := interval.project_l I hZF large.toBoolean_d
  obtain ⟨_,F₀,_,fn₀,graph₀⟩ := bv_hit_graph_l hZF B R z b τ K
  have fn₀ : M.IsSetFunctionFromTo I F₀ K J := ⟨fn₀.1,fn₀.2.1,fun U hU => by
    obtain ⟨W,_,uw⟩ := fn₀.2.2 U hU
    exact ⟨W,(largeFamily W).mpr (((graph₀ U W).mp uw).2.regular_l hZF O hb name.1),uw⟩⟩
  obtain ⟨F,fn,compose⟩ := ZF.exists_compositionFunction hZF I fn₀ projection.function
  have localFamily X : M.mem X L ↔ Ropen_d B R z X ∧ M.MemberSubset X C := by
    apply (interval.carrier X).trans
    exact ⟨fun h => ⟨(largeFamily X).mp h.1,((largeOrder X C).mp h.2).2.2⟩,
      fun h => ⟨(largeFamily X).mpr h.1,(largeOrder X C).mpr ⟨(largeFamily X).mpr h.1,interval.bound,h.2⟩⟩⟩
  refine ⟨K,S,e,C,L,V,d,F,⟨O,small,hb,⟨hp,hz⟩,pb,power,name,family,empty,order,source,cone,point,minimal,
    localFamily,largeEmpty,?_,target,fn,?_⟩⟩
  · intro X Y hx hy
    exact (largeOrder X Y).trans (and_iff_right ((interval.carrier X).mp hx).1 |>.trans
      (and_iff_right ((interval.carrier Y).mp hy).1))
  · intro U X ux
    obtain ⟨_,W,uw,wx⟩ := (compose U X).mp ux
    exact ⟨W,((graph₀ U W).mp uw).2,ropen_meet_values_l hZF largeFamily largeOrder large.toBoolean_d
      (fn₀.output_mem_of_pairMember uw) interval.bound ((project W X).mp wx).2⟩

end YesMetaZFC.Model.Forcing.Internal
