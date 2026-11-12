import YesMetaZFC.Model.Forcing.Collapse.ProductCoordinates
import YesMetaZFC.Model.Forcing.Boolean.DensePush
import YesMetaZFC.Model.Forcing.Ground.ProductProjection
import YesMetaZFC.Model.SetTheory.Reflection.ReflectedSeed

/-! # 全乘积任务的实际滤子列及逐坐标进度

H 是背景中保存各坐标滤子的有限序列。已完成部分逐坐标接受同一任务条件；
追加包含下一坐标条件的实际滤子后，进度严格前进一步，全部旧条目保持。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Fp_ready_d (n H d : M.Domain) : Prop := ∀ i p, M.mem i n → M.PairMember I i p d →
  ∃ K, M.PairMember I i K H ∧ M.mem p K

def fp_ready_m {k} (n H d : Term k) : Formula 1 k := set[k] ⟪
  ∀ i ∈ ⌜n⌝ₛ, ∀ p, ⌜Formula.orderedPairMem 𝒞⌝ₚ(i,p,⌜d⌝ₛ) →
    ∃ K, ⌜Formula.orderedPairMem 𝒞⌝ₚ(i,K,⌜H⌝ₛ) ∧ p ∈ K⟫
derive_free_closed fp_ready_m

theorem fp_ready_sat_l {k} (ρ : Env M k) (n H d : Term k) :
    Formula.satisfies ρ (fp_ready_m (𝒞 := 𝒞) n H d) ↔
      Fp_ready_d I (n.eval ρ) (H.eval ρ) (d.eval ρ) := by
  simp only [fp_ready_m,Fp_ready_d,Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff,Formula.satisfies_orderedPairMem_iff I,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
  exact ⟨fun h i p hi => h i hi p,fun h i hi p => h i p hi⟩

/-- 实际追加的滤子列接受新坐标块，当且仅当旧块已接受且末条件属于新滤子。 -/
theorem fp_ready_snoc_l (hE : Extensional M) {n m F F' q t p K : M.Domain}
    (succ : M.SuccessorOf m n) (ft : M.IsSetFunction I t) (cut : M.IsRestrictionOf I q t n)
    (last : M.PairMember I n p t) (ff : M.IsSetFunction I F')
    (keep : M.IsRestrictionOf I F F' n) (new : M.PairMember I n K F') :
    Fp_ready_d I m F' t ↔ Fp_ready_d I n F q ∧ M.mem p K := by
  constructor
  · intro ready
    refine ⟨?_,?_⟩
    · intro i s hi is
      obtain ⟨J,iJ,sJ⟩ := ready i s ((succ i).mpr (Or.inl hi)) ((cut.2 i s).mp is).2
      exact ⟨J,(keep.2 i J).mpr ⟨hi,iJ⟩,sJ⟩
    · obtain ⟨J,nJ,pJ⟩ := ready n p succ.predecessor_mem last
      exact ff.2 n J K nJ new ▸ pJ
  · rintro ⟨ready,pK⟩ i s hi is
    rcases (succ i).mp hi with hi | eq
    · obtain ⟨J,iJ,sJ⟩ := ready i s hi ((cut.2 i s).mpr ⟨hi,is⟩)
      exact ⟨J,((keep.2 i J).mp iJ).2,sJ⟩
    · have eq := hE.eq_of_same_members i n eq
      subst i
      exact ⟨K,new,ft.2 n p s last is ▸ pK⟩

/-- 任务的下一坐标由实际滤子完成，整个新前缀序列也在背景中构造。 -/
theorem fp_ready_append_l (hZF : M.Models ZF) {ω n H d p K : M.Domain} (hw : M.IsOmega ω)
    (hn : M.mem n ω) (seq : M.IsSequenceOfLength I H n) (fd : M.IsSetFunction I d)
    (ready : Fp_ready_d I n H d) (next : M.PairMember I n p d) (accepted : M.mem p K) :
    ∃ m H', M.SuccessorOf m n ∧ M.mem m ω ∧ M.IsSequenceOfLength I H' m ∧
      M.IsRestrictionOf I H H' n ∧ M.PairMember I n K H' ∧ Fp_ready_d I m H' d := by
  obtain ⟨V,range⟩ := ZF.exists_range_of_setFunction hZF I seq.2.1 seq.2.2
  obtain ⟨W,insert⟩ := KP.exists_insert (ZF.modelsKP hZF) V K
  have fn : M.IsSetFunctionFromTo I H n W := ⟨seq.2.1,seq.2.2,fun i hi => by
    obtain ⟨v,iv⟩ := (seq.2.2 i).mp hi
    exact ⟨v,(insert v).mpr (Or.inl ((range v).mpr ⟨i,iv⟩)),iv⟩⟩
  obtain ⟨m,H',hm,fn',m',n',last⟩ := ZF.fseq_end_exists_l I hZF hw hn fn ((insert K).mpr (Or.inr rfl))
  have en := last.prefix_sequence.2.2.2.eq hZF.1 seq.2.2
  subst n'
  have em := last.source.2.2.2.eq hZF.1 fn'.2.1
  subst m'
  refine ⟨m,H',last.length_successor,hm,last.source.2,last.prefix_restriction,last.last_value,?_⟩
  intro i q hi iq
  rcases (last.length_successor i).mp hi with hi | eq
  · obtain ⟨J,iJ,qJ⟩ := ready i q hi iq
    exact ⟨J,((last.prefix_restriction.2 i J).mp iJ).2,qJ⟩
  · have eq := hZF.1.eq_of_same_members i n eq
    subst i
    exact ⟨K,last.last_value,fd.2 n p q next iq ▸ accepted⟩

/-- 已兑现整块时，所选全乘积稠密条件进入该同一实际滤子。 -/
theorem fp_ready_filter_l (hZF : M.Models ZF) (n H P : M.Domain) :
    ∃ K, ∀ d, M.mem d K ↔ M.mem d P ∧ Fp_ready_d I n H d := by
  let ρ : Env M 2 := ⟨fun i => [n,H].get i,fun _ => H⟩
  let φ : UnarySchema 2 := { body := fp_ready_m (𝒞 := 𝒞) (.bound 1) (.bound 2) .newest }
  obtain ⟨K,members⟩ := ZF.separation_exists_d hZF φ ρ P
  exact ⟨K,fun d => (members d).trans (and_congr_right fun _ => fp_ready_sat_l I ..)⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 全乘积任务调度的实际空前缀

任意给定字母表列自动构造全乘积、零长度前缀偏序及其唯一泛型。
滤子坐标列是同一空集，接受谓词显式限制在前缀条件域中。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem fp_start_l {ω A U : M.Domain} (hw : M.IsOmega ω) (fa : M.IsSetFunctionFromTo I A ω U) :
    ∃ P R o C S, Fp_product_d hZF ω A P R ∧ (∀ x, ¬ M.mem x o) ∧ M.mem o ω ∧
      M.IsSequenceOfLength I o o ∧ Fp_prefix_d hZF ω A o C S ∧
      Generic_d M C S C (fun q => M.mem q C ∧ Fp_ready_d I o o q) := by
  obtain ⟨P,R,product⟩ := fp_product_l hZF hw fa
  obtain ⟨o,empty,ho⟩ := hw.1.1
  have seq := Structure.IsSequenceOfLength.empty I empty
  have start : Fp_at_d I ω A o o := ⟨seq.2.1,seq.2.2,fun i s ⟨v,_,hv⟩ => (empty v hv).elim⟩
  obtain ⟨C,S,stage⟩ := product.prefix_l hZF ho
  have order := stage.order_l hZF
  have same q (hq : M.mem q C) : q = o := by
    have fq := (stage.conditions q).mp hq
    apply hZF.1.eq_of_same_members q o
    intro v
    refine iff_of_false (fun hv => ?_) (empty v)
    obtain ⟨i,s,c⟩ := fq.function.1 v hv
    exact empty i ((fq.domain i).mpr ⟨s,⟨v,c,hv⟩⟩)
  have ready q : Fp_ready_d I o o q := fun i _ hi _ => (empty i hi).elim
  have proper q (hq : M.mem q C) : q ≠ C := fun eq =>
    KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ hq)
  refine ⟨P,R,o,C,S,product,empty,ho,seq,stage,?_⟩
  refine ⟨fun q hq => ⟨hq.1,proper q hq.1⟩,⟨o,(stage.conditions o).mpr start,ready o⟩,
    fun _ q _ hq _ => ⟨hq,ready q⟩,?_,?_⟩
  · intro p q hp hq
    have eq := (same p hp.1).trans (same q hq.1).symm
    exact ⟨p,hp,order.refl p hp.1,eq ▸ order.refl p hp.1⟩
  · intro p hp D dense
    obtain ⟨q,hq,qD⟩ := dense p ⟨hp.1,proper p hp.1,order.refl p hp.1⟩
    exact ⟨q,⟨hq.1,ready q⟩,qD⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 空前缀与零字母表坍缩的实际比较

两个条件域都只有空函数。实际单点图给出稠密比较，全部小条件本身即为泛型滤子。
此处只用 ZF；不把非零前缀的不可数基数要求带入初态。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Fp_prefix_d.zero_comparison_l {ω A o C S Q T : M.Domain} (stage : Fp_prefix_d hZF ω A o C S)
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x o)
    (space : Fseq_space_d I ω o Q) (L : Cond_order_d M Q T Q)
    {H : M.Domain → Prop} (generic : Generic_d M C S C H) :
    ∃ Γ, H o ∧ Dmap_at_d Q T Q C S C Γ o ∧
      (∀ p, Pull_generic_d M Γ H p ↔ M.mem p Q) ∧
      Generic_d M Q T Q (fun p => M.mem p Q) ∧
      Miso_over_d (extension_l M hZF Q T Q (fun p => M.mem p Q)) (extension_l M hZF C S C H)
        (Gval_d M Q T Q (fun p => M.mem p Q)) (Gval_d M C S C H) := by
  obtain ⟨o₀,empty₀,ho₀⟩ := hw.1.1
  have ho : M.mem o ω := (hZF.1.eq_of_same_members o₀ o (fun x => iff_of_false (empty₀ x) (empty x))) ▸ ho₀
  have seq := Structure.IsSequenceOfLength.empty I empty
  have hoQ : M.mem o Q := (space o).mpr ⟨o,ho,seq.2.1,seq.2.2,fun i hi => (empty i hi).elim⟩
  have hoC : M.mem o C := (stage.conditions o).mpr
    ⟨seq.2.1,seq.2.2,fun i s ⟨v,_,hv⟩ => (empty v hv).elim⟩
  have small p (hp : M.mem p Q) : p = o := by
    obtain ⟨n,_,fn⟩ := (space p).mp hp
    apply hZF.1.eq_of_same_members p o
    intro v
    refine iff_of_false (fun hv => ?_) (empty v)
    obtain ⟨i,x,pair⟩ := fn.1.1 v hv
    exact empty x (fn.output_mem_of_pairMember ⟨v,pair,hv⟩)
  have block p (hp : M.mem p C) : p = o := by
    have fp := (stage.conditions p).mp hp
    apply hZF.1.eq_of_same_members p o
    intro v
    refine iff_of_false (fun hv => ?_) (empty v)
    obtain ⟨i,s,pair⟩ := fp.function.1 v hv
    exact empty i ((fp.domain i).mpr ⟨s,⟨v,pair,hv⟩⟩)
  have nzQ : o ≠ Q := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) Q (eq ▸ hoQ)
  have nzC : o ≠ C := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ hoC)
  have O := stage.order_l hZF
  obtain ⟨v,pair⟩ := (I).total o o
  obtain ⟨Γ,single⟩ := KP.exists_singleton (ZF.modelsKP hZF) v
  have entries p q : Entry_d M p q Γ ↔ p = o ∧ q = o := by
    constructor
    · rintro ⟨w,pq,hw⟩
      exact (I).injective ((single w).mp hw ▸ pq) pair
    · rintro ⟨rfl,rfl⟩
      exact ⟨v,pair,(single v).mpr rfl⟩
  have oo := (entries o o).mpr ⟨rfl,rfl⟩
  have map : Dmap_d Q T Q C S C Γ := by
    refine ⟨fun p hp _ => ⟨o,(entries p o).mpr ⟨small p hp,rfl⟩⟩,?_,?_,?_,?_,?_⟩
    · intro p q pq
      obtain ⟨ep,eq⟩ := (entries p q).mp pq
      subst p q
      exact ⟨⟨hoQ,nzQ⟩,hoC,nzC⟩
    · intro p x y px py
      exact ((entries p x).mp px).2.trans ((entries p y).mp py).2.symm
    · intro p q x y px qy _
      obtain ⟨ep,ex⟩ := (entries p x).mp px
      obtain ⟨eq,ey⟩ := (entries q y).mp qy
      subst p x q y
      exact O.refl o hoC
    · intro p q x y px qy _
      obtain ⟨ep,ex⟩ := (entries p x).mp px
      obtain ⟨eq,ey⟩ := (entries q y).mp qy
      subst p x q y
      exact ⟨o,below_refl_l L hoQ nzQ,L.refl o hoQ⟩
    · intro q hq _
      exact ⟨o,o,oo,(block q hq).symm ▸ O.refl o hoC⟩
  obtain ⟨q,hq⟩ := generic.inhabited
  have accepted : H o := block q (generic.proper q hq).1 ▸ hq
  have localMap : Dmap_at_d Q T Q C S C Γ o := ⟨map.regular_l O,map.functional,
    fun p q pq => ((entries p q).mp pq).2.symm ▸ below_refl_l O hoC nzC,
    fun q hq => map.dense q hq.1 hq.2.1⟩
  have read p : Pull_generic_d M Γ H p ↔ M.mem p Q :=
    ⟨fun ⟨q,pq,_⟩ => ((entries p q).mp pq).1.symm ▸ hoQ,
      fun hp => ⟨o,(entries p o).mpr ⟨small p hp,rfl⟩,accepted⟩⟩
  have same : Pull_generic_d M Γ H = (fun p => M.mem p Q) := funext fun p => propext (read p)
  have pulled := reg_generic_l L O hZF localMap.toReg_map_d generic ⟨o,o,oo,accepted⟩
  exact ⟨Γ,accepted,localMap,read,same ▸ pulled,same ▸ map.ground_l hZF L O generic⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原滤子列的接受关系与有界投影反射

条件图的坐标固定即可；滤子列及其中的各个滤子允许移动。
函数值的原像由真实初等图恢复；有界投影在秩层构造后沿同一图回收，
不要求源壳满足收集或分离模式。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.InnerModel SetTheory.Internal SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem fp_ready_fixed_l {ω c d X R Y S π n F G q : M.Domain}
    (hw : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (map : Smap_d I ω c d X Y π)
    (fg : Rd_entry_d F G π) (fn : M.IsSetFunction I G)
    (fixed : ∀ i p, M.mem i n → Rd_entry_d i p q → Rd_entry_d i i π ∧ Rd_entry_d p p π) :
    Fp_ready_d I n F q ↔ Fp_ready_d I n G q := by
  constructor
  · intro ready i p hi ip
    obtain ⟨K,ik,hp⟩ := ready i p hi ip
    have hk := (ik.choose_spec.1.mem_l M xt
      (xt F (map.1.1.input_mem_of_pairMember fg) _ ik.choose_spec.2)).2
    obtain ⟨L,_,kl⟩ := map.1.1.2.2 K hk
    exact ⟨L,(map.entry_l hZF hw xt yt mx my (fixed i p hi ip).1 kl fg).mp ik,
      (map.member_l I hZF hw mx my (fixed i p hi ip).2 kl).mp hp⟩
  · intro ready i p hi ip
    obtain ⟨L,il,hp⟩ := ready i p hi ip
    obtain ⟨K,ik,kl⟩ := map.value_preimage_l hZF hw xt yt mx my (fixed i p hi ip).1 fg fn il
    exact ⟨K,ik,(map.member_l I hZF hw mx my (fixed i p hi ip).2 kl).mpr hp⟩

end YesMetaZFC.Model.Forcing.Internal

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 任意壳内三参数的投影集合仍在壳内；其像是秩层中条件域的实际子集。 -/
theorem Rf_hull_d.filter_project_l {ω T α V d S P c R π : M.Domain} {Φ : List Lr_formula}
    {n} {v : Fin n → M.Domain} (h : Rf_hull_d hZF ω T Φ v α V d S P c R π)
    (hw : M.IsOmega ω) (C U H : M.Domain) (hC : M.mem C P) (hU : M.mem U P) (hH : M.mem H P) :
    ∃ K, M.mem K P ∧ Fp_filter_project_d C U H K := by
  obtain ⟨C',hc,cc⟩ := h.map.1.1.2.2 C hC
  obtain ⟨U',_,uu⟩ := h.map.1.1.2.2 U hU
  obtain ⟨H',_,hh⟩ := h.map.1.1.2.2 H hH
  obtain ⟨K,project⟩ := fp_filter_project_l (ZF.modelsKP hZF) C' U' H'
  have hk := v_subset_mem_l I h.rank hc (fun q hq => ((project q).mp hq).1)
  have tr := h.map.exists_delta_l hZF hw h.transitive (v_transitive_l I h.rank) h.model h.target (n := 3)
    (fp_filter_project_m (.bound 1) (.bound 2) (.bound 3) .newest)
    (by simp -implicitDefEqProofs) (fp_filter_project_delta_l ..)
    ⟨Fin.cases C (Fin.cases U (fun _ => H)),fun _ => C⟩
    ⟨Fin.cases C' (Fin.cases U' (fun _ => H')),fun _ => C'⟩
    (Fin.cases cc (Fin.cases uu (fun _ => hh)))
  simp only [fp_filter_project_sat_l hZF.1] at tr
  exact tr.mpr ⟨K,hk,project⟩

end YesMetaZFC.SetTheory.Internal
