import YesMetaZFC.SetTheory.LargeCardinal.Absorption.TestRun
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinInitial
import YesMetaZFC.Model.SetTheory.Reflection.ReflectedSeed
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Realization
import YesMetaZFC.Model.SetTheory.Reflection.ReflectedRankReals
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed

/-! # 原反例与原可数源进入同一个完整吸收运行

第二个 hull 同时包含原有限历史和十八项反例证书。其原像保持指定实数、
真实 Jensen 呈示及有界非决定性；完整运行仍从原源和原 G 的前缀接续。
端点返回图的反坍塌像明确等于原返回图，供后续复合真实返回因子。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}
section
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 所有见证均为同一测试壳、反坍塌图和实际吸收列中的对象。 -/
def Ab_counter_run_d (Ω c X R cY Y S j A Q U G : M.Domain) (x : Fin 18 → M.Domain) : Prop :=
  ∃ m L Z T α V d W P b R₀ π,
  ∃ test : Rf_hull_d hZF Ω T (ab_test_queries_l lr_ad_m lr_ad_closed_l)
      (Fin.addCases (fun k : Fin 5 => [cY,Y,S,L,Z].get k) x) α V d W P b R₀ π,
    M.mem Ω P ∧ M.mem X P ∧ M.MemberSubset X P ∧
    Rd_entry_d X X π ∧ Rd_entry_d G G π ∧ (∀ a, M.mem a X → Rd_entry_d a a π) ∧
    ∃ y : Fin 18 → M.Domain, (∀ k, Rd_entry_d (y k) (x k) π) ∧
      y 0 = Ω ∧ y 4 = x 4 ∧ Rb_reals_d P Ω (y 2) ∧ Tc_d (y 2) (y 1) ∧
      Fseq_space_d I Ω Ω (y 3) ∧ Jp_counter_d lr_payoff_m y ∧ Gs_number_d I Ω (y 3) (y 7) ∧
      Jp_d I lr_payoff_m (y 1) (y 2) (y 4) (y 5) (y 6) ∧
      ¬ Gs_det_d Ω (y 2) (y 3) (y 7) (y 8) (y 6) ∧
    ∃ C Y₀ S₀ : (smdl_structure_l I (R := R₀) test.model.1.2.1).Domain,
      Rd_entry_d C.val cY π ∧ Rd_entry_d Y₀.val Y π ∧ Rd_entry_d S₀.val S π ∧
      ∃ F, Ab_run_d I P Ω C.val Y₀.val S₀.val F ∧
      ∃ i r, (∀ a, ¬ M.mem a i) ∧ M.mem i Ω ∧ M.SuccessorOf m i ∧ Rd_entry_d i r F ∧
      ∃ v : Fin 26 → M.Domain, Rt_tuple_d v r ∧
        v 7 = m ∧ v 0 = c ∧ v 1 = X ∧ v 2 = R ∧ v 4 = A ∧ v 5 = Q ∧ v 6 = U ∧
        Rd_entry_d (v 3) j π ∧ Fp_filter_project_d (v 8) U G (v 11)

end

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_counterexample_run_l
    {Ω c X R cY Y S θ j G : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d I Ω c X R) (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X Ω) (target : Smem_d I cY Y S) (rank : V_d I θ Y)
    (embed : Smap_d I Ω c cY X Y j)
    {ω A Q U : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) ω A)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω A Q U)
    (generic : Gset_d Q.val U.val Q.val X G)
    {x : Fin 18 → M.Domain} (ew : x 0 = Ω) (space : Baire_d I Ω (x 2)) (bad : Jp_counter_d lr_payoff_m x)
    (number : Gs_number_d I Ω (x 3) (x 7)) :
    Ab_counter_run_d hZF Ω c X R cY Y S j A.val Q.val U.val G x := by
  classical
  obtain ⟨i,empty,hi⟩ := hΩ.1.1
  obtain ⟨m,L,Z,_,T,α,V,d,W,P,b,R₀,π,test,succ,_,_,hωP,hXP,subX,_,fixedX,fixedG,points,_,
    C,Y₀,S₀,_,_,cc,yy,ss,_,_,_,_,_,F,_,_,run,_,r,_,ir,v,vr,em,ec,eX,eR,eA,eQ,eU,image,projection⟩ :=
    ab_test_run_l hZFC hΩ certificate source xt count target rank embed hw sequence product generic hi
      lr_ad_m lr_ad_closed_l Fin.elim0 (fun k => Fin.elim0 k) x
  have parameters (k : Fin 18) : ∃ a, Rd_entry_d a (x k) π := by
    simpa only [Fin.addCases_right] using test.params (Fin.natAdd 5 k)
  obtain ⟨y,images⟩ := Classical.axiomOfChoice parameters
  obtain ⟨eqω,eqa,reals,seed,finite,data,present,no⟩ :=
    test.counterexample_l hZF hΩ hωP lr_payoff_closed_l ew images space bad
  have number' := test.game_number_l hZF hΩ hωP finite (images 3) (images 7) number
  exact ⟨m,L,Z,T,α,V,d,W,P,b,R₀,π,test,hωP,hXP,subX,fixedX,fixedG,points,
    y,images,eqω,eqa,reals,seed,finite,data,number',present,no,C,Y₀,S₀,cc,yy,ss,F,run,
    i,r,empty,hi,succ,ir,v,vr,em,ec,eX,eR,eA,eQ,eU,image,projection⟩

/-- 从原真类 Woodin 前提和 lr_ad 否定构造两层 hull 及完整反例吸收列。
备用 Woodin、序列共同界和真实第一坐标像仍留在同一个初始源中。 -/
theorem wd_counterexample_run_l
    (proper : Wd_proper_d I)
    (bad : ¬ M.SatisfiesSentence Axioms.lr_ad) :
    ∃ x : Fin 18 → M.Domain, ∃ seed : Lr_seed_d hZF (x 0) (x 2) (x 1), Jp_counter_d lr_payoff_m x ∧
      ∃ θ Y d S, Smem_d I d Y S ∧ V_d I θ Y ∧ Zc_model_d I (x 0) d Y S ∧
      ∃ c X R π, ∃ source : Smem_d I c X R, ∃ certificate : Zc_model_d I (x 0) c X R,
        M.TransitiveSet X ∧ M.CardinalLessOrEqual I X (x 0) ∧ Smap_d I (x 0) c d X Y π ∧
      let N := smdl_structure_l I (R := R) source.1.2.1
      let native := ZFC.models_zf_l (certificate.native_l I hZF seed.1.1)
      let J := kp_pair_l (ZF.modelsKP native)
      ∃ w A μ δ Z o κ a P V σ : N.Domain, w.val = x 0 ∧ a.val = x 4 ∧ Rd_entry_d (x 4) (x 4) π ∧
        N.IsOmega w ∧ Bc_binary_d w a ∧ Wd_sequence_d J w A ∧
        N.IsSetFunctionFromTo J A w μ ∧ N.mem μ δ ∧ Woodin_d J δ ∧ V_d J δ Z ∧
        (∀ t, ¬ N.mem t o) ∧ Entry_d N o κ A ∧
      ∃ K α Vα, Rd_entry_d κ.val K π ∧ M.IsUncountableCardinal I (x 0) K ∧
        Woodin_d I α ∧ V_d I α Vα ∧ M.mem (x 0) Vα ∧ M.MemberSubset α K ∧
        Fp_product_d native w A P V ∧ Rp_name_d native w A P σ ∧
      ∃ H, Gset_d P.val V.val P.val X H ∧
        Ab_counter_run_d hZF (x 0) c X R d Y S π A.val P.val V.val H x := by
  obtain ⟨x,seed,data,number⟩ := lr_counterexample_data_l hZF bad
  obtain ⟨θ,Y,d,S,target,rank,theory,c,X,R,π,source,certificate,xt,count,embed,
    w,A,μ,δ,Z,o,κ,a,P,V,σ,ew,ea,fixed,hw,binary,sequence,fa,small,woodin,rankδ,empty,first,
    K,α,Vα,image,hK,large,rankα,inside,bound,product,name,H,generic⟩ :=
    wd_initial_l hZFC seed.1.1 proper data.binary
  have run := ab_counterexample_run_l hZFC seed.1.1 certificate source xt count target rank embed
    hw sequence product generic rfl seed.1 data number
  exact ⟨x,seed,data,θ,Y,d,S,target,rank,theory,c,X,R,π,source,certificate,xt,count,embed,
    w,A,μ,δ,Z,o,κ,a,P,V,σ,ew,ea,fixed,hw,binary,sequence,fa,small,woodin,rankδ,empty,first,
    K,α,Vα,image,hK,large,rankα,inside,bound,product,name,H,generic,run⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原吸收极限到真实返回目标的复合

测试壳的反坍塌在内部返回目标上限制为完整初等图，再与原极限返回因子
复合。固定的零轮源及原返回图的像保证新方块严格交换。极限的可数性
来自其向测试壳的实际单射，派生实数则仍为同一测试壳的全部实数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ab_run_d.returned_limit_l {Ω T₀ α V₀ d₀ S₀ P c₀ R₀ π : M.Domain}
    {Φ : List Lr_formula} {n} {z : Fin n → M.Domain}
    (test : Rf_hull_d hZF Ω T₀ Φ z α V₀ d₀ S₀ P c₀ R₀ π) (hw : M.IsOmega Ω) (hω : M.mem Ω P)
    {cY Y S : (smdl_structure_l I (R := R₀) test.model.1.2.1).Domain} {F : M.Domain}
    (run : Ab_run_d I P Ω cY.val Y.val S.val F)
    {dY W U j i r : M.Domain} (target : Smem_d I dY W U)
    (yy : Rd_entry_d Y.val W π) (ss : Rd_entry_d S.val U π)
    {v : Fin 26 → M.Domain} (empty : ∀ a, ¬ M.mem a i) (ir : Rd_entry_d i r F) (vr : Rt_tuple_d v r)
    (fixedX : Rd_entry_d (v 1) (v 1) π) (points : ∀ a, M.mem a (v 1) → Rd_entry_d a a π)
    (image : Rd_entry_d (v 3) j π) :
    ∃ B, Rb_reals_d P Ω B ∧ ∃ C D d X R J σ A Q T H,
    ∃ lim : Ab_limit_d hZF Ω cY.val Y.val F C D d X R J σ A Q T,
      Gset_d Q T Q X H ∧ (∀ x, Ab_limit_real_d hZF lim H x ↔ M.mem x B) ∧
      M.CardinalLessOrEqual I X Ω ∧
    ∃ q η, Smap_d I Ω (v 0) d (v 1) X q ∧ Smap_d I Ω d dY X W η ∧ It_comp_d q η j ∧
      Rd_entry_d (v 4) A q ∧ Rd_entry_d (v 5) Q q ∧ Rd_entry_d (v 6) T q := by
  let ω : (smdl_structure_l I (R := R₀) test.model.1.2.1).Domain := ⟨Ω,hω⟩
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,common,_⟩ :=
    run.finish_l hZF test.model test.transitive (ω := ω) hw
  obtain ⟨_,⟨w,hwY⟩,B,ew,reals,_,C,D,_,d,X,R,J,σ,A,Q,T,H,_,_,_,lim,generic,_,same,_⟩ := common
  change w = Ω at ew
  subst w
  have frame := (run.queues i r v ir vr).frame
  obtain ⟨q,iq⟩ := (lim.domain i).mp (run.function.bound_l ir).1
  obtain ⟨root,square,pq,ut⟩ := lim.rows i r v q ir vr iq
  have aa := lim.zero_alphabet i r v q empty ir vr iq
  -- 原返回目标嵌入真实目标；其限制图量化全部内部公式码。
  obtain ⟨χ,uncollapse,cut⟩ := test.restrict_l hZF hw hω run.target.1 target.1 yy ss
  obtain ⟨η,returned,compose⟩ := it_comp_elementary_l hZF lim.returns uncollapse
  have vt := v_transitive_l I test.rank
  have original := fn0_function_l (ZF.modelsKP hZF)
    ((test.map.function_l hZF hw test.transitive vt test.model test.target fixedX yy image).mp
      (fn0_of_function_l (ZF.modelsKP hZF) frame.returns.1.1))
  have initial : It_comp_d (v 3) χ j := by
    refine ⟨original.1.1,fun a b => ⟨?_,?_⟩⟩
    · intro ab
      have ha := original.input_mem_of_pairMember ab
      obtain ⟨s,hs,as⟩ := frame.returns.1.1.2.2 a ha
      obtain ⟨b',_,sb⟩ := uncollapse.1.1.2.2 s hs
      have ab' := (test.map.entry_l hZF hw test.transitive vt test.model test.target
        (points a ha) ((cut.2 s b').mp sb).2 image).mp as
      have eq := original.1.2 a b' b ab' ab
      exact ⟨s,as,eq ▸ sb⟩
    · rintro ⟨s,as,sb⟩
      exact (test.map.entry_l hZF hw test.transitive vt test.model test.target
        (points a (frame.returns.1.1.input_mem_of_pairMember as)) ((cut.2 s b).mp sb).2 image).mp as
  obtain ⟨j',_,composed⟩ := it_comp_elementary_l hZF root returned
  have eq : j' = j := (square.assoc_l compose composed).unique_l hZF.1 initial
  have commute : It_comp_d q η j := eq ▸ composed
  -- 极限先单射进内部返回目标，再单射进可数测试壳。
  have into : M.IsSetInjectionFromTo I σ X P := by
    refine ⟨⟨lim.returns.1.1.1,lim.returns.1.1.2.1,?_⟩,lim.returns.1.2⟩
    intro a ha
    obtain ⟨b,hb,ab⟩ := lim.returns.1.1.2.2 a ha
    exact ⟨b,test.transitive Y.val Y.property b hb,ab⟩
  obtain ⟨f,small⟩ := test.count
  have count := ZF.exists_compositionInjection hZF I into small
  exact ⟨B.val,reals,C,D,d,X,R,J,σ,A,Q,T,H,lim,generic,same,count,q,η,root,returned,commute,aa,pq,ut⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 反例吸收列的备用 Woodin 与真实返回极限

零轮到极限的同一嵌入运输序列共同界、备用 Woodin、其实际秩层和第一
坐标。规范名字在这个实际极限中构造；全乘积泛型和精确实数迹来自原
吸收运行。所有资料因此可供既有高度吸收定理直接调用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ab_counter_run_d.limit_l {c X R dY Y S π G K : M.Domain} (source : Smem_d I c X R)
    {ω A Q U δ Z μ a o κ : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (hw : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R) (target : Smem_d I dY Y S)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) δ Z)
    (small : (smdl_structure_l I (R := R) source.1.2.1).mem μ δ)
    (fa : (smdl_structure_l I (R := R) source.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) A ω μ)
    (binary : Bc_binary_d ω a) (empty : ∀ t, ¬ (smdl_structure_l I (R := R) source.1.2.1).mem t o)
    (first : Entry_d (smdl_structure_l I (R := R) source.1.2.1) o κ A) (image : Rd_entry_d κ.val K π)
    {x : Fin 18 → M.Domain} (param : a.val = x 4)
    (h : Ab_counter_run_d hZF ω.val c X R dY Y S π A.val Q.val U.val G x) :
    ∃ T₀ α V₀ d₀ W₀ P b R₀ π₀, ∃ z : Fin 23 → M.Domain,
    Rf_hull_d hZF ω.val T₀ (ab_test_queries_l lr_ad_m lr_ad_closed_l) z α V₀ d₀ W₀ P b R₀ π₀ ∧
      M.mem ω.val P ∧ ∃ y : Fin 18 → M.Domain, (∀ k, Rd_entry_d (y k) (x k) π₀) ∧
      y 0 = ω.val ∧ y 4 = x 4 ∧ Rb_reals_d P ω.val (y 2) ∧ Tc_d (y 2) (y 1) ∧
      Fseq_space_d I ω.val ω.val (y 3) ∧ Jp_counter_d lr_payoff_m y ∧ Gs_number_d I ω.val (y 3) (y 7) ∧
      Jp_d I lr_payoff_m (y 1) (y 2) (y 4) (y 5) (y 6) ∧
      ¬ Gs_det_d ω.val (y 2) (y 3) (y 7) (y 8) (y 6) ∧
    ∃ d X₁ R₁ q η, ∃ model : Smem_d I d X₁ R₁, ∃ theory : Zc_model_d I ω.val d X₁ R₁,
      M.TransitiveSet X₁ ∧ M.CardinalLessOrEqual I X₁ ω.val ∧
      Smap_d I ω.val c d X X₁ q ∧ Smap_d I ω.val d dY X₁ Y η ∧ It_comp_d q η π ∧
      let N := smdl_structure_l I (R := R) source.1.2.1
      let N' := smdl_structure_l I (R := R₁) model.1.2.1
      let native := ZFC.models_zf_l (theory.native_l I hZF hw)
      let J := kp_pair_l (ZF.modelsKP native)
    ∃ e : N.Domain → N'.Domain, Pe_d e ∧ (∀ t, Rd_entry_d t.val (e t).val q) ∧
      (e ω).val = ω.val ∧ (e a).val = y 4 ∧ N'.IsOmega (e ω) ∧ Bc_binary_d (e ω) (e a) ∧
      Wd_sequence_d J (e ω) (e A) ∧ N'.IsSetFunctionFromTo J (e A) (e ω) (e μ) ∧
      N'.mem (e μ) (e δ) ∧ Woodin_d J (e δ) ∧ V_d J (e δ) (e Z) ∧
      (∀ t, ¬ N'.mem t (e o)) ∧ Entry_d N' (e o) (e κ) (e A) ∧ Rd_entry_d (e κ).val K η ∧
      Fp_product_d native (e ω) (e A) (e Q) (e U) ∧
    ∃ σ, Rp_name_d native (e ω) (e A) (e Q) σ ∧ ∃ H,
      Gset_d (e Q).val (e U).val (e Q).val X₁ H ∧
      ∀ r, Rp_bg_d hZF model native (e ω) (e A) (e U) H r ↔ M.mem r (y 2) := by
  obtain ⟨m,L,B₀,T₀,α,V₀,d₀,W₀,P,b,R₀,π₀,test,hωP,_,_,fixedX,_,points,
    y,images,eyω,eya,reals,seed,finite,data,number,present,no,C,Y₀,S₀,_,yy,ss,F,run,
    i,r,zero,_,_,ir,v,vr,_,ec,eX,eR,eA,eQ,eU,returned,_⟩ := h
  have frame := (run.queues i r v ir vr).frame
  have xt : M.TransitiveSet X := eX ▸ frame.transitive
  obtain ⟨B,reals',C',D',d,X₁,R₁,J₁,τ,A₁,Q₁,U₁,H,lim,generic,same,count,q,η,root,ret,commute,aa,qq,uu⟩ :=
    run.returned_limit_l hZF test hw hωP target yy ss zero ir vr
      (eX.symm ▸ fixedX) (fun t ht => points t (eX ▸ ht)) returned
  have eqB : B = y 2 := hZF.1.eq_of_same_members _ _ (fun t => (reals' t).trans (reals t).symm)
  have root' : Smap_d I ω.val c d X X₁ q := by simpa only [ec,eX] using! root
  let N := smdl_structure_l I (R := R) source.1.2.1
  let N' := smdl_structure_l I (R := R₁) lim.model.1.2.1
  have hN := ZFC.models_zf_l (certificate.native_l I hZF hw)
  have hN' := ZFC.models_zf_l (lim.theory.native_l I hZF hw)
  let I' := kp_pair_l (ZF.modelsKP hN')
  obtain ⟨e,elem,values⟩ := root'.project_l I hZF hw source.1 lim.model.1
  have ew : e ω = (⟨ω.val,lim.inside.1⟩ : N'.Domain) := Subtype.ext
    (root'.1.1.1.2 _ _ _ (values ω) (root'.omega_l I hZF hw xt lim.transitive source lim.model ω.property))
  have ea : e A = (⟨A₁,lim.inside.2.1⟩ : N'.Domain) := Subtype.ext
    (root'.1.1.1.2 _ _ _ (values A) (eA ▸ aa))
  have eq : e Q = (⟨Q₁,lim.inside.2.2.1⟩ : N'.Domain) := Subtype.ext
    (root'.1.1.1.2 _ _ _ (values Q) (eQ ▸ qq))
  have eu : e U = (⟨U₁,lim.inside.2.2.2⟩ : N'.Domain) := Subtype.ext
    (root'.1.1.1.2 _ _ _ (values U) (eU ▸ uu))
  have clock : N'.IsOmega (e ω) := ew.symm ▸ lim.clock
  have sequence : Wd_sequence_d I' (e ω) (e A) := ew.symm ▸ ea.symm ▸ lim.alphabet
  have product : Fp_product_d hN' (e ω) (e A) (e Q) (e U) :=
    ew.symm ▸ ea.symm ▸ eq.symm ▸ eu.symm ▸ lim.product
  -- 备用配置全部沿同一个原生初等映射运输，不增加极限模型的额外前提。
  have fa' : N'.IsSetFunctionFromTo I' (e A) (e ω) (e μ) := by
    let ρ : Env N 3 := ⟨fun k => [A,ω,μ].get k,fun _ => ω⟩
    exact fn0_function_l (ZF.modelsKP hN') ((fn0_sat_l hN'.1 (image_env_l e ρ) (.bound 1) (.bound 2) (.bound 0)).mp
      ((elem (fn0_m (.bound 1) (.bound 2) (.bound 0)) (by simp -implicitDefEqProofs) ρ).mp
        ((fn0_sat_l hN.1 ρ (.bound 1) (.bound 2) (.bound 0)).mpr (fn0_of_function_l (ZF.modelsKP hN) fa))))
  have wd' : Woodin_d I' (e δ) := by
    let ρ : Env N 1 := ⟨fun _ => δ,fun _ => δ⟩
    exact (woodin_sat_l I' hN'.1 (image_env_l e ρ) .newest).mp
      ((elem (woodin_m (𝒞 := kpair_convention_l) .newest) (by simp -implicitDefEqProofs) ρ).mp
        ((woodin_sat_l (kp_pair_l (ZF.modelsKP hN)) hN.1 ρ .newest).mpr woodin))
  have rank' : V_d I' (e δ) (e Z) := by
    let ρ : Env N 2 := ⟨Fin.cases δ (fun _ => Z),fun _ => δ⟩
    exact (v_sat_l I' hN'.1 (image_env_l e ρ) (.bound 0) (.bound 1)).mp
      ((elem (v_m kpair_convention_l (.bound 0) (.bound 1)) (by simp -implicitDefEqProofs) ρ).mp
        ((v_sat_l (kp_pair_l (ZF.modelsKP hN)) hN.1 ρ (.bound 0) (.bound 1)).mpr rank))
  have binary' : Bc_binary_d (e ω) (e a) := by
    let ρ : Env N 2 := ⟨Fin.cases ω (fun _ => a),fun _ => ω⟩
    exact (bc_binary_sat_l hN'.1 (image_env_l e ρ) (.bound 0) (.bound 1)).mp
      ((elem (bc_binary_m (.bound 0) (.bound 1)) (by simp -implicitDefEqProofs) ρ).mp
        ((bc_binary_sat_l hN.1 ρ (.bound 0) (.bound 1)).mpr binary))
  have empty' : ∀ t, ¬ N'.mem t (e o) := by
    let ρ : Env N 1 := ⟨fun _ => o,fun _ => o⟩
    exact (Formula.satisfies_isEmpty_iff (image_env_l e ρ) .newest).mp
      ((elem (Formula.isEmpty .newest) (by simp -implicitDefEqProofs) ρ).mp
        ((Formula.satisfies_isEmpty_iff ρ .newest).mpr empty))
  have first' := (em_entry_l hN.1 hN'.1 e elem o κ A).mp first
  obtain ⟨t,kt,tk⟩ := (commute.2 κ.val K).mp image
  have et := root'.1.1.1.2 _ _ _ kt (values κ)
  have image' : Rd_entry_d (e κ).val K η := et ▸ tk
  have nat := root'.natural_l hZF hw xt lim.transitive source lim.model ω.property
  have real := (smem_fn0_l I hZF.1 source xt ω ω a).mp binary.1
  have fixed := root'.fixed_function_l hZF hw xt lim.transitive source lim.model
    (root'.omega_l I hZF hw xt lim.transitive source lim.model ω.property) nat ω.property a.property real
    (fun _ t edge => nat t (real.bound_l edge).2)
  have epa : (e a).val = y 4 := (root'.1.1.1.2 _ _ _ (values a) fixed).trans (param.trans eya.symm)
  obtain ⟨σ,name⟩ := rp_name_exists_l hN' clock fa' product
  refine ⟨T₀,α,V₀,d₀,W₀,P,b,R₀,π₀,_,test,hωP,y,images,eyω,eya,reals,seed,finite,data,number,present,no,
    d,X₁,R₁,q,η,lim.model,lim.theory,lim.transitive,count,root',ret,commute,
    e,elem,values,congrArg Subtype.val ew,epa,clock,binary',sequence,fa',
    (em_member_l e elem μ δ).mp small,wd',rank',empty',first',image',product,σ,name,H,?_,?_⟩
  · simpa only [eq,eu] using! generic
  · intro t
    rw [ew,ea,eu]
    exact (same t).trans (by rw [eqB])

end YesMetaZFC.SetTheory.LargeCardinal
