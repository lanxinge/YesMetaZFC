import YesMetaZFC.SetTheory.LargeCardinal.Absorption.HeightPreserve
import YesMetaZFC.SetTheory.LargeCardinal.Determinacy.TwinTreeOutward
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.CounterLimit

/-! # 同一次高度吸收中的原参数决定性

原 H 保持泛型且 R* 不变。返回交换律把新第一坐标的像识别为原真实大基数，
从而可在真实返回秩层排除最小坏代码。原实数参数逐点固定；检查映射、
规范实数并的实际值、传递种子和派生模型都在同一个旧 H 扩张中构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ag_height_det_l {φ : Formula 1 4} (hc : φ.FreeClosed)
    {c X R d Y S₀ θ π β H₀ K : M.Domain} (source : Smem_d I c X R)
    (ω : (smdl_structure_l I (R := R) source.1.2.1).Domain) (hw : M.IsOmega ω.val)
    (certificate : Zc_model_d I ω.val c X R) (trans : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X ω.val)
    (target : Smem_d I d Y S₀) (rank : V_d I θ Y) (embed : Smap_d I ω.val c d X Y π)
    {δ Z₀ A₀ P V μ σ a₀ o κ₀ : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) δ)
    (rankδ : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) δ Z₀)
    (small : (smdl_structure_l I (R := R) source.1.2.1).mem μ δ)
    (fa : (smdl_structure_l I (R := R) source.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) A₀ ω μ)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A₀ P V)
    (name : Rp_name_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A₀ P σ)
    (generic : Gset_d P.val V.val P.val X H₀) (binary : Bc_binary_d ω a₀)
    (empty : ∀ x, ¬ (smdl_structure_l I (R := R) source.1.2.1).mem x o)
    (alphabet : Entry_d (smdl_structure_l I (R := R) source.1.2.1) o κ₀ A₀)
    (image : Rd_entry_d κ₀.val K π) (hK : M.IsUncountableCardinal I ω.val K)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) ω A₀)
    {α Vα : M.Domain} (hα : Woodin_d I α) (rankα : V_d I α Vα)
    (inside : M.mem ω.val Vα) (bound : M.MemberSubset α K)
    (hβ : M.IsOrdinal β) (countβ : M.CardinalLessOrEqual I β ω.val) :
    ∃ c₁ X₁ R₁ j η, ∃ model : Smem_d I c₁ X₁ R₁, ∃ theory : Zc_model_d I ω.val c₁ X₁ R₁,
      M.TransitiveSet X₁ ∧ M.CardinalLessOrEqual I X₁ ω.val ∧ M.mem β X₁ ∧
      Smap_d I ω.val c c₁ X X₁ j ∧ Smap_d I ω.val c₁ d X₁ Y η ∧ It_comp_d j η π ∧
      let N := smdl_structure_l I (R := R) source.1.2.1
      let N' := smdl_structure_l I (R := R₁) model.1.2.1
      let hN := ZFC.models_zf_l (certificate.native_l I hZF hw)
      let hN' := ZFC.models_zf_l (theory.native_l I hZF hw)
      ∃ e : N.Domain → N'.Domain, Pe_d e ∧ (∀ a, Rd_entry_d a.val (e a).val j) ∧
        (e ω).val = ω.val ∧ (e a₀).val = a₀.val ∧
        ∃ product' : Fp_product_d hN' (e ω) (e A₀) (e P) (e V),
        Rp_name_d hN' (e ω) (e A₀) (e P) (e σ) ∧
        N'.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hN')) (e A₀) (e ω) (e μ) ∧
        Gset_d (e P).val (e V).val (e P).val X₁ H₀ ∧
        (∀ x, Rp_bg_d hZF source hN ω A₀ V H₀ x ↔ Rp_bg_d hZF model hN' (e ω) (e A₀) (e V) H₀ x) ∧
        let H : N'.Domain → Prop := fun q => M.mem q.val H₀
        ∃ g : Generic_d N' (e P) (e V) (e P) H,
        let E := extension_l N' hN' (e P) (e V) (e P) H
        ∃ k : N'.Domain → E.Domain, (∀ a, Gval_d N' (e P) (e V) (e P) H a (k a)) ∧
          ∃ Z S, Qval_d N' (e P) (e V) (e P) H (e σ) Z ∧ ∃ tc : Tc_d Z S,
          let hE := preserves_zf_l (product'.order_l hN') hN' g
          let D := Relative.la_model_l S (ZF.models_kpi_l hE)
          let hD := Relative.la_model_zf_l S hE tc.1
          let J := kp_pair_l (ZF.modelsKP hD)
          ∃ w b s T a : D.Domain, w.val = k (e ω) ∧ b.val = Z ∧ s.val = S ∧ a.val = k (e a₀) ∧
            Lr_seed_d hD w b s ∧ Fseq_space_d J w w T ∧ D.mem a b ∧
            ∀ q A, Jp_d J φ s b a q A → Det_d J w b T A := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  have native := ZFC.models_zf_l (certificate.native_l I hZF hw)
  let nx : Nonempty {x // M.mem x X} := ⟨ω⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => ω,fun _ => ω⟩
  have hwN : N.IsOmega ω := (Formula.satisfies_isOmega_iff _ .newest).mp
    ((smem_formula_l I source nx (Formula.isOmega .newest) ρ).mp
      ((Formula.satisfies_isOmega_iff ρ .newest).mpr (rt_omega_l trans nx hZF.1 ω hw)))
  obtain ⟨ν,B₀,_,_,low,p,s,z,H,x,f,_,_,_,_,_,ρ₀,γ,T₁,Q,G,E₀,b,_,_,_,_,_,_,_,r,η,
      factor,commute,countN,theory,_,height,e,elem,values,fixed,product',name',fa',generic',same⟩ :=
    ag_height_preserve_l hZFC hw certificate source trans count rank target embed hwN woodin rankδ small
      fa product name generic hβ countβ
  let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
  have eqω : (e ω).val = ω.val := fixed ω (((source.2 ω.val B₀.val).mp (low ω (by simp))).2.2)
  have hw' : M.IsOmega (e ω).val := eqω.symm ▸ hw
  -- 实数的定义域和各实际值都是自然数，原根腿遂固定整张图。
  have naturals := r.map.natural_l hZF hw trans r.transitive source r.target ω.property
  have real := (smem_fn0_l I hZF.1 source trans ω ω a₀).mp binary.1
  have aa := r.map.fixed_function_l hZF hw trans r.transitive source r.target
    (r.map.omega_l I hZF hw trans r.transitive source r.target ω.property) naturals ω.property a₀.property real
    (fun _ y edge => naturals y (real.bound_l edge).2)
  have eqa : (e a₀).val = a₀.val := r.map.1.1.1.2 _ _ _ (values a₀) aa
  -- 返回方块识别第一大基数的真实像；无需把可数源中的 κ₀ 当作背景不可数基数。
  obtain ⟨t,kt,tk⟩ := (commute.2 κ₀.val K).mp image
  have eqt := r.map.1.1.1.2 _ _ _ kt (values κ₀)
  have image' : Rd_entry_d (e κ₀).val K η := eqt ▸ tk
  have binary' : Bc_binary_d (e ω) (e a₀) := by
    let ρ : Env N 2 := ⟨fun i => [ω,a₀].get i,fun _ => ω⟩
    exact (bc_binary_sat_l r.native.1 (image_env_l e ρ) (.bound 0) (.bound 1)).mp
      ((elem (bc_binary_m (.bound 0) (.bound 1)) (by simp -implicitDefEqProofs) ρ).mp
        ((bc_binary_sat_l native.1 ρ (.bound 0) (.bound 1)).mpr binary))
  have empty' : ∀ a, ¬ N'.mem a (e o) := by
    let ρ : Env N 1 := ⟨fun _ => o,fun _ => o⟩
    exact (Formula.satisfies_isEmpty_iff (image_env_l e ρ) .newest).mp
      ((elem (Formula.isEmpty .newest) (by simp -implicitDefEqProofs) ρ).mp
        ((Formula.satisfies_isEmpty_iff ρ .newest).mpr empty))
  have first' := (em_entry_l native.1 r.native.1 e elem o κ₀ A₀).mp alphabet
  have sequence' := sequence.image_l (kp_pair_l (ZF.modelsKP native))
    (kp_pair_l (ZF.modelsKP r.native)) native.1 r.native.1 e elem
  let H' : N'.Domain → Prop := fun q => M.mem q.val H₀
  have g : Generic_d N' (e P) (e V) (e P) H' :=
    ((r.target.generic_code_l I hZF.1 r.transitive (ZF.modelsKP r.native) (e P) (e V) (e P) H₀).mp generic').2
  let E := extension_l N' r.native (e P) (e V) (e P) H'
  have hE : E.Models ZF := preserves_zf_l (product'.order_l r.native) r.native g
  obtain ⟨Z,value,_⟩ := name'.value_l r.native (by
    let ρ : Env N 1 := ⟨fun _ => ω,fun _ => ω⟩
    exact (Formula.satisfies_isOmega_iff (image_env_l e ρ) .newest).mp
      ((elem (Formula.isOmega .newest) (by simp -implicitDefEqProofs) ρ).mp
        ((Formula.satisfies_isOmega_iff ρ .newest).mpr hwN))) fa' product' g
  obtain ⟨q,hq⟩ := g.inhabited
  obtain ⟨k,checks,_,_⟩ := check_map_l (product'.order_l r.native) r.native g hq
  have ground a := (gval_check_map_l (product'.order_l r.native) r.native g hq k checks a (k a)).mpr rfl
  obtain ⟨S,tc⟩ := ZF.tc_exists_l (kp_pair_l (ZF.modelsKP hE)) hE Z
  have determined := qs_derived_det_l hZFC hc r.target r.transitive (e ω) hw' (eqω.symm ▸ theory)
    target rank (eqω.symm ▸ factor) fa' product' name' binary' empty' first' image' (eqω.symm ▸ hK)
    sequence' hα rankα (eqω.symm ▸ inside) bound H' g k ground Z value S tc
  exact ⟨r.d,r.N,r.W,r.j,η,r.target,theory,r.transitive,countN,height,r.map,factor,commute,
    e,elem,values,eqω,eqa,product',name',fa',generic',same,g,k,ground,Z,S,value,tc,determined⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从原反例构造超过测试壳高度的固定参数决定模型

两层 hull、原吸收极限及高度吸收依次使用同一原参数。测试壳高度由
背景有界分离实际构造，其可数性继承自壳。高度吸收保留原极限泛型，
所以最终派生实数仍恰为该反例的实数族；固定参数决定性由实际返回图取得。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem wd_counterexample_height_l (proper : Wd_proper_d I) (bad : ¬ M.SatisfiesSentence Axioms.lr_ad) :
    ∃ Ω, ∃ hw : M.IsOmega Ω,
    ∃ T₀ α₀ V₀ d₀ W₀ P b₀ R₀ π₀, ∃ z : Fin 23 → M.Domain,
      Rf_hull_d hZF Ω T₀ (ab_test_queries_l lr_ad_m lr_ad_closed_l) z α₀ V₀ d₀ W₀ P b₀ R₀ π₀ ∧
      M.mem Ω P ∧ ∃ y : Fin 18 → M.Domain, (∀ k, M.mem (y k) P) ∧
      y 0 = Ω ∧ Rb_reals_d P Ω (y 2) ∧ Tc_d (y 2) (y 1) ∧
      Fseq_space_d I Ω Ω (y 3) ∧ Jp_counter_d lr_payoff_m y ∧ Gs_number_d I Ω (y 3) (y 7) ∧
      Jp_d I lr_payoff_m (y 1) (y 2) (y 4) (y 5) (y 6) ∧
      ¬ Gs_det_d Ω (y 2) (y 3) (y 7) (y 8) (y 6) ∧
    ∃ β, Oh_bound_d P β ∧ M.CardinalLessOrEqual I β Ω ∧
    ∃ c X R, ∃ model : Smem_d I c X R, ∃ theory : Zc_model_d I Ω c X R,
      M.TransitiveSet X ∧ M.CardinalLessOrEqual I X Ω ∧ M.mem β X ∧
      let N := smdl_structure_l I (R := R) model.1.2.1
      let native := ZFC.models_zf_l (theory.native_l I hZF hw)
    ∃ w A Q U σ a μ : N.Domain, w.val = Ω ∧ a.val = y 4 ∧
      N.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP native)) A w μ ∧
    ∃ product : Fp_product_d native w A Q U, Rp_name_d native w A Q σ ∧
    ∃ H₀, Gset_d Q.val U.val Q.val X H₀ ∧
      (∀ r, Rp_bg_d hZF model native w A U H₀ r ↔ M.mem r (y 2)) ∧
      let H : N.Domain → Prop := fun q => M.mem q.val H₀
    ∃ g : Generic_d N Q U Q H,
      let E := extension_l N native Q U Q H
    ∃ k : N.Domain → E.Domain, (∀ t, Gval_d N Q U Q H t (k t)) ∧
    ∃ Z S, Qval_d N Q U Q H σ Z ∧ ∃ tc : Tc_d Z S,
      let hE := preserves_zf_l (product.order_l native) native g
      let D := la_model_l S (ZF.models_kpi_l hE)
      let hD := la_model_zf_l S hE tc.1
      let J := kp_pair_l (ZF.modelsKP hD)
    ∃ w' b s T a' : D.Domain, w'.val = k w ∧ b.val = Z ∧ s.val = S ∧ a'.val = k a ∧
      Lr_seed_d hD w' b s ∧ Fseq_space_d J w' w' T ∧ D.mem a' b ∧
      ∀ q B, Jp_d J lr_payoff_m s b a' q B → Det_d J w' b T B := by
  -- 一、原反例、初始源及测试壳都由原真类 Woodin 假设生成。
  obtain ⟨x,seed,data,θ,Y,dY,SY,target,rankY,_,c₀,X₀,R',π,source,certificate,_,_,_,
    ω,A₀,μ,δ,Z₀,o,κ,a₀,Q₀,U₀,_,eω,ea,_,_,binary,_,fa,small,woodin,rankδ,empty,first,
    K,α,Vα,image,hK,large,rankα,inside,bound,_,_,G,_,run⟩ := wd_counterexample_run_l hZFC proper bad
  have hw : M.IsOmega ω.val := eω.symm ▸ seed.1.1
  have cert : Zc_model_d I ω.val c₀ X₀ R' := eω.symm ▸ certificate
  have run' : Ab_counter_run_d hZF ω.val c₀ X₀ R' dY Y SY π A₀.val Q₀.val U₀.val G x := eω.symm ▸ run
  obtain ⟨T₀,α₀,V₀,d₀,W₀,P,b₀,R₀,π₀,z,test,hωP,y,images,eyω,_,reals,tc₀,finite,data',number,present,no,
    c₁,X₁,R₁,q,η,model₁,theory₁,trans₁,count₁,_,ret,_,e,_,_,ew,epa,_,binary',sequence',fa',small',wd',rank',
    empty',first',image',product',σ₁,name',H₀,generic,same⟩ :=
    run'.limit_l hZF source hw cert target woodin rankδ small fa binary empty first image ea
  -- 二、壳的实际序数高度是可数集合；同一次高度吸收继续使用原极限 H₀。
  obtain ⟨β,height,countβ⟩ := oh_countable_l hZF test.transitive test.count
  have hw₁ : M.IsOmega (e ω).val := ew.symm ▸ hw
  have theory₁' : Zc_model_d I (e ω).val c₁ X₁ R₁ := ew.symm ▸ theory₁
  have ret' : Smap_d I (e ω).val c₁ dY X₁ Y η := ew.symm ▸ ret
  have count₁' : M.CardinalLessOrEqual I X₁ (e ω).val := ew.symm ▸ count₁
  have hK' : M.IsUncountableCardinal I (e ω).val K := ew.symm ▸ eω.symm ▸ hK
  have inside' : M.mem (e ω).val Vα := ew.symm ▸ eω.symm ▸ inside
  obtain ⟨c₂,X₂,R₂,_,_,model₂,theory₂,trans₂,count₂,high,_,_,_,f,_,_,fw,faeq,
    product₂,name₂,fa₂,generic₂,keep,g,k,ground,Z,S,value,tc,determined⟩ :=
    ag_height_det_l hZFC lr_payoff_closed_l model₁ (e ω) hw₁ theory₁' trans₁ count₁'
      target rankY ret' wd' rank' small' fa' product' name' generic binary' empty' first' image' hK'
      sequence' large rankα inside' bound height.ordinal (ew.symm ▸ countβ)
  -- 三、保留最终实际扩张及派生模型，实数族仍是同一反例的实数迹。
  have finalω : (f (e ω)).val = ω.val := fw.trans ew
  have finala : (f (e a₀)).val = y 4 := faeq.trans epa
  have realTrace r := (keep r).symm.trans (same r)
  refine ⟨ω.val,hw,T₀,α₀,V₀,d₀,W₀,P,b₀,R₀,π₀,z,test,hωP,y,
    (fun k => test.map.1.1.input_mem_of_pairMember (images k)),eyω,reals,tc₀,finite,data',number,present,no,
    β,height,countβ,c₂,X₂,R₂,model₂,ew ▸ theory₂,trans₂,ew ▸ count₂,high,
    f (e ω),f (e A₀),f (e Q₀),f (e U₀),f σ₁,f (e a₀),f (e μ),finalω,finala,fa₂,
    product₂,name₂,H₀,generic₂,realTrace,g,k,ground,Z,S,value,tc,determined⟩

end YesMetaZFC.SetTheory.LargeCardinal
