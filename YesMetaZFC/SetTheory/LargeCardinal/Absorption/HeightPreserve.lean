import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Return
import YesMetaZFC.Model.Forcing.Ground.BackgroundExtension
import YesMetaZFC.Model.Forcing.Ground.RealGround
import YesMetaZFC.Model.Forcing.Ground.Ordinals
import YesMetaZFC.Model.Forcing.Reflection.Transitive
import YesMetaZFC.Model.SetTheory.Images.RelationCodeImage
import YesMetaZFC.Model.Forcing.Order.GenericTreeGround
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.OldProduct
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.Model.Forcing.Collapse.ProductCoordinates
import YesMetaZFC.Model.Forcing.Collapse.ProductRealCollapse

/-! # 原 7.23 吸收扩张的背景传递呈示与真实序数

先把同一 H、K 的积泛型编码为背景集合，再坍塌原名字商。
原检查名字逐点还原地对象，函数图读取因此成为指定 x 的字面相等。
扩张的每个序数在该呈示下属于同一迭代目标，不混同不同模型载体。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_real_d.background_l {Ω c X R z Q G b f H x : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    {r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f}
    (real : Ag_real_d hZF r H x) (rel : M.IsSetRelation I x) :
    let N := smdl_structure_l I (R := r.W) r.target.1.2.1
    ∃ K F, Gset_d (r.w 5).val (r.w 6).val (r.w 5).val r.N F ∧
      (∀ q : N.Domain, M.mem q.val F ↔ Ag_prod_d hZF r H K q) ∧
      let E := extension_l N r.native (r.w 5) (r.w 6) (r.w 5) (Ag_prod_d hZF r H K)
      E.Models ZF ∧ ∃ Y, ∃ e : E.Domain → M.Domain,
        M.TransitiveSet Y ∧ M.MemberSubset r.N Y ∧ (∀ a, M.mem (e a) Y) ∧
        Function.Injective e ∧ (∀ a y, M.mem y (e a) ↔ ∃ t, E.mem t a ∧ e t = y) ∧
        (∀ a t, Gval_d N (r.w 5) (r.w 6) (r.w 5) (Ag_prod_d hZF r H K) a t → e t = a.val) ∧
        (∃ y, e y = x) ∧ ∀ ξ, E.IsOrdinal ξ → M.IsOrdinal (e ξ) ∧ M.mem (e ξ) r.N := by
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  obtain ⟨_,_,_,_,_,_,K,_,_,generic,τ,C,_,_,j,_,_,checks,y,_,fn,read,_⟩ := real
  obtain ⟨_,O,hbase,top,_⟩ := r.product_data_l hZF hw source native s
  let E := extension_l N r.native (r.w 5) (r.w 6) (r.w 5) (Ag_prod_d hZF r H K)
  have hE : E.Models ZF := preserves_zf_l O r.native generic
  have ni : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have nf := smem_full_l I r.target r.transitive
  -- 积滤子取条件域与 H×K 的实际交集。
  obtain ⟨D,product⟩ := ZF.exists_cartesianProduct hZF I H K
  obtain ⟨F,inter⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) (r.w 5).val D
  have accepted (q : N.Domain) : M.mem q.val F ↔ Ag_prod_d hZF r H K q := by
    rw [inter q.val]
    constructor
    · rintro ⟨hq,hD⟩
      obtain ⟨a,ha,t,ht,pair⟩ := (product q.val).mp hD
      have inside := trans_kpair_l r.transitive q.property pair
      let a' : N.Domain := ⟨a,inside.1⟩
      let t' : N.Domain := ⟨t,inside.2⟩
      exact ⟨(image_member_l Subtype.val ni nf).mp hq,a',t',
        (smem_kpair_l I r.target.1 r.target.2 r.transitive q a' t').mpr pair,ha,ht⟩
    · rintro ⟨hq,a,t,pair,ha,ht⟩
      exact ⟨(image_member_l Subtype.val ni nf).mpr hq,
        (product q.val).mpr ⟨a.val,ha,t.val,ht,(smem_kpair_l I r.target.1 r.target.2 r.transitive q a t).mp pair⟩⟩
  have predicate : (fun q : N.Domain => M.mem q.val F) = Ag_prod_d hZF r H K :=
    funext fun q => propext (accepted q)
  have coded : Gset_d (r.w 5).val (r.w 6).val (r.w 5).val r.N F :=
    (r.target.generic_code_l I hZF.1 r.transitive (ZF.modelsKP r.native) (r.w 5) (r.w 6) (r.w 5) F).mpr
      ⟨fun a ha => ((inter a).mp ha).1,predicate.symm ▸ generic⟩
  have background := bg_extension_l hZF r.target r.transitive r.native O coded
  dsimp only at background
  rw [predicate] at background
  obtain ⟨Y,e,trans,range,inj,full,fixed⟩ := background
  obtain ⟨q,hq⟩ := generic.inhabited
  have base := generic.upward q (r.w 8) hq hbase (top q (generic.proper q hq).1)
  have ground a : Gval_d N (r.w 5) (r.w 6) (r.w 5) (Ag_prod_d hZF r H K) a (j a) := by
    obtain ⟨t,check,_,_⟩ := zf_check_l N r.native hbase a
    exact ⟨r.w 8,t,base,check,checks a t check⟩
  have commute a : e (j a) = a.val := fixed a (j a) (ground a)
  have eq : e y = x := read.image_eq_l (ZF.modelsKP hZF) (ZF.modelsKP hE) e inj full nf commute fn rel
  obtain ⟨k,checked,_,_,ordinals⟩ := check_map_ordinals_l O r.native generic hq
  refine ⟨K,F,coded,accepted,hE,Y,e,trans,fun a ha => ?_,range,inj,full,fixed,⟨y,eq⟩,?_⟩
  · have eq : e (j ⟨a,ha⟩) = a := commute ⟨a,ha⟩
    exact eq ▸ range (j ⟨a,ha⟩)
  · intro ξ ordinal
    obtain ⟨α,hα,eq⟩ := (ordinals ξ).mp ordinal
    have old := (gval_check_map_l O r.native generic hq k checked α (k α)).mpr rfl
    have same : e ξ = α.val := (congrArg e eq).symm.trans (fixed α (k α) old)
    exact same.symm ▸ ⟨image_ord_l r.native hZF Subtype.val ni nf hα,α.property⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 被原 7.23 吸收的良序实数给出严格高度下界

从同一次积泛型的背景呈示恢复编码实数。源中实际解码并坍塌的序型
映为指定背景序数；无新序数结论使它已经属于原迭代目标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_real_d.code_height_l {Ω c X R z Q G b f H x β : M.Domain} (hw : M.IsOmega Ω)
    (source : Smem_d I c X R)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    {r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f}
    (real : Ag_real_d hZF r H x) (code : Wo_code_d I Ω x β) : M.mem β r.N := by
  obtain ⟨K,F,_,_,hE,Y,e,_,_,_,inj,full,_,⟨y,ey⟩,ordinals⟩ :=
    real.background_l hZF hw source native s (fn0_function_l (ZF.modelsKP hZF) code.1.1).1.1
  let N := smdl_structure_l I (R := r.W) r.target.1.2.1
  let E := extension_l N r.native (r.w 5) (r.w 6) (r.w 5) (Ag_prod_d hZF r H K)
  obtain ⟨w,hwE⟩ := ZF.exists_omega hE
  have moved : M.IsOmega (e w) := image_omega_l (hEN := hZF.1) e inj full hE
    (fun _ => KP.mem_minimal_exists_d (ZF.modelsKP hZF)) hwE
    (fun D => KP.difference_exists_d (ZF.modelsKP hZF) D (e w))
  have ew : e w = Ω := hZF.1.eq_of_same_members _ _ (fun i => ⟨moved.2 Ω hw.1 i,hw.2 (e w) moved.1 i⟩)
  have code' : Wo_code_d I (e w) (e y) β := by simpa only [ew,ey] using code
  obtain ⟨α,hα,eq,_⟩ := code'.pull_type_l hE hZF e inj full hwE
  exact eq ▸ (ordinals α hα).2

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 一次原 7.23 运行超过任意指定背景可数序数

小泛型由源载体的实际计数和背景 DC 构造。指定序数先编码为一个实数，
原专用博弈及复制返回枝吸收它，再由序型回收取得严格高度下界。
输出保留同一完整迭代树、临界点界、返回因子和两级泛型，供旧资料保持使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ag_height_l {Ω c X R d Y S θ π β : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d I Ω c X R) (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X Ω)
    (targetRank : V_d I θ Y) (target : Smem_d I d Y S) (embed : Smap_d I Ω c d X Y π)
    {ω κ δ Z : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) certificate.model.2.1).IsOmega ω)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ Z)
    (small : (smdl_structure_l I (R := R) certificate.model.2.1).mem κ δ)
    (hβ : M.IsOrdinal β) (countβ : M.CardinalLessOrEqual I β Ω) :
    let N := smdl_structure_l I (R := R) certificate.model.2.1
    let native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
    ∃ p : Ag_forcing_d native ω κ δ ω, ∃ s : Ag_system_d native p,
      ∃ z H x f, (∀ a, ¬ M.mem a z) ∧ M.MemberSubset H p.Q.val ∧
        Generic_d N p.Q p.T p.Q (fun q => M.mem q.val H) ∧ Wo_code_d I Ω x β ∧
        Ag_trace_d hZF Ω ω.val s.A.val s.F₀.val s.R₀.val f x H ∧
        ∃ ρ γ T Q G E b, Rk_d I (s.aux_params_l native 10).val ρ ∧ M.mem ρ γ ∧ M.IsOrdinal γ ∧
          It_tree_d hZF Ω c Ω T Q G E ∧ It_critical_bound_d I γ Q E ∧
          It_return_at_d hZF Ω z T Q G d Y π b ∧ It_wf_branch_d hZF Ω Ω T Q G b ∧
          ∃ r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f,
          ∃ σ, Smap_d I Ω r.d d r.N Y σ ∧ It_comp_d r.j σ π ∧
            M.CardinalLessOrEqual I r.N Ω ∧
            Generic_d (smdl_structure_l I (R := r.W) r.target.1.2.1)
              (r.w 1) (r.w 2) (r.w 1) (fun q => M.mem q.val H) ∧
            Ag_real_d hZF r H x ∧ M.mem β r.N := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  have native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
  let J := kp_pair_l (ZF.modelsKP native)
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have moved : M.IsOmega ω.val := image_omega_l (hEN := hZF.1) Subtype.val inj full native
    (fun _ => KP.mem_minimal_exists_d (ZF.modelsKP hZF)) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hZF) D ω.val)
  have eω : ω.val = Ω := hZF.1.eq_of_same_members _ _ (fun i => ⟨moved.2 Ω hΩ.1 i,hΩ.2 ω.val moved.1 i⟩)
  have letters : N.mem ω Z := by
    obtain ⟨ω₀,_,hw₀,above,_,_,_,_⟩ := woodin
    have eq : ω₀ = ω := native.1.eq_of_same_members _ _ (fun i => ⟨hw₀.2 ω hw.1 i,hw.2 ω₀ hw₀.1 i⟩)
    exact ZF.v_ordinal_mem_l J native rank (eq ▸ above)
  obtain ⟨a,_,ha⟩ := hw.1.1
  obtain ⟨p,s,z,empty,absorb⟩ := ag_absorb_l hZFC hΩ certificate source trans count targetRank target embed
    hw woodin rank letters ⟨a,ha⟩ small
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,H,_,_,_,_,_,_,_,sub,_,generic⟩ :=
    gn_source_branch_l hZF hΩ (ZFC.dc_l I hZFC hΩ) source trans native count p.Q p.T p.b p.small_order p.small_base
  obtain ⟨x,code⟩ := wo_code_exists_l hZF hΩ hβ countβ
  have fx : Fn0_d Ω ω.val x := by simpa only [eω] using code.1.1
  obtain ⟨f,trace,returned⟩ := absorb H x sub generic fx
  obtain ⟨ρ,γ,T,Q,G,E,b,rk,lower,ordinal,tree,bound,returned,wf,r,σ,factor,commute,countN,smallG,real⟩ := returned
  exact ⟨p,s,z,H,x,f,empty,sub,generic,code,trace,ρ,γ,T,Q,G,E,b,rk,lower,ordinal,tree,bound,returned,wf,
    r,σ,factor,commute,countN,smallG,real,real.code_height_l hZF hΩ source native s code⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一次高度吸收保留原全乘积和派生实数族

从备用 Woodin 以下的字母表共同界自动选取 κ；原 7.23 返回枝既超过指定
背景可数序数，又逐点固定共同 Vκ。新的小泛型只编码高度，最终 R* 使用
原全乘积泛型 H₀。共同层、目标泛型和实数族相等均由此次实际运行导出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ag_height_preserve_l {Ω c X R d Y S θ π β H₀ : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d I Ω c X R) (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X Ω)
    (targetRank : V_d I θ Y) (target : Smem_d I d Y S) (embed : Smap_d I Ω c d X Y π)
    {ω δ Z A₀ P T μ σ : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ Z)
    (small : (smdl_structure_l I (R := R) source.1.2.1).mem μ δ)
    (fa : (smdl_structure_l I (R := R) source.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) A₀ ω μ)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω A₀ P T)
    (name : Rp_name_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω A₀ P σ)
    (generic : Gset_d P.val T.val P.val X H₀)
    (hβ : M.IsOrdinal β) (countβ : M.CardinalLessOrEqual I β Ω) :
    let N := smdl_structure_l I (R := R) source.1.2.1
    let native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
    ∃ κ V : N.Domain, N.mem κ δ ∧ V_d (kp_pair_l (ZF.modelsKP native)) κ V ∧
      (∀ a, a ∈ [ω,P,σ] → N.mem a V) ∧
      ∃ p : Ag_forcing_d native ω κ δ ω, ∃ s : Ag_system_d native p,
      ∃ z H x f, (∀ a, ¬ M.mem a z) ∧ M.MemberSubset H p.Q.val ∧
        Generic_d N p.Q p.T p.Q (fun q => M.mem q.val H) ∧ Wo_code_d I Ω x β ∧
        Ag_trace_d hZF Ω ω.val s.A.val s.F₀.val s.R₀.val f x H ∧
        ∃ ρ γ T₁ Q G E b, Rk_d I (s.aux_params_l native 10).val ρ ∧ M.mem ρ γ ∧ M.IsOrdinal γ ∧
          It_tree_d hZF Ω c Ω T₁ Q G E ∧ It_critical_bound_d I γ Q E ∧
          It_return_at_d hZF Ω z T₁ Q G d Y π b ∧ It_wf_branch_d hZF Ω Ω T₁ Q G b ∧
          ∃ r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f,
          ∃ η, Smap_d I Ω r.d d r.N Y η ∧ It_comp_d r.j η π ∧
            M.CardinalLessOrEqual I r.N Ω ∧ Zc_model_d I Ω r.d r.N r.W ∧
            Ag_real_d hZF r H x ∧ M.mem β r.N ∧
            let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
            ∃ e : N.Domain → N'.Domain, Pe_d e ∧ (∀ a, Rd_entry_d a.val (e a).val r.j) ∧
              (∀ a, M.mem a.val V.val → (e a).val = a.val) ∧
              Fp_product_d r.native (e ω) (e A₀) (e P) (e T) ∧
              Rp_name_d r.native (e ω) (e A₀) (e P) (e σ) ∧
              N'.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP r.native)) (e A₀) (e ω) (e μ) ∧
              Gset_d (e P).val (e T).val (e P).val r.N H₀ ∧
              ∀ x, Rp_bg_d hZF source native ω A₀ T H₀ x ↔
                Rp_bg_d hZF r.target r.native (e ω) (e A₀) (e T) H₀ x := by
  let native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
  let J := kp_pair_l (ZF.modelsKP native)
  have wd := woodin
  obtain ⟨ω₀,_,hw₀,above,regular,strong,_,_⟩ := wd
  have eqω : ω₀ = ω := native.1.eq_of_same_members _ _ (fun a => ⟨hw₀.2 ω hw.1 a,hw.2 ω₀ hw₀.1 a⟩)
  have high := eqω ▸ above
  have limit := regular.isLimitOrdinal
  have hω := ZF.v_ordinal_mem_l J native rank high
  have hμ := ZF.v_ordinal_mem_l J native rank small
  have hP := product.rank_mem_l native hw rank limit hω hμ
    (fun i κ edge => ((v_ordinal_l J rank).mem small).transitive κ (fa.output_mem_of_pairMember edge))
  -- 规范名字的秩界来自实际 Vδ 模型中的统一检查名字库。
  obtain ⟨c₀,R₀,model,cert⟩ := zc_inaccessible_l (certificate.native_l I hZF hΩ) hw high regular strong rank
  have hσ := name.rank_mem_l native model rank limit (ZFC.models_zf_l (cert.native_l J native hw)) hω hP product
  have inside a (ha : a ∈ [ω,P,σ]) : (smdl_structure_l I (R := R) source.1.2.1).mem a Z := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact hω
    · exact hP
    · exact hσ
  obtain ⟨κ,V,small,low,bound⟩ := ZF.v_list_bound_l (kp_pair_l (ZF.modelsKP native)) native rank limit _ inside
  -- 先选共同低秩界，再用同一次运行吸收高度代码并提升原 H₀。
  obtain ⟨p,s,z,H,x,f,empty,sub,g,code,trace,ρ,γ,T₁,Q,G,E,b,rk,lower,ordinal,tree,critical,
      returned,wf,r,η,factor,commute,countN,_,real,height⟩ :=
    ag_height_l hZFC hΩ certificate source trans count targetRank target embed hw woodin rank small hβ countβ
  obtain ⟨e,elem,values,fixed,product',name',fa',generic',same⟩ :=
    r.old_product_l hZF hΩ source trans native s hw low bound fa product name generic
  exact ⟨κ,V,small,low,bound,p,s,z,H,x,f,empty,sub,g,code,trace,ρ,γ,T₁,Q,G,E,b,rk,lower,ordinal,tree,
    critical,returned,wf,r,η,factor,commute,countN,certificate.map_l hZF hΩ r.target.1 r.map,
    real,height,e,elem,values,fixed,product',name',fa',generic',same⟩

end YesMetaZFC.SetTheory.LargeCardinal
