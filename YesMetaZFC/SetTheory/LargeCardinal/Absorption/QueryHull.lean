import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Links
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Realization
import YesMetaZFC.Model.SetTheory.Reflection.ReflectedSeed
import YesMetaZFC.SetTheory.Descriptive.Topology.Completion
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.TestRun
import YesMetaZFC.Model.Forcing.Collapse.ProductTruthPrefix
import YesMetaZFC.Model.Forcing.Order.QueryAttempt
import YesMetaZFC.Model.Forcing.Functions.ValueIsomorphism
import YesMetaZFC.Model.Forcing.Ground.RealValue
import YesMetaZFC.Model.Forcing.Ground.RealGround
import YesMetaZFC.Model.Forcing.Ground.NaturalRead
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Order.QueryContext
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed

/-! # 有限反射测试壳到真实 L(ℝ) 的出口

最终只运输给定的派生模型断言，随后在背景的规范 L(ℝ) 中恢复同一见证。
真值运输无需测试模型满足完整 ZFC。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}
section Upload
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_test_upload_l {ω T α V d S P c R π B : M.Domain} {n m}
    {φ : Formula 1 n} (hc : φ.FreeClosed) {v : Fin m → M.Domain}
    (h : Rf_hull_d hZF ω T (ab_test_queries_l φ hc) v α V d S P c R π)
    (space : Baire_d I ω B) (x : Fin n → M.Domain)
    (ρ : Env (smdl_structure_l I (R := R) h.model.1.2.1) (n+1))
    (images : ∀ k, Rd_entry_d (ρ.bound k).val (Fin.cases B x k) π)
    (truth : Formula.satisfies ρ (Relative.dr_m φ .newest (fun i => .bound i.succ))) :
    ∃ b : (Relative.lr_model_l hZF).Domain, b.val = B ∧
    ∃ y : Fin n → (Relative.lr_model_l hZF).Domain,
      (∀ i, (y i).val = x i) ∧ Sr_truth_d b φ y := by
  let ψ := Relative.dr_m φ (.newest : Term (n+1)) (fun i => .bound i.succ)
  let η : Env M (n+1) := ⟨Fin.cases B x,fun _ => B⟩
  have moved := (h.formula_l hZF space.1 ψ (Relative.dr_closed_l φ hc _ _ rfl (fun _ => rfl))
    (by simp [ab_test_queries_l,ψ]) ρ η images).mp truth
  have dr : Relative.Dr_truth_d B φ x := (Relative.dr_sat_l (ZF.modelsKP hZF) φ hc η _ _).mp moved
  obtain ⟨S₀,tc,_⟩ := dr.2
  have seed : Relative.Lr_seed_d hZF ω B S₀ := ⟨space,tc⟩
  obtain ⟨b,bB,y,values,sr⟩ := (Relative.dr_model_l (ZF.models_kpi_l hZF) tc φ hc x).mp dr
  let K := Relative.la_model_l S₀ (ZF.models_kpi_l hZF)
  let L := Relative.lr_model_l hZF
  let f : K.Domain → L.Domain := fun a => ⟨a.val,(Relative.lr_iff_l hZF seed a.val).mpr a.property⟩
  have fi : Function.Injective f := fun _ _ eq =>
    Subtype.ext (congrArg (fun z : L.Domain => z.val) eq)
  have ff (a : K.Domain) (z : L.Domain) : L.mem z (f a) ↔ ∃ b, K.mem b a ∧ f b = z := by
    constructor
    · intro hz
      exact ⟨⟨z.val,Relative.la_transitive_l S₀ (ZF.models_kpi_l hZF) tc.1 a.property hz⟩,hz,Subtype.ext rfl⟩
    · rintro ⟨b,hb,rfl⟩
      exact hb
  exact ⟨f b,bB,(fun i => f (y i)),values,Sr_truth_d.image_l (M := K) (N := L) f fi ff hc sr⟩

/-- 同一吸收运行的原行断言，经有限反射进入真实背景 L(ℝ)，实数参数逐点不变。 -/
theorem Ab_run_d.test_truth_l {ω T α V d S P c R π : M.Domain} {n m}
    {φ : Formula 1 n} (hc : φ.FreeClosed) {v : Fin m → M.Domain}
    (test : Rf_hull_d hZF ω T (ab_test_queries_l φ hc) v α V d S P c R π)
    (hw : M.IsOmega ω) (hω : M.mem ω P)
    {cY Y U : (smdl_structure_l I (R := R) test.model.1.2.1).Domain} {F : M.Domain}
    (run : Ab_run_d I P ω cY.val Y.val U.val F) :
    ∃ B, Baire_d I ω B ∧
    ∀ i r (w : Fin 26 → M.Domain), Rd_entry_d i r F → Rt_tuple_d w r →
      ∃ data : Ab_product_data_d I ω w,
      let N := smdl_structure_l I (R := w 2) data.model.1.2.1
      let hN := ZFC.models_zf_l (data.theory.native_l I hZF hw)
      ∀ x : Fin n → M.Domain,
        Fp_truth_d hN (Subtype.val : N.Domain → M.Domain)
          ⟨ω,data.inside.1⟩ ⟨w 4,data.inside.2.1⟩ ⟨w 5,data.inside.2.2.1⟩
          ⟨w 6,data.inside.2.2.2.1⟩ ⟨w 8,data.inside.2.2.2.2.2.1⟩ (fun p => M.mem p.val (w 11)) φ x →
        ∃ b : (Relative.lr_model_l hZF).Domain, b.val = B ∧
        ∃ y : Fin n → (Relative.lr_model_l hZF).Domain,
          (∀ k, (y k).val = x k) ∧ Sr_truth_d b φ y := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,upload⟩ :=
    run.finish_l hZF test.model test.transitive (ω := ⟨ω,hω⟩) hw
  obtain ⟨B,reals,all⟩ := upload
  obtain ⟨C,bc,space⟩ := test.real_image_l hZF hw hω B.property reals
  refine ⟨C,space,?_⟩
  intro i r w ir wr
  obtain ⟨data,all⟩ := all i r w ir wr
  refine ⟨data,?_⟩
  dsimp only
  intro x accepted
  obtain ⟨y,values,sat⟩ := all φ hc x accepted
  let N := smdl_structure_l I (R := R) test.model.1.2.1
  let ρ : Env N (n+1) := ⟨Fin.cases B y,fun _ => B⟩
  have params : ∀ k, N.mem (y k) B := (st_params_sat_l ρ .newest (fun k => .bound k.succ)).mp sat.1
  have images : ∀ k, Rd_entry_d (ρ.bound k).val (Fin.cases C x k) π := by
    refine Fin.cases bc (fun k => ?_)
    have real := ((reals (y k).val).mp ((smem_member_l I test.model.1 test.model.2 (y k) B).mp (params k))).2
    change Rd_entry_d (y k).val (x k) π
    rw [← values k]
    exact test.real_fixed_l hZF hw hω (y k).property real
  exact ab_test_upload_l hZF hc test space x ρ images sat

end Upload
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 保留原前缀的单向真值正确性

保存端点的模型代码与原源相同，条件域由同一个前缀长度唯一确定。
原 G 的投影方程保持该前缀中的接受关系；原名字及其解释直接进入
同一运行的 8.6 与共同层出口，最后得到真实背景 L(ℝ) 中的同一断言。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_prefix_correct_l {c X R cY Y S θ j G : M.Domain} (source : Smem_d I c X R)
    {ω A Q U i n C T : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (hΩ : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R)
    (xt : M.TransitiveSet X) (count : M.CardinalLessOrEqual I X ω.val)
    (target : Smem_d I cY Y S) (rank : V_d I θ Y) (embed : Smap_d I ω.val c cY X Y j)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) ω A)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω A Q U)
    (generic : Gset_d Q.val U.val Q.val X G)
    (hi : (smdl_structure_l I (R := R) source.1.2.1).mem i ω)
    (succ : (smdl_structure_l I (R := R) source.1.2.1).SuccessorOf n i)
    (stage : Fp_prefix_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω A n C T)
    {a} (φ : Formula 1 a) (hc : φ.FreeClosed) (x : Fin a → M.Domain)
    (truth : Fp_truth_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) Subtype.val
      ω A Q U C (fun p => M.mem p.val G) φ x) :
    ∃ B, Baire_d I ω.val B ∧ ∃ b : (Relative.lr_model_l hZF).Domain, b.val = B ∧
      ∃ y : Fin a → (Relative.lr_model_l hZF).Domain, (∀ k, (y k).val = x k) ∧ Sr_truth_d b φ y := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  have native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source xt
  have si := image_successor_l (hEN := hZF.1) Subtype.val inj full native.1 succ
  obtain ⟨m,L,Z,x₀,T₀,α,V,d,W,P,b₀,R₀,π,test,sm,hm,_,hωP,_,_,_,_,_,_,_,
      C₀,Y₀,S₀,B₀,H₀,_,_,_,_,_,_,_,_,J,_,_,run,_,r,_,ir,v,vr,em,ec,eX,eR,eA,eQ,eU,_,projection⟩ :=
    ab_test_run_l hZFC hΩ certificate source xt count target rank embed hw sequence product generic
      ((smem_member_l I source.1 source.2 i ω).mp hi) φ hc x truth.1 (l := 0) Fin.elim0
  have mn := sm.eq hZF.1 si
  obtain ⟨B,space,all⟩ := run.test_truth_l hZF hc test hΩ hωP (cY := C₀) (Y := Y₀) (U := S₀)
  obtain ⟨data,correct⟩ := all i.val r v ir vr
  subst c X R
  let N' := smdl_structure_l I (R := v 2) data.model.1.2.1
  have hN := ZFC.models_zf_l (data.theory.native_l I hZF hΩ)
  let ω' : N'.Domain := ⟨ω.val,data.inside.1⟩
  let A' : N'.Domain := ⟨v 4,data.inside.2.1⟩
  let Q' : N'.Domain := ⟨v 5,data.inside.2.2.1⟩
  let U' : N'.Domain := ⟨v 6,data.inside.2.2.2.1⟩
  let n' : N'.Domain := ⟨v 7,data.inside.2.2.2.2.1⟩
  let C' : N'.Domain := ⟨v 8,data.inside.2.2.2.2.2.1⟩
  let T' : N'.Domain := ⟨v 9,data.inside.2.2.2.2.2.2⟩
  have ew : ω' = ω := Subtype.ext rfl
  have ea : A' = A := Subtype.ext eA
  have eq : Q' = Q := Subtype.ext eQ
  have eu : U' = U := Subtype.ext eU
  have en : n' = n := Subtype.ext (em.trans mn)
  obtain ⟨_,_,_,prefixStage⟩ := (ab_kernel_read_l I data.model data.transitive hN ω' A' Q' U' n' C' T').mp data.kernel
  have stage' : Fp_prefix_d native ω A n C' T' := by simpa only [ew,ea,eq,eu,en] using! prefixStage
  have eC : C' = C := native.1.eq_of_same_members C' C (fun p => (stage'.conditions p).trans (stage.conditions p).symm)
  have project : Fp_filter_project_d C.val U.val G (v 11) := by
    have val : v 8 = C.val := congrArg Subtype.val eC
    simpa only [val] using! projection
  obtain ⟨sub,g⟩ := (source.generic_code_l I hZF.1 xt (ZF.modelsKP native) Q U Q G).mp generic
  have hn : N.mem n ω := by
    obtain ⟨n₀,s₀,hn₀⟩ := hw.1.2 i hi
    exact s₀.eq native.1 succ ▸ hn₀
  have read := Smem_d.project_filter_read_l hZF source xt native product stage hn sub project
  have accepts p (hp : N.mem p C) : M.mem p.val G ↔ M.mem p.val (v 11) := by
    constructor
    · intro gp
      exact (read p).mpr ⟨hp,p,gp,Fp_le_d.refl_l (kp_pair_l (ZF.modelsKP native)) p⟩
    · intro gp
      obtain ⟨_,q,gq,qp⟩ := (read p).mp gp
      have hq := (g.proper q gq).1
      have pp := ((stage.product_read_l native product hn).1 p).mp hp |>.1
      exact g.upward q p gq pp ((product.order q p).mpr ⟨hq,pp,qp⟩)
  have selected : Fp_truth_d native Subtype.val ω A Q U C (fun p => M.mem p.val (v 11)) φ x := by
    obtain ⟨real,H,gH,frozen,rest⟩ := truth
    exact ⟨real,H,gH,fun p hp => (frozen p hp).trans (accepts p hp),rest⟩
  refine ⟨B,space,correct x ?_⟩
  change Fp_truth_d hN (Subtype.val : N'.Domain → M.Domain) ω' A' Q' U' C'
    (fun p => M.mem p.val (v 11)) φ x
  rw [ew,ea,eq,eu,eC]
  exact selected

/-- 原 8.5：派生模型中的有限实数参数 Σ₁(ℝ) 断言，在真实背景 L(ℝ) 中成立。
共同正长度前缀、实际测试壳和吸收运行均在证明中构造；源断言采用与
原 8.3 见证语义等价的 Dr_truth_d，完整图读取指定同一背景实数。 -/
theorem ab_lemma85_l {c X R cY Y S θ j G : M.Domain} (source : Smem_d I c X R)
    {ω A Q U : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (hΩ : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R)
    (xt : M.TransitiveSet X) (count : M.CardinalLessOrEqual I X ω.val)
    (target : Smem_d I cY Y S) (rank : V_d I θ Y) (embed : Smap_d I ω.val c cY X Y j)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) ω A)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω A Q U)
    (generic : Gset_d Q.val U.val Q.val X G) :
    let N := smdl_structure_l I (R := R) source.1.2.1
    let hN := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
    let H : N.Domain → Prop := fun p => M.mem p.val G
    let E := extension_l N hN Q U Q H
    ∀ r, Rp_name_d hN ω A Q r → ∀ Z : E.Domain, Qval_d N Q U Q H r Z →
    ∀ k : N.Domain → E.Domain, (∀ a, Gval_d N Q U Q H a (k a)) →
    ∀ {n} (φ : Formula 1 n), φ.FreeClosed → ∀ x : Fin n → M.Domain, ∀ y : Fin n → E.Domain,
      (∀ a, Fn0_d ω.val ω.val (x a)) → (∀ a, Fn_read_d Subtype.val k (y a) (x a)) →
      Relative.Dr_truth_d Z φ y →
      ∃ B, Baire_d I ω.val B ∧ ∃ b : (Relative.lr_model_l hZF).Domain, b.val = B ∧
        ∃ z : Fin n → (Relative.lr_model_l hZF).Domain, (∀ a, (z a).val = x a) ∧ Sr_truth_d b φ z := by
  dsimp only
  intro r name Z value k ground n φ hc x y real read truth
  let N := smdl_structure_l I (R := R) source.1.2.1
  have native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
  obtain ⟨W,range⟩ := ZF.exists_range_of_setFunction native (kp_pair_l (ZF.modelsKP native))
    sequence.function sequence.domain
  have fa : N.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP native)) A ω W :=
    ⟨sequence.function,sequence.domain,fun i hi => ((sequence.domain i).mp hi).elim fun δ edge =>
      ⟨δ,(range δ).mpr ⟨i,edge⟩,edge⟩⟩
  have g := ((source.generic_code_l I hZF.1 xt (ZF.modelsKP native) Q U Q G).mp generic).2
  obtain ⟨i,m,C,T,hi,succ,_,stage,finite⟩ := name.truth_prefix_l native Subtype.val hw fa product g
    value k ground real read truth
  exact ab_prefix_correct_l hZFC source hΩ certificate xt count target rank embed hw sequence product generic
    hi succ stage φ hc x finite

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 正负根力迫沿原 8.5 上传同一个查询点

原名字的商值仍由第一坐标 x 完整读取。二值码及规范自然数图从同一泛型
扩张实际恢复为背景图，再对这四个实数参数调用原 8.5。解码仍指向原 x。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_signed_query_l {c X R cY Y S θ π G x : M.Domain} (source : Smem_d I c X R)
    {ω A Q U : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (hΩ : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R)
    (xt : M.TransitiveSet X) (count : M.CardinalLessOrEqual I X ω.val)
    (target : Smem_d I cY Y S) (rank : V_d I θ Y) (embed : Smap_d I ω.val c cY X Y π)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) ω A)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hΩ)) ω A Q U)
    (generic : Gset_d Q.val U.val Q.val X G) (fx : Fn0_d ω.val ω.val x) :
    let N := smdl_structure_l I (R := R) source.1.2.1
    let hN := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
    let H : N.Domain → Prop := fun p => M.mem p.val G
    ∀ {φ : Formula 1 4}, φ.FreeClosed → ∀ sign a r τ b p,
      Rp_name_d hN ω A Q r → H b → H p → Qs_force_d φ sign Q U r ω a τ b p →
      Fn_value_d hN Subtype.val Q U Q ω τ H x →
      Relative.Lq_signed_d hZF φ sign ω.val a.val x := by
  dsimp only
  intro φ hc sign a r τ b p name hb hp force named
  let N := smdl_structure_l I (R := R) source.1.2.1
  have native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
  let H : N.Domain → Prop := fun p => M.mem p.val G
  let E := extension_l N native Q U Q H
  have O := product.order_l native
  have g := ((source.generic_code_l I hZF.1 xt (ZF.modelsKP native) Q U Q G).mp generic).2
  have hE := preserves_zf_l O native g
  obtain ⟨j,y,τy,ground,_,read⟩ := named
  obtain ⟨Z,rZ⟩ := name_value_l (R := U) (z := Q) (U := H) name.name
  obtain ⟨z,c₁,s₁,code₁,basis,binaryA,binary,decoded,truth⟩ :=
    (qs_truth_l native O g hc sign hb j ground rZ τy).mp ⟨p,hp,force⟩
  obtain ⟨j₀,checks,jfull,ji⟩ := check_map_l O native g hb
  have ej : j₀ = j := funext fun t => (gval_check_map_l O native g hb j₀ checks t (j t)).mp (ground t)
  subst j₀
  have ni : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have nfull := smem_full_l I source xt
  have ba : Bc_binary_d ω a := (bc_binary_image_l j ji jfull native.1 hE.1).mpr binaryA
  have baM : Bc_binary_d ω.val a.val := (bc_binary_image_l Subtype.val ni nfull native.1 hZF.1).mp ba
  have readA := function_read_ground_l (ZF.modelsKP native) hZF.1 hE.1 Subtype.val ni nfull j ji jfull
    (fn0_function_l (ZF.modelsKP native) ba.1).1.1
  obtain ⟨j₁,ground₁,values⟩ := real_values_background_l hZF source xt native (ω := ω) O generic
  have ej₁ : j₁ = j := funext fun t => (ground₁ t).unique_l O native g (ground t)
  subst j₁
  obtain ⟨c₀,fc,_,rc⟩ := values c₁ basis.constant
  obtain ⟨s₀,fs,_,rs⟩ := values s₁ basis.successor
  obtain ⟨code,fb,_,rb⟩ := values code₁ binary.1
  obtain ⟨z₀,natural⟩ := natural_basis_read_l (ZF.modelsKP native) hZF.1 hE.1 Subtype.val ni nfull j ji jfull
    hw hΩ basis fc fs rc rs
  obtain ⟨bits,decode⟩ := rb.binary_decode_l native hZF hE Subtype.val ni nfull j ji jfull
    (hw.isOrdinal (ZF.modelsKP native)) fb fx read binary decoded
  let v : Fin 4 → M.Domain := fun i => [c₀,s₀,a.val,code].get i
  let w : Fin 4 → E.Domain := fun i => [c₁,s₁,j a,code₁].get i
  have reals : ∀ i, Fn0_d ω.val ω.val (v i) := Fin.cases fc (Fin.cases fs (Fin.cases baM.1 (Fin.cases fb (fun i => Fin.elim0 i))))
  have reads : ∀ i, Fn_read_d (M := M) Subtype.val j (w i) (v i) :=
    Fin.cases rc (Fin.cases rs (Fin.cases readA (Fin.cases rb (fun i => Fin.elim0 i))))
  obtain ⟨B,space,b₀,eb,v₀,images,uploaded⟩ := ab_lemma85_l hZFC source hΩ certificate xt count target rank embed hw
    sequence product generic r name Z rZ j ground (Relative.jp_signed_m φ sign) (Relative.jp_signed_closed_l hc sign) v w reals reads truth
  exact ⟨B,space,z₀,c₀,s₀,code,natural,baM,bits,decode,b₀,eb,v₀,images,uploaded⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 分支坍塌源的原乘积资料及同一固定参数上传

Woodin 序列、全乘积和规范实数并名字由返回初等图反射。
该图逐点固定内部自然数，因此旧实数参数的关系原像就是原图。
原秩层作为 8.5 的实际返回目标，给出真实 L(ℝ) 中关于同一 a、x 的见证。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem gh_query_upload_l {φ : Formula 1 4} (hc : φ.FreeClosed) {sign : Bool}
    {c X R θ N d H B π j cB RB P' V' G x : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X) (rank : V_d I θ X)
    (ω A P V σ a₀ : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (hw : M.IsOmega ω.val) (certificate : Zc_model_d I ω.val c X R)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) ω A)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A P V)
    (name : Rp_name_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A P σ)
    (fa : Fn0_d ω.val ω.val a₀.val) (fx : Fn0_d ω.val ω.val x)
    (h : Gh_collapse_d hZF ω.val c X N d P.val V.val H B π j cB RB P' V' G)
    (hwB : M.mem ω.val B) (A' σ' a' τ' b' p' : (smdl_structure_l I (R := RB) h.model.1.2.1).Domain)
    (imageA : Rd_entry_d A.val A'.val π) (imageσ : Rd_entry_d σ.val σ'.val π) (imagea : Rd_entry_d a₀.val a'.val π)
    (hb : M.mem b'.val G) (hp : M.mem p'.val G)
    (force : Qs_force_d (M := smdl_structure_l I (R := RB) h.model.1.2.1) φ sign
      ⟨P',(h.collapse.function.bound_l h.conditions).2⟩ ⟨V',(h.collapse.function.bound_l h.order).2⟩
      σ' ⟨ω.val,hwB⟩ a' τ' b' p')
    (named : Fn_value_d (ZFC.models_zf_l (h.theory.native_l I hZF hw)) Subtype.val
      ⟨P',(h.collapse.function.bound_l h.conditions).2⟩ ⟨V',(h.collapse.function.bound_l h.order).2⟩
      ⟨P',(h.collapse.function.bound_l h.conditions).2⟩ ⟨ω.val,hwB⟩ τ' (fun p => M.mem p.val G) x) :
    Relative.Lq_signed_d hZF φ sign ω.val a₀.val x := by
  let L := smdl_structure_l I (R := R) source.1.2.1
  let C := smdl_structure_l I (R := RB) h.model.1.2.1
  have native := ZFC.models_zf_l (certificate.native_l I hZF hw)
  have small := ZFC.models_zf_l (h.theory.native_l I hZF hw)
  let Ω : C.Domain := ⟨ω.val,hwB⟩
  let P₁ : C.Domain := ⟨P',(h.collapse.function.bound_l h.conditions).2⟩
  let V₁ : C.Domain := ⟨V',(h.collapse.function.bound_l h.order).2⟩
  obtain ⟨_,omega,_,_⟩ := h.numbers_l hZF hw source trans
  have hΩ : C.IsOmega Ω := omega
  obtain ⟨g,elem,values⟩ := h.embedding.project_l I hZF hw h.model.1 source.1
  have point (z : C.Domain) (y : M.Domain) (yz : Rd_entry_d y z.val π) : (g z).val = y :=
    h.embedding.1.1.1.2 _ _ _ (values z) ((h.inverse_entries y z.val).mpr yz)
  have gP : g P₁ = P := Subtype.ext (point P₁ P.val h.conditions)
  have gV : g V₁ = V := Subtype.ext (point V₁ V.val h.order)
  have gA : g A' = A := Subtype.ext (point A' A.val imageA)
  have gσ : g σ' = σ := Subtype.ext (point σ' σ.val imageσ)
  have fixedω := h.embedding.omega_l I hZF hw h.transitive trans h.model source hwB
  have fixed n (hn : M.mem n ω.val) := h.embedding.natural_l hZF hw h.transitive trans h.model source hwB n hn
  have gΩ : g Ω = ω := Subtype.ext (h.embedding.1.1.1.2 _ _ _ (values Ω) fixedω)
  let ψ : Formula 1 5 := .conj (wd_sequence_m (.bound 0) (.bound 1))
    (.conj (fp_product_m (.bound 0) (.bound 1) (.bound 2) (.bound 3)) (rp_name_m (.bound 0) (.bound 1) (.bound 2) (.bound 4)))
  let ρ : Env C 5 := ⟨fun i => [Ω,A',P₁,V₁,σ'].get i,fun _ => σ'⟩
  have old : Formula.satisfies (image_env_l g ρ) ψ := by
    simp only [ψ,Formula.satisfies_conj_iff,wd_sequence_sat_l (kp_pair_l (ZF.modelsKP native)) native.1,
      fp_product_sat_l native,rp_name_sat_l native]
    change Wd_sequence_d (kp_pair_l (ZF.modelsKP native)) (g Ω) (g A') ∧
      Fp_product_d native (g Ω) (g A') (g P₁) (g V₁) ∧ Rp_name_d native (g Ω) (g A') (g P₁) (g σ')
    simpa only [gΩ,gA,gP,gV,gσ] using And.intro sequence (And.intro product name)
  have pulled := (elem ψ (by simp -implicitDefEqProofs [ψ,Definitional.Formula.FreeClosed]) ρ).mpr old
  have data : Wd_sequence_d (kp_pair_l (ZF.modelsKP small)) Ω A' ∧ Fp_product_d small Ω A' P₁ V₁ ∧ Rp_name_d small Ω A' P₁ σ' := by
    exact ⟨(wd_sequence_sat_l (kp_pair_l (ZF.modelsKP small)) small.1 ρ (.bound 0) (.bound 1)).mp pulled.1,
      (fp_product_sat_l small ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3)).mp pulled.2.1,
      (rp_name_sat_l small ρ (.bound 0) (.bound 1) (.bound 2) (.bound 4)).mp pulled.2.2⟩
  have same : a'.val = a₀.val := h.embedding.relation_preimage_l hZF hw h.transitive trans h.model source fixedω fixed
    ((h.inverse_entries a₀.val a'.val).mpr imagea) ⟨(fn0_function_l (ZF.modelsKP hZF) fa).1.1,fun _ _ edge => fa.bound_l edge⟩
  obtain ⟨Z,space,z,c₀,s₀,code,natural,binarya,binary,decode,b₀,eb,v,images,truth⟩ :=
    ab_signed_query_l hZFC h.model hw h.theory h.transitive h.countable source rank h.embedding hΩ
    data.1 data.2.1 h.generic fx hc sign a' σ' τ' b' p' data.2.2 hb hp force named
  exact ⟨Z,space,z,c₀,s₀,code,natural,same ▸ binarya,binary,decode,b₀,eb,v,
    fun i => (images i).trans (congrArg (fun a : M.Domain => ([c₀,s₀,a,code] : List M.Domain).get i) same),truth⟩

end YesMetaZFC.SetTheory.LargeCardinal
