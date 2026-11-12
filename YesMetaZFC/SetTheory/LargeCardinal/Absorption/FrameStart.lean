import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Pending
import YesMetaZFC.Model.Forcing.Collapse.ProductReflection
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Target

/-! # 空滤子列上的实际初始吸收

构造全乘积、空前缀及长度一的全空任务。零字母表坍缩的整个条件域
就是背景小泛型；原 7.23 工厂从这个集合吸收指定实数，供统一待完成任务接口使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ag_absorb_start_l {Ω c X R cY Y S θ π : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d I Ω c X R) (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X Ω)
    (targetRank : V_d I θ Y) (target : Smem_d I cY Y S) (embed : Smap_d I Ω c cY X Y π)
    {ω o δ B Z A W : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) certificate.model.2.1).IsOmega ω)
    (empty : ∀ x, ¬ (smdl_structure_l I (R := R) certificate.model.2.1).mem x o)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ Z)
    (letters : (smdl_structure_l I (R := R) certificate.model.2.1).mem B Z)
    (inh : ∃ x, (smdl_structure_l I (R := R) certificate.model.2.1).mem x B)
    (fa : (smdl_structure_l I (R := R) certificate.model.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) A ω W)
    (first : Entry_d (smdl_structure_l I (R := R) certificate.model.2.1) o δ A) :
    let N := smdl_structure_l I (R := R) certificate.model.2.1
    let hN := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
    let J := kp_pair_l (ZF.modelsKP hN)
    ∃ P U C T m d : N.Domain,
      Fp_product_d hN ω A P U ∧ Fp_prefix_d hN ω A o C T ∧ N.mem o ω ∧
      M.IsSequenceOfLength I o.val o.val ∧
      N.SuccessorOf m o ∧ N.mem m ω ∧ Fp_at_d J ω A m d ∧
      Dense_set_d N P U P P ∧ N.mem d P ∧ Fp_ready_d I o.val o.val d.val ∧
      Entry_d N o δ A ∧
      let H₀ := fun q : N.Domain => N.mem q C ∧ Fp_ready_d I o.val o.val q.val
      Generic_d N C T C H₀ ∧
      ∃ p : Ag_forcing_d hN ω o δ B, ∃ s : Ag_system_d hN p,
      ∃ Γ : N.Domain, ∃ z : M.Domain,
        H₀ o ∧ Dmap_at_d p.Q p.T p.Q C T C Γ o ∧
        (∀ q : N.Domain, M.mem q.val p.Q.val ↔ Pull_generic_d N Γ H₀ q) ∧
        Generic_d N p.Q p.T p.Q (fun q => M.mem q.val p.Q.val) ∧
        Miso_over_d (extension_l N hN p.Q p.T p.Q (fun q => M.mem q.val p.Q.val)) (extension_l N hN C T C H₀)
          (Gval_d N p.Q p.T p.Q (fun q => M.mem q.val p.Q.val)) (Gval_d N C T C H₀) ∧
        (∀ a, ¬ M.mem a z) ∧
        ∀ x, Fn0_d Ω B.val x → ∃ f,
          Ag_trace_d hZF Ω B.val s.A.val s.F₀.val s.R₀.val f x p.Q.val ∧
          Ag_return_d hZF Ω z c X cY Y π (fun i => (s.aux_params_l hN i).val) f p.Q.val x := by
  let N := smdl_structure_l I (R := R) certificate.model.2.1
  have hN := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
  let J := kp_pair_l (ZF.modelsKP hN)
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source xt
  have ambientEmpty a : ¬ M.mem a o.val := fun h => (full o a).mp h |>.elim fun b hb => empty b hb.1
  have member {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b :=
    image_member_l (M := N) (N := M) Subtype.val inj full
  obtain ⟨P,U,o₀,C,T,product,empty₀,ho₀,_,stage,generic⟩ := fp_start_l hN hw fa
  have eq : o₀ = o := hN.1.eq_of_same_members o₀ o (fun x => iff_of_false (empty₀ x) (empty x))
  subst o₀
  have ready d : Fp_ready_d I o.val o.val d := fun i _ hi _ => (ambientEmpty i hi).elim
  let H₀ := fun q : N.Domain => N.mem q C ∧ Fp_ready_d I o.val o.val q.val
  have predicate : (fun q : N.Domain => N.mem q C ∧ Fp_ready_d J o o q) = H₀ := by
    funext q
    apply propext
    exact and_congr_right fun _ => ⟨fun _ => ready q.val,fun _ i _ hi _ => (empty i hi).elim⟩
  have generic₀ : Generic_d N C T C H₀ := predicate ▸ generic
  obtain ⟨m,succ,hm⟩ := hw.1.2 o ho₀
  obtain ⟨C₁,T₁,next⟩ := product.prefix_l hN hm
  obtain ⟨d,hd,_⟩ := next.top_l hN hw hm fa
  have fd := (next.conditions d).mp hd
  have dP := (product.conditions d).mpr ⟨m,hm,fd⟩
  have dense : Dense_set_d N P U P P :=
    ⟨fun q hq => ⟨hq,fun eq => KP.mem_irrefl_d (ZF.modelsKP hN) P (eq ▸ hq)⟩,
      fun q hq nz => ⟨q,below_refl_l (product.order_l hN) hq nz,hq⟩⟩
  have wd := woodin
  obtain ⟨ω₀,_,hw₀,above,_,strong,_,_⟩ := woodin
  have eqω : ω₀ = ω := hN.1.eq_of_same_members ω₀ ω (fun i => ⟨hw₀.2 ω hw.1 i,hw.2 ω₀ hw₀.1 i⟩)
  have small : N.mem o δ := strong.1.1.transitive ω (eqω ▸ above) o ho₀
  obtain ⟨p,s,z,emptyZ,absorb⟩ := ag_absorb_l hZFC hΩ certificate source xt count targetRank target embed
    hw wd rank letters inh small
  obtain ⟨Γ,accepted,map,read,genericQ,comparison⟩ := stage.zero_comparison_l hN hw empty p.small_space p.small_order generic₀
  have same : (fun q : N.Domain => N.mem q p.Q) = (fun q => M.mem q.val p.Q.val) :=
    funext fun q => propext member.symm
  have smallQ : Generic_d N p.Q p.T p.Q (fun q => M.mem q.val p.Q.val) := same ▸ genericQ
  exact ⟨P,U,C,T,m,d,product,stage,ho₀,Structure.IsSequenceOfLength.empty I ambientEmpty,succ,hm,fd,dense,dP,ready d.val,first,
    generic₀,p,s,Γ,z,accepted,map,fun q => member.trans (read q).symm,smallQ,same ▸ comparison,emptyZ,
    fun x fx => absorb p.Q.val x (fun _ h => h) smallQ fx⟩

/-- 首次吸收实际完成一个坐标，并返回下一轮所需的模型、返回因子和背景泛型集合。 -/
theorem ag_absorb_first_l {Ω c X R cY Y S θ π x : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d I Ω c X R) (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X Ω)
    (targetRank : V_d I θ Y) (target : Smem_d I cY Y S) (embed : Smap_d I Ω c cY X Y π)
    {ω o δ B Z A W : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) certificate.model.2.1).IsOmega ω)
    (empty : ∀ a, ¬ (smdl_structure_l I (R := R) certificate.model.2.1).mem a o)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) δ Z)
    (letters : (smdl_structure_l I (R := R) certificate.model.2.1).mem B Z)
    (inh : ∃ a, (smdl_structure_l I (R := R) certificate.model.2.1).mem a B)
    (fa : (smdl_structure_l I (R := R) certificate.model.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) A ω W)
    (first : Entry_d (smdl_structure_l I (R := R) certificate.model.2.1) o δ A)
    (fx : Fn0_d Ω B.val x) :
    let N := smdl_structure_l I (R := R) certificate.model.2.1
    ∃ c' X' R' j σ : M.Domain, ∃ model : Smem_d I c' X' R', ∃ cert : Zc_model_d I Ω c' X' R',
      M.TransitiveSet X' ∧ M.CardinalLessOrEqual I X' Ω ∧
      Smap_d I Ω c c' X X' j ∧ Smap_d I Ω c' cY X' Y σ ∧ It_comp_d j σ π ∧
      let N' := smdl_structure_l I (R := R') model.1.2.1
      let hN' := ZFC.models_zf_l (cert.native_l I hZF hΩ)
      ∃ e : N.Domain → N'.Domain, Pe_d e ∧ (∀ a, Rd_entry_d a.val (e a).val j) ∧
        (e ω).val = Ω ∧ (e o).val = o.val ∧
        ∃ P U n C T : N'.Domain, ∃ F H : M.Domain,
          Fp_product_d hN' (e ω) (e A) P U ∧ N'.SuccessorOf n (e o) ∧ N'.mem n (e ω) ∧
          M.IsSequenceOfLength I F n.val ∧
          Fp_prefix_d hN' (e ω) (e A) n C T ∧ M.MemberSubset H C.val ∧
          (∀ t, M.mem t H ↔ M.mem t C.val ∧ Fp_ready_d I n.val F t) ∧
          Generic_d N' C T C (fun q => M.mem q.val H) ∧
          Gset_d C.val T.val C.val X' H ∧
          let E := extension_l N' hN' C T C (fun q => M.mem q.val H)
          ∃ k : N'.Domain → E.Domain, Function.Injective k ∧
            (∀ a, Gval_d N' C T C (fun q => M.mem q.val H) a (k a)) ∧
            ∃ B' y, Fn_bg_d X' C.val T.val C.val (e ω).val B'.val H x ∧
              Fn0_d (k (e ω)) (k B') y ∧ Fn_read_d Subtype.val k y x ∧
              ∀ g, M.IsSetRelation I g → (Fn_read_d Subtype.val k y g ↔ g = x) := by
  have native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
  obtain ⟨P,U,C,T,m,d,product,stage,ho,seq,succ,hm,fd,dense,hit,ready,_,generic,p,s,Γ,z,accepted,map,read,_,_,_,absorb⟩ :=
    ag_absorb_start_l hZFC hΩ certificate source xt count targetRank target embed hw empty woodin rank letters inh fa first
  obtain ⟨f,_,returned⟩ := absorb x fx
  have move := returned.pending_l hZF hΩ source xt certificate native s hw inh fa product stage ho hm succ.predecessor_mem fd dense hit first
      (fun i _ hi _ => (empty i hi).elim) generic accepted map (fun _ h => h) read seq ready
  rcases move with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,r,σ,returnMap,square,count',cert,move⟩
  rcases move with ⟨e,elem,values,eo,_,product',_,_,_,move⟩
  rcases move with ⟨n,C',T',F',K,H',succ',hn,_,seq',_,_,_,_,stage',sub,members,generic',genericCode,_,move⟩
  rcases move with ⟨k,ki,ground,B',y,code,fn,read',unique⟩
  have ew : e ω = r.w 0 := Subtype.ext (r.map.1.1.1.2 _ _ _ (values ω) (r.images 0))
  refine ⟨r.d,r.N,r.W,r.j,σ,r.target,cert,r.transitive,count',r.map,returnMap,square,
    e,elem,values,(congrArg Subtype.val ew).trans r.omega,eo,e P,e U,n,C',T',F',H',
    ew.symm ▸ product',succ',ew.symm ▸ hn,seq',ew.symm ▸ stage',sub,members,generic',genericCode,k,ki,ground,B',y,ew.symm ▸ code,?_,read',unique⟩
  exact ew.symm ▸ fn

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 由实际 Woodin 序列构造第一个吸收帧

序列的首项自动提供 7.23 的 Woodin、秩层和实数字母表参数。
真实首轮输出编码为十四项集合记录，保存返回因子和首个已吸收实数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ab_frame_first_l {Ω c X R cY Y S θ π x : M.Domain} (hΩ : M.IsOmega Ω)
    (certificate : Zc_model_d I Ω c X R) (source : Smem_d I c X R) (xt : M.TransitiveSet X)
    (count : M.CardinalLessOrEqual I X Ω)
    (targetRank : V_d I θ Y) (target : Smem_d I cY Y S) (embed : Smap_d I Ω c cY X Y π)
    {ω A : (smdl_structure_l I (R := R) certificate.model.2.1).Domain}
    (hw : (smdl_structure_l I (R := R) certificate.model.2.1).IsOmega ω)
    (sequence : Wd_sequence_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hΩ)))) ω A)
    (fx : Fn0_d Ω Ω x) :
    ∃ o r : M.Domain, ∃ v : Fin 14 → M.Domain, ∃ j,
      (∀ a, ¬ M.mem a o) ∧ Rt_tuple_d v r ∧ Ab_frame_d I Ω cY Y v ∧
      M.SuccessorOf (v 7) o ∧ v 13 = x ∧
      Smap_d I Ω c (v 0) X (v 1) j ∧ It_comp_d j (v 3) π ∧ Rd_entry_d A.val (v 4) j := by
  let N := smdl_structure_l I (R := R) certificate.model.2.1
  have native := ZFC.models_zf_l (certificate.native_l I hZF hΩ)
  let J := kp_pair_l (ZF.modelsKP native)
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source xt
  have hw₀ := image_omega_l (hEN := hZF.1) Subtype.val inj full native
    (fun _ ne => KP.mem_minimal_exists_d (ZF.modelsKP hZF) ne) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hZF) D ω.val)
  have eqω : ω.val = Ω := hZF.1.eq_of_same_members ω.val Ω
    (fun i => ⟨hw₀.2 Ω hΩ.1 i,hΩ.2 ω.val hw₀.1 i⟩)
  obtain ⟨o,empty,ho⟩ := hw.1.1
  obtain ⟨δ,first⟩ := (sequence.domain o).mp ho
  have wd := sequence.woodin o δ first
  obtain ⟨ω₀,Z,hw',above,_,_,rank,_⟩ := wd
  have ew := native.1.eq_of_same_members ω₀ ω (fun i => ⟨hw'.2 ω hw.1 i,hw.2 ω₀ hw'.1 i⟩)
  have letters := ZF.v_ordinal_mem_l J native rank (ew ▸ above)
  obtain ⟨W,range⟩ := ZF.exists_range_of_setFunction native J sequence.function sequence.domain
  have fa : N.IsSetFunctionFromTo J A ω W := ⟨sequence.function,sequence.domain,fun i hi => by
    obtain ⟨δ,edge⟩ := (sequence.domain i).mp hi
    exact ⟨δ,(range δ).mpr ⟨i,edge⟩,edge⟩⟩
  have fx' : Fn0_d Ω ω.val x := by rw [eqω]; exact fx
  obtain ⟨c',X',R',j,σ,model,cert,trans,count',emb,ret,square,e,elem,values,omega,eo,
      P,U,n,C,T,F,H,product,succ,hn,seq,stage,_,members,_,generic,_,_,_,B',_,name,_,_,_⟩ :=
    ag_absorb_first_l hZFC hΩ certificate source xt count targetRank target embed hw empty
      (sequence.woodin o δ first) rank letters ⟨o,ho⟩ fa first fx'
  let N' := smdl_structure_l I (R := R') model.1.2.1
  have native' := ZFC.models_zf_l (cert.native_l I hZF hΩ)
  have hw'' : N'.IsOmega (e ω) := by
    let ρ : Env N 1 := ⟨fun _ => ω,fun _ => ω⟩
    exact (Formula.satisfies_isOmega_iff (image_env_l e ρ) .newest).mp
      ((elem (Formula.isOmega .newest) (by simp -implicitDefEqProofs) ρ).mp
        ((Formula.satisfies_isOmega_iff ρ .newest).mpr hw))
  have sequence' := sequence.image_l J (kp_pair_l (ZF.modelsKP native')) native.1 native'.1 e elem
  have kernel := (ab_kernel_read_l I model trans native' (e ω) (e A) P U n C T).mpr
    ⟨hw'',sequence',product,stage⟩
  have ambientEmpty a : ¬ M.mem a o.val := fun h => (full o a).mp h |>.elim fun b hb => empty b hb.1
  let v : Fin 14 → M.Domain := fun i => [c',X',R',σ,(e A).val,P.val,U.val,n.val,C.val,T.val,F,H,B'.val,x].get i
  have frame : Ab_frame_d I Ω cY Y v :=
    ⟨model,cert,trans,count',ret,⟨omega ▸ (e ω).property,(e A).property,P.property,U.property,n.property,C.property,T.property,B'.property⟩,
      omega ▸ ((model.2 n.val (e ω).val).mp hn).2.2,omega ▸ kernel,seq.2.1,seq.2.2,members,generic,fx,omega ▸ name⟩
  have inj' : Function.Injective (Subtype.val : N'.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full' := smem_full_l I model trans
  have successor := image_successor_l (hEN := hZF.1) Subtype.val inj' full' native'.1 succ
  obtain ⟨r,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) v
  exact ⟨o.val,r,v,j,ambientEmpty,tuple,frame,eo ▸ successor,rfl,emb,square,values A⟩

end YesMetaZFC.SetTheory.LargeCardinal
