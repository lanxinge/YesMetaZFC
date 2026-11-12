import YesMetaZFC.Model.Forcing.Order.GenericTreeGround
import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.SetTheory.Internal.RealTrace
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.SetTheory.FunctionRetraction

/-! # 原幂集可数证书产生实际地泛型

原条件域到 δ 的单射将全部旧稠密集编码进原 𝒫(δ)。在传递隶属背景中
取得其实际可数枚举，内部 DC 构造滤子，再沿完整地包含映射回读泛型性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原幂集可数时，任一有内部单射到该幂集的非空旧集合都有实际满枚举。 -/
theorem Pc_count_d.enumeration_l {Ω c X R : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    (δ P A : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (power : (smdl_structure_l I (R := R) source.1.2.1).IsPowerSetOf P δ)
    (small : (smdl_structure_l I (R := R) source.1.2.1).CardinalLessOrEqual (kp_pair_l (ZF.modelsKP native)) A P)
    (inh : ∃ a, (smdl_structure_l I (R := R) source.1.2.1).mem a A)
    (count : Pc_count_d I Ω X R δ.val) :
    ∃ e, M.IsSetFunctionFromTo I e Ω A.val ∧ M.IsSetSurjectiveOnto I e Ω A.val := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  obtain ⟨P',B,power',carrier,size⟩ := count.native_l hZF source.1.2.1 δ
  have eq := native.1.eq_of_same_members P' P (fun x => (power' x).trans (power x).symm)
  subst P'
  have members y : M.mem y A.val ↔ M.mem y X ∧ Rd_entry_d y A.val R := by
    refine ⟨fun hy => ?_,fun hy => ((source.2 y A.val).mp hy.2).2.2⟩
    have inside := trans A.val A.property y hy
    exact ⟨inside,(source.2 y A.val).mpr ⟨inside,A.property,hy⟩⟩
  obtain ⟨i,fi⟩ := rr_cardinal_bound_l hZF source.1.2.1 (ZF.modelsKP native) A P members carrier small
  obtain ⟨k,fk⟩ := size
  obtain ⟨a,fa⟩ := ZF.exists_compositionInjection hZF I fi fk
  obtain ⟨v,hv⟩ := inh
  have hv' : M.mem v.val A.val := ((source.2 v.val A.val).mp hv).2.2
  obtain ⟨e,fe,back⟩ := ZF.injection_retract_l I hZF fa (fun _ hx => hx) hv'
  refine ⟨e,fe,fun y hy => ?_⟩
  obtain ⟨n,hn,yn⟩ := fa.1.2.2 y hy
  exact ⟨n,hn,back y n yn⟩

theorem Pc_count_d.generic_l {Ω c X R : M.Domain} (hw : M.IsOmega Ω) (dc : Dc_d I Ω)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    (δ Q T p : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) Q T Q)
    (small : (smdl_structure_l I (R := R) source.1.2.1).CardinalLessOrEqual (kp_pair_l (ZF.modelsKP native)) Q δ)
    (hp : (smdl_structure_l I (R := R) source.1.2.1).mem p Q)
    (count : Pc_count_d I Ω X R δ.val) :
    ∃ H, M.MemberSubset H Q.val ∧ M.mem p.val H ∧
      Generic_d (smdl_structure_l I (R := R) source.1.2.1) Q T Q (fun q => M.mem q.val H) := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let J := kp_pair_l (ZF.modelsKP native)
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  obtain ⟨P,power⟩ := ZF.exists_powerSet native δ
  obtain ⟨D,family⟩ := dense_family_l native Q T Q
  have coding : N.CardinalLessOrEqual J D P := dense_family_bound_l native (fun E => (family E).mp) power small
  have self : N.mem Q D := (family Q).mpr
    ⟨fun q hq => ⟨hq,fun eq => KP.mem_irrefl_d (ZF.modelsKP native) Q (eq ▸ hq)⟩,
      fun q hq ne => ⟨q,below_refl_l O hq ne,hq⟩⟩
  obtain ⟨e,fe,onto⟩ := count.enumeration_l hZF source trans native δ P D power coding ⟨Q,self⟩
  have order := image_cond_order_l (ZF.modelsKP native) hZF.1 Subtype.val inj full O
  have dense : ∀ E, M.mem E D.val → Dense_set_d M Q.val T.val Q.val E := by
    intro E hE
    obtain ⟨E₀,hE₀,eq⟩ := (full D E).mp hE
    subst E
    exact image_global_dense_l native hZF.1 Subtype.val inj full ((family E₀).mp hE₀)
  obtain ⟨H,ph,filter⟩ := countable_filter_l hZF order hw dc dense fe onto ((image_member_l Subtype.val inj full).mpr hp)
  exact ⟨H,fun q hq => (filter.proper q hq).1,ph,
    filter.ground_global_l native hZF.1 Subtype.val inj full O (fun E hE => (family E).mpr hE)⟩

end YesMetaZFC.SetTheory.Internal
