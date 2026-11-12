import YesMetaZFC.Model.Forcing.Order.GenericTreeGround
import YesMetaZFC.Model.SetTheory.Internal.RealTrace
import YesMetaZFC.SetTheory.FunctionRetraction

/-! # 每个可数阶段出生的全部稠密任务都有实际编号

条件序的全部全局稠密集在原模型中分离成集合，再由原模型的背景可数性
构造背景 ω 上的满枚举。编号覆盖整个稠密集族，不限于先前选出的子族。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Smem_d.dense_enumeration_l {ω c X R : M.Domain}
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    (count : M.CardinalLessOrEqual I X ω)
    (P T : (smdl_structure_l I (R := R) source.1.2.1).Domain)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) P T P) :
    ∃ D : (smdl_structure_l I (R := R) source.1.2.1).Domain,
      (∀ E, (smdl_structure_l I (R := R) source.1.2.1).mem E D ↔
        Dense_set_d (smdl_structure_l I (R := R) source.1.2.1) P T P E) ∧
      ∃ e, M.IsSetFunctionFromTo I e ω D.val ∧ M.IsSetSurjectiveOnto I e ω D.val := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  obtain ⟨D,family⟩ := dense_family_l native P T P
  have self : N.mem P D := (family P).mpr
    ⟨fun p hp => ⟨hp,fun eq => KP.mem_irrefl_d (ZF.modelsKP native) P (eq ▸ hp)⟩,
      fun p hp nz => ⟨p,below_refl_l O hp nz,hp⟩⟩
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have inhabited : M.mem P.val D.val := (image_member_l (M := N) (N := M) Subtype.val inj full).mpr self
  obtain ⟨i,fi⟩ := ZF.exists_inclusionInjection hZF I (trans D.val D.property)
  obtain ⟨j,fj⟩ := count
  obtain ⟨k,fk⟩ := ZF.exists_compositionInjection hZF I fi fj
  obtain ⟨e,fe,back⟩ := ZF.injection_retract_l I hZF fk (fun _ hx => hx) inhabited
  refine ⟨D,family,e,fe,fun E hE => ?_⟩
  obtain ⟨n,hn,En⟩ := fk.1.2.2 E hE
  exact ⟨n,hn,back E n En⟩

end YesMetaZFC.SetTheory.Internal
