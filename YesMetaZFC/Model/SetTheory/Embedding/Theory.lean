import YesMetaZFC.Model.SetTheory.Internal.Extensionality
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.Model.SetTheory.Relations.CollectCode

/-! # 原关系初等图保持所属结构的实际理论

逐句使用同一个完整初等图，不另加目标模型假设。
此处传输原生理论，不替代覆盖全部内部程序的 Zc_model 证书。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.native_models_l {ω c X R d Y S j : M.Domain} {𝒯 : Theory}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (map : Smap_d I ω c d X Y j) (h : (smdl_structure_l I (R := R) mx.2.1).Models 𝒯) :
    (smdl_structure_l I (R := S) my.2.1).Models 𝒯 := by
  have ext : Rf_ext_d I X R := fun a ha b hb same => congrArg Subtype.val
    (h.1.eq_of_same_members ⟨a, ha⟩ ⟨b, hb⟩ (fun z => same z.val z.property))
  have targetExt : Rf_ext_d I Y S := map.extensional_l hZF hω mx my ext
  refine ⟨targetExt.native_l I my.2.1, fun φ hφ => ?_⟩
  rw [Structure.satisfiesSentence_iff]
  intro f
  obtain ⟨x, hx⟩ := mx.2.1
  let g : FreeVarId → (smdl_structure_l I (R := R) mx.2.1).Domain := fun _ => ⟨x, hx⟩
  exact (smap_source_l I hZF hω mx my map φ.formula φ.freeClosed
    ⟨Fin.elim0, g⟩ ⟨Fin.elim0, f⟩ (fun i => Fin.elim0 i)).mp
      ((Structure.satisfiesSentence_iff _ φ).mp (h.2 φ hφ) g)

end YesMetaZFC.SetTheory.Internal
