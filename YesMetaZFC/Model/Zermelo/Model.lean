import YesMetaZFC.Model.Zermelo.Project

/-! # 无附加公理的完整 Z 模型

所有集合运算由具体小分支树给出，全部公理逐句验证。
经典一阶语义使用稳定真值；它不要求把双重否定存在提升为元层正存在。
最终模型和一致性声明没有排中律、选择、外延性或模型存在参数。
-/

namespace YesMetaZFC.Model.Zermelo
open SetTheory SetTheory.Definitional
universe u

/-- 原 Project Z 的七项固定公理和完整分离模式。 -/
theorem project_z (s : Project.Sentence) (hs : SetTheory.Z s) (ρ : PEnv.{u} 0) :
    value s.formula ρ := by
  cases hs with
  | extensionality => exact fun _ _ h => V.ext h
  | emptySet => exact nn_in ⟨V.empty, V.empty_mem⟩
  | pairing => exact fun a b => nn_in ⟨V.pair a b, V.pair_mem a b⟩
  | union => exact fun a => nn_in ⟨V.union a, V.union_mem a⟩
  | powerSet => exact fun a => nn_in ⟨V.power a, V.power_mem a⟩
  | infinity =>
    exact nn_in ⟨V.omega, nn_in ⟨V.empty, V.empty_mem, V.omega_zero⟩,
      fun a h => nn_in ⟨V.succ a, V.succ_mem a, V.omega_succ h⟩⟩
  | foundation => exact V.foundation
  | separation φ => exact closure_valid _ ρ (fun b => separation_core φ ⟨b, ρ.free⟩)

/-- 实际载体及已验证的经典规则满足原纯一阶 Z 理论。 -/
theorem models_z : model.{u}.models (Project.fo_theory SetTheory.Z) := by
  intro φ ⟨s, hs, e⟩ ρ
  cases e
  exact (formula_correct s.formula s.freeClosed ρ
    ⟨Fin.elim0, fun _ => V.empty⟩ (fun i => Fin.elim0 i)).mpr (project_z s hs _)

/-- 原 Hilbert 推导的一致性，直接消费上述非平凡模型。 -/
theorem z_consistent : Logic.FirstOrder.Derives.Consistent
    (Project.fo_theory SetTheory.Z) ([] : Logic.FirstOrder.Context ℒ []) :=
  rules.{0}.consistent_of_models not_false models_z

end YesMetaZFC.Model.Zermelo
