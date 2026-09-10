import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedTarski

/-! # 原支撑理论中逐参数赋值的真不可定义性

候选公式有一个编码槽及任意有限参数列。真值合同覆盖使用同一参数列的全部开放公式；
实际反例在每个赋值下失败，不要求参数由闭项命名，也不要求模型标准。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedTarski.Parameters
open Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
universe x
variable {parameters : SetContext}

def predicate_m (P : ObjectDiagonal.ParameterFormula_m parameters)
    (φ : SetOpenFormula parameters) : SetOpenFormula parameters :=
  P.instantiateFreeTop (ObjectParameterDiagonal.quote_m φ)

def liarFormula_m (P : ObjectDiagonal.ParameterFormula_m parameters) : SetOpenFormula parameters :=
  ObjectTarski.Parameters.liarFormula_m intrinsic_zfc_core.code_domain P

theorem liar_fixed_point_m (P : ObjectDiagonal.ParameterFormula_m parameters) :
    Derives intrinsic_zfc_theory [] (liarFormula_m P ↔ₘ ¬ₘ predicate_m P (liarFormula_m P)) :=
  ObjectTarski.Parameters.liar_fixed_point_m ReducedRosser.diagonalSupport P

theorem liar_refutes_m (P : ObjectDiagonal.ParameterFormula_m parameters) :
    Derives intrinsic_zfc_theory [] (¬ₘ (predicate_m P (liarFormula_m P) ↔ₘ liarFormula_m P)) :=
  Tarski.liar_refutes_m (liar_fixed_point_m P)

/-- 对任意参数赋值的反例，在理论中统一全称闭合。 -/
theorem liar_refutes_closed_m (P : ObjectDiagonal.ParameterFormula_m parameters) :
    Derives intrinsic_zfc_theory [] (Metatheory.Formula.forall_close
      (¬ₘ (predicate_m P (liarFormula_m P) ↔ₘ liarFormula_m P))) :=
  Metatheory.Derives.forall_close_of_derives (liar_refutes_m P)

private theorem consistent_open_m
    (hT : Derives.Consistent intrinsic_zfc_theory ([] : Context signature [])) :
    Derives.Consistent intrinsic_zfc_theory ([] : Context signature parameters) := by
  intro h
  apply hT
  have τ : VariableSubstitution signature parameters [] [] :=
    fun {s} _ => by cases s; exact (numₘ(0) : SetOpenTerm [])
  simpa only [Context.substituteFree, Formula.substituteFree, Formula.substitute,
    Substitution.free_map, Formula.substituteMapped, List.map_nil] using
    Derives.free_substitution τ h

theorem biconditional_unprovable_m (P : ObjectDiagonal.ParameterFormula_m parameters)
    (hT : Derives.Consistent intrinsic_zfc_theory ([] : Context signature [])) :
    ¬ Derives intrinsic_zfc_theory [] (predicate_m P (liarFormula_m P) ↔ₘ liarFormula_m P) :=
  Tarski.biconditional_unprovable_m (liar_fixed_point_m P) (consistent_open_m hT)

theorem undefinable_syntax_m (parameters : SetContext)
    (hT : Derives.Consistent intrinsic_zfc_theory ([] : Context signature [])) :
    ¬ ∃ P : ObjectDiagonal.ParameterFormula_m parameters,
      Tarski.TruthSchema_m intrinsic_zfc_theory (predicate_m P) := by
  rintro ⟨P, h⟩
  exact Tarski.not_truth_schema_m (liar_fixed_point_m P) (consistent_open_m hT) h

/-- 同一个实际反例在每一组参数取值下否定候选真值等价式。 -/
theorem liar_fails_at_m {ℳ : Structure.{0,0,0,x} signature}
    (hℳ : Theory.Models ℳ intrinsic_zfc_theory) (env : Env ℳ [] parameters)
    (P : ObjectDiagonal.ParameterFormula_m parameters) :
    ¬ ((predicate_m P (liarFormula_m P)).satisfies env ↔
      (liarFormula_m P).satisfies env) :=
  (liar_refutes_m P).sound hℳ env (by intro φ h; cases h)

/-- 固定任意参数赋值，均不存在正确判定全部相应开放公式的候选谓词。 -/
theorem undefinable_at_m {ℳ : Structure.{0,0,0,x} signature}
    (hℳ : Theory.Models ℳ intrinsic_zfc_theory) (env : Env ℳ [] parameters) :
    ¬ ∃ P : ObjectDiagonal.ParameterFormula_m parameters,
      Tarski.DefinesSatisfaction_m env (predicate_m P) := by
  rintro ⟨P, h⟩
  exact Tarski.not_defines_satisfaction_m hℳ env (liar_fixed_point_m P) h

/-- 同时排除任意有限参数数目、参数取值及候选公式。 -/
theorem undefinable_parameters_m {ℳ : Structure.{0,0,0,x} signature}
    (hℳ : Theory.Models ℳ intrinsic_zfc_theory) :
    ¬ ∃ (parameters : SetContext) (env : Env ℳ [] parameters)
      (P : ObjectDiagonal.ParameterFormula_m parameters),
      Tarski.DefinesSatisfaction_m env (predicate_m P) := by
  rintro ⟨parameters, env, P, h⟩
  exact undefinable_at_m hℳ env ⟨P, h⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.ReducedTarski.Parameters
