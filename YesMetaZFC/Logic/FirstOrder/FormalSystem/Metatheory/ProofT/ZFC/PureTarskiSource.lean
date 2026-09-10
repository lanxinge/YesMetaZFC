import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureOpenTransfer
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedTarskiParameters

/-! # 裸 ZFC 中保留原语法编码的带参数真不可定义性

候选为纯隶属公式；编码对象仍是源支撑语言公式。真值合同覆盖全部源公式的纯翻译，
反例也由同一翻译实际产生。这里不将源反例 quotation 改称纯反例自身的 quotation。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureTarskiSource
open Nonlogical.BasicSetTheory PureOpenTransfer
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature
attribute [local implicit_reducible] RelationalTranslation.Expansion.model
universe x
variable {parameters : SetContext}

abbrev Candidate_m (parameters : SetContext) :=
  OpenFormula ℒ (pureContext_m (SetSort.set :: parameters))

def sourceTemplate_m (P : Candidate_m parameters) : ObjectDiagonal.ParameterFormula_m parameters :=
  PureOpenTransfer.embed_m P

def sourceLiar_m (P : Candidate_m parameters) : SetOpenFormula parameters :=
  ReducedTarski.Parameters.liarFormula_m (sourceTemplate_m P)

noncomputable def liarFormula_m (P : Candidate_m parameters) : OpenFormula ℒ (pureContext_m parameters) :=
  translate_m (sourceLiar_m P)

/-- 候选在原 quotation 处的实例，消去全部支撑符号后的纯公式。 -/
noncomputable def predicate_m (P : Candidate_m parameters) (φ : SetOpenFormula parameters) :
    OpenFormula ℒ (pureContext_m parameters) :=
  translate_m (ReducedTarski.Parameters.predicate_m (sourceTemplate_m P) φ)

/-- 原公式的闭 quotation 在规范扩张中的值，与参数赋值无关。 -/
noncomputable def quotation_m {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) (φ : SetOpenFormula parameters) : PureModel.Carrier ℳ :=
  (IntrinsicQuotation.quote φ).eval (Env.empty : Env (PureCompletedStage.expansion hℳ).model [] [])

private theorem quote_eval_m {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) (env : Env ℳ [] (pureContext_m parameters))
    (φ : SetOpenFormula parameters) :
    (ObjectParameterDiagonal.quote_m φ).eval (sourceEnv_m hℳ env) = quotation_m hℳ φ := by
  simpa only [ObjectParameterDiagonal.quote_m, quotation_m, Term.substitute, Env.empty_unique] using
    Term.eval_substitute (sourceEnv_m hℳ env)
      (Substitution.map VariableSubstitution.boundId VariableSubstitution.empty) (IntrinsicQuotation.quote φ)

/-- 消元后的实例确实应用原纯候选；编码放入首槽，全部参数原样保留。 -/
theorem predicate_satisfies_m {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) (env : Env ℳ [] (pureContext_m parameters))
    (P : Candidate_m parameters) (φ : SetOpenFormula parameters) :
    (predicate_m P φ).satisfies env ↔ P.satisfies (env.pushFree (quotation_m hℳ φ)) := by
  unfold predicate_m ReducedTarski.Parameters.predicate_m sourceTemplate_m
  rw [translate_satisfies_m hℳ, Formula.satisfies_instantiateFreeTop, quote_eval_m,
    ← sourceEnv_push_m]
  exact embed_canonical_m hℳ _ P

theorem liar_fixed_point_m (P : Candidate_m parameters) :
    Derives PureModel.theory [] (.iff (liarFormula_m P) (.neg (predicate_m P (sourceLiar_m P)))) :=
  translate_derives_m (ReducedTarski.Parameters.liar_fixed_point_m (sourceTemplate_m P))

theorem liar_refutes_m (P : Candidate_m parameters) :
    Derives PureModel.theory [] (.neg (.iff (predicate_m P (sourceLiar_m P)) (liarFormula_m P))) :=
  Tarski.liar_refutes_m (liar_fixed_point_m P)

theorem liar_refutes_closed_m (P : Candidate_m parameters) :
    Derives PureModel.theory [] (Metatheory.Formula.forall_close
      (.neg (.iff (predicate_m P (sourceLiar_m P)) (liarFormula_m P)))) :=
  Metatheory.Derives.forall_close_of_derives (liar_refutes_m P)

theorem biconditional_unprovable_m (P : Candidate_m parameters)
    (hT : Derives.Consistent PureModel.theory ([] : Context ℒ [])) :
    ¬ Derives PureModel.theory [] (.iff (predicate_m P (sourceLiar_m P)) (liarFormula_m P)) :=
  Tarski.biconditional_unprovable_m (liar_fixed_point_m P)
    (SemanticTransfer.consistent_open_m PureRosserSchedule.target hT _)

/-- 原公式按自身原编码索引，右侧为其纯隶属翻译。 -/
def TruthSchema_m (P : Candidate_m parameters) : Prop :=
  ∀ φ : SetOpenFormula parameters,
    Derives PureModel.theory [] (.iff (predicate_m P φ) (translate_m φ))

theorem undefinable_syntax_m (parameters : SetContext)
    (hT : Derives.Consistent PureModel.theory ([] : Context ℒ [])) :
    ¬ ∃ P : Candidate_m parameters, TruthSchema_m P := by
  rintro ⟨P, h⟩
  exact biconditional_unprovable_m P hT (h (sourceLiar_m P))

def DefinesSatisfaction_m {ℳ : Structure.{0,0,0,x} ℒ}
    (env : Env ℳ [] (pureContext_m parameters)) (P : Candidate_m parameters) : Prop :=
  ∀ φ : SetOpenFormula parameters, (predicate_m P φ).satisfies env ↔ (translate_m φ).satisfies env

theorem liar_fails_at_m {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ PureModel.theory)
    (env : Env ℳ [] (pureContext_m parameters)) (P : Candidate_m parameters) :
    ¬ ((predicate_m P (sourceLiar_m P)).satisfies env ↔ (liarFormula_m P).satisfies env) :=
  (liar_refutes_m P).sound hℳ env (by intro φ h; cases h)

theorem undefinable_at_m {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ PureModel.theory)
    (env : Env ℳ [] (pureContext_m parameters)) :
    ¬ ∃ P : Candidate_m parameters, DefinesSatisfaction_m env P := by
  rintro ⟨P, h⟩
  exact liar_fails_at_m hℳ env P (h (sourceLiar_m P))

theorem undefinable_parameters_m {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) :
    ¬ ∃ (parameters : SetContext) (env : Env ℳ [] (pureContext_m parameters))
      (P : Candidate_m parameters), DefinesSatisfaction_m env P := by
  rintro ⟨parameters, env, P, h⟩
  exact undefinable_at_m hℳ env ⟨P, h⟩

/-- 直接以原纯候选及规范扩张的源真值表述，不以翻译后的候选替代候选本身。 -/
theorem undefinable_source_at_m {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) (env : Env ℳ [] (pureContext_m parameters)) :
    ¬ ∃ P : Candidate_m parameters, ∀ φ : SetOpenFormula parameters,
      P.satisfies (env.pushFree (quotation_m hℳ φ)) ↔ φ.satisfies (sourceEnv_m hℳ env) := by
  rintro ⟨P, h⟩
  apply undefinable_at_m hℳ env
  exact ⟨P, fun φ => (predicate_satisfies_m hℳ env P φ).trans
    ((h φ).trans (translate_satisfies_m hℳ env φ).symm)⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureTarskiSource
