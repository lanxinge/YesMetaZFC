import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureFixedPoint
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Tarski

/-! # 裸 ZFC 的纯语言自身编码真不可定义定理

候选、反例和合同量化的公式全部属于纯隶属语言；编码是每个纯公式的完整 AST 码。
任意有限参数、任意参数赋值以及非标准模型均包括在内。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureTarski
open Nonlogical.BasicSetTheory PureOpenTransfer PureQuotation PureFixedPoint
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature RelationalTranslation.Expansion.model PureCompletedStage.interpretation
attribute [local irreducible] PureFixedPoint.formula_m PureFixedPoint.predicate_m PureQuotation.number_m PureQuotation.code_m
universe x
variable {parameters : SetContext}

noncomputable def liarFormula_m (P : Candidate_m parameters) : OpenFormula ℒ (pureContext_m parameters) :=
  PureFixedPoint.formula_m (.neg P)

theorem liar_fixed_point_m (P : Candidate_m parameters) :
    Derives PureModel.theory [] (.iff (liarFormula_m P) (.neg (predicate_m P (liarFormula_m P)))) := by
  apply SemanticTransfer.derives_open_m PureRosserSchedule.target
  intro ℳ hℳ env
  rw [Formula.satisfies_iff_m, Formula.satisfies_neg_m]
  have h := PureFixedPoint.satisfies_m hℳ env (.neg P)
  rw [Formula.satisfies_neg_m] at h
  exact h.trans (not_congr (predicate_satisfies_m hℳ env P (liarFormula_m P)).symm)

theorem liar_refutes_m (P : Candidate_m parameters) :
    Derives PureModel.theory [] (.neg (.iff (predicate_m P (liarFormula_m P)) (liarFormula_m P))) :=
  Tarski.liar_refutes_m (liar_fixed_point_m P)

theorem liar_refutes_closed_m (P : Candidate_m parameters) :
    Derives PureModel.theory [] (Metatheory.Formula.forall_close
      (.neg (.iff (predicate_m P (liarFormula_m P)) (liarFormula_m P)))) :=
  Metatheory.Derives.forall_close_of_derives (liar_refutes_m P)

theorem biconditional_unprovable_m (P : Candidate_m parameters)
    (hT : Derives.Consistent PureModel.theory ([] : Context ℒ [])) :
    ¬ Derives PureModel.theory [] (.iff (predicate_m P (liarFormula_m P)) (liarFormula_m P)) :=
  Tarski.biconditional_unprovable_m (liar_fixed_point_m P)
    (SemanticTransfer.consistent_open_m PureRosserSchedule.target hT _)

def TruthSchema_m (P : Candidate_m parameters) : Prop :=
  ∀ φ : OpenFormula ℒ (pureContext_m parameters),
    Derives PureModel.theory [] (.iff (predicate_m P φ) φ)

theorem undefinable_syntax_m (parameters : SetContext)
    (hT : Derives.Consistent PureModel.theory ([] : Context ℒ [])) :
    ¬ ∃ P : Candidate_m parameters, TruthSchema_m P := by
  rintro ⟨P, h⟩
  exact biconditional_unprovable_m P hT (h (liarFormula_m P))

/-- 对象编码值独立于参数赋值；它命名该纯公式自身的完整 AST。 -/
noncomputable def quotation_m {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) (φ : OpenFormula ℒ (pureContext_m parameters)) :
    PureModel.Carrier ℳ := number_m hℳ (code_m (bound := []) (free := parameters) φ)

def DefinesSatisfaction_m {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) (env : Env ℳ [] (pureContext_m parameters))
    (P : Candidate_m parameters) : Prop :=
  ∀ φ : OpenFormula ℒ (pureContext_m parameters),
    P.satisfies (env.pushFree (quotation_m hℳ φ)) ↔ φ.satisfies env

theorem liar_fails_at_m {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ PureModel.theory)
    (env : Env ℳ [] (pureContext_m parameters)) (P : Candidate_m parameters) :
    ¬ (P.satisfies (env.pushFree (quotation_m hℳ (liarFormula_m P))) ↔
      (liarFormula_m P).satisfies env) := by
  intro h
  have hr := (liar_refutes_m P).sound hℳ env (by intro φ hφ; cases hφ)
  rw [Formula.satisfies_neg_m, Formula.satisfies_iff_m] at hr
  exact hr ((predicate_satisfies_m hℳ env P (liarFormula_m P)).trans h)

theorem undefinable_at_m {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ PureModel.theory)
    (env : Env ℳ [] (pureContext_m parameters)) :
    ¬ ∃ P : Candidate_m parameters, DefinesSatisfaction_m hℳ env P := by
  rintro ⟨P, h⟩
  exact liar_fails_at_m hℳ env P (h (liarFormula_m P))

theorem undefinable_parameters_m {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) :
    ¬ ∃ (parameters : SetContext) (env : Env ℳ [] (pureContext_m parameters))
      (P : Candidate_m parameters), DefinesSatisfaction_m hℳ env P := by
  rintro ⟨parameters, env, P, h⟩
  exact undefinable_at_m hℳ env ⟨P, h⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureTarski
