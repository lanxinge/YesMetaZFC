import YesMetaZFC.Automation.FunctionFreeDelta0
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRosserComplete
import YesMetaZFC.Model.ZFC.Pure.PureSeparation

/-! # 纯隶属 Rosser 的 Δ₀ 参数矩阵与闭句边界

纯签名没有常元或函数，故无参数闭 Δ₀ 公式均为纯逻辑可判定式。
真正的有界比较保留 ω 及两侧证明码集合为显式参数；参数定义及其存在量词
不计入矩阵的 Δ₀ 分类，也不由此免除原模型 Agreement 的义务。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRosserDelta0
open PureModel
open PureFinalTransfer (E)
open Nonlogical.BasicSetTheory (SetSentence SetOpenTerm)
open _root_.YesMetaZFC.Automation
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
attribute [local irreducible] ReducedProofPresentation.presentation ReducedRosser.sentence
  ReducedRosser.presentation
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}

def levyBound : Formula.LevyBound ℒ where
  sort := setSort
  relation := .membership
  domains := rfl

theorem closed_decided (formula : Sentence ℒ) (hDelta : Formula.IsDelta0 levyBound formula) :
    Derives theory [] formula ∨ Derives theory [] (.neg formula) :=
  FunctionFreeDelta0.closed_decided levyBound (fun symbol => nomatch symbol)
    (fun symbol => by cases symbol; intro h; cases h) theory formula hDelta

/-- 当前纯固定点的最外层存在量词没有闭界项，故不能直接分类为 Δ₀。 -/
theorem sentence_not_delta0 : ¬ Formula.IsDelta0 levyBound PureRosser.sentence := by
  obtain ⟨body, hBody⟩ := ReducedRosser.sentence_exists_body
  unfold PureRosser.sentence PureRosser.translate
  rw [hBody]
  exact FunctionFreeDelta0.exists_not_delta0 levyBound (fun symbol => nomatch symbol) _ _

theorem comparison_not_delta0 : ¬ Formula.IsDelta0 levyBound PureRosser.comparison := by
  obtain ⟨body, hBody⟩ := ReducedRosser.predicate_exists_body ReducedRosser.sentence
  unfold PureRosser.comparison PureRosser.translate
  rw [hBody]
  exact FunctionFreeDelta0.exists_not_delta0 levyBound (fun symbol => nomatch symbol) _ _

/-- 即使更换等价闭句，独立性成立时也不可能得到无参数纯 Δ₀ 代表。 -/
theorem no_closed_delta0_equivalent
    (hConsistent : Derives.Consistent theory ([] : Context ℒ []))
    (formula : Sentence ℒ) (hDelta : Formula.IsDelta0 levyBound formula) :
    ¬ Derives theory [] (.iff PureRosser.sentence formula) := by
  intro hEquivalent
  have hIndependent := PureRosser.independent hConsistent
  rcases closed_decided formula hDelta with hTrue | hFalse
  · exact hIndependent.1 (Derives.iff_elim_right hEquivalent hTrue)
  · apply hIndependent.2
    apply Derives.neg_intro
    exact Derives.neg_elim
      (Derives.iff_elim_left hEquivalent.context_weaken_cons
        (Derives.assumption List.mem_cons_self)) hFalse.context_weaken_cons

/-- 纯 ∈ 矩阵：¬∃ p∈ω，p∈positive 且 ∀q∈p，q∉negative。 -/
def matrix {bound free : SortContext ℒ}
    (omega positive negative : Term ℒ bound free setSort) : Formula ℒ bound free :=
  .neg (levyBound.boundedExists omega
    (.conj (levyBound.membership (.bvar .here) (positive.weakenBound setSort))
      (levyBound.boundedForall (.bvar .here)
        (.neg (levyBound.membership (.bvar .here)
          ((negative.weakenBound setSort).weakenBound setSort))))))

theorem matrix_delta0 {bound free : SortContext ℒ}
    (omega positive negative : Term ℒ bound free setSort) :
    Formula.IsDelta0 levyBound (matrix omega positive negative) :=
  .neg (.bounded_exists _ (.conj (.rel _ _) (.bounded_forall _ (.neg (.rel _ _)))))

theorem matrix_satisfies {bound free : SortContext ℒ} (env : Env ℳ bound free)
    (omega positive negative : Term ℒ bound free setSort) :
    (matrix omega positive negative).satisfies env ↔
      ¬ ∃ code, membership ℳ code (omega.eval env) ∧ membership ℳ code (positive.eval env) ∧
        ∀ smaller, membership ℳ smaller code → ¬ membership ℳ smaller (negative.eval env) := by
  simp only [matrix, levyBound, Formula.LevyBound.boundedExists, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, Formula.satisfies, Arguments.eval, Term.eval_weakenBound]
  rfl

/-- 固定结论的原完整证明图之实际纯翻译；本定义未声称 Δ₀。 -/
def proofCondition (formula : SetSentence) : Formula ℒ [] [setSort] :=
  openFormula PureCompletedStage.interpretation
    (ReducedProofPresentation.presentation.graph.condition (.fvar .here : SetOpenTerm [.set])
      ((IntrinsicQuotation.quote formula).weakenFree Nonlogical.BasicSetTheory.SetSort.set))

theorem proofCondition_correct (hℳ : Theory.Models ℳ theory) (formula : SetSentence)
    (code : Carrier ℳ) :
    (proofCondition formula).satisfies (templateEnv (.cons code .nil)) ↔
      PureNaturalRosserAgreement.Proof (E hℳ).model code formula := by
  unfold proofCondition
  refine (openFormula_correct (E hℳ) (PureCompletedStage.realizes hℳ)
    (free := [Nonlogical.BasicSetTheory.SetSort.set]) _ (.cons code .nil)).trans ?_
  have hQuote : ((IntrinsicQuotation.quote formula).weakenFree Nonlogical.BasicSetTheory.SetSort.set).eval
      (templateEnv (.cons code .nil) : Env (E hℳ).model [] [.set]) =
        (IntrinsicQuotation.quote formula).eval (Env.empty : Env (E hℳ).model [] []) := by
    rw [ModelClosure.templateEnv_cons, Term.eval_weakenFree, ModelClosure.templateEnv_nil]
  simpa only [PureNaturalRosserAgreement.Proof, hQuote] using!
    NaturalRosserSemantics.binary_satisfies ReducedProofPresentation.presentation.graph.condition
      (templateEnv (.cons code .nil) : Env (E hℳ).model [] [.set])
      (.fvar .here) ((IntrinsicQuotation.quote formula).weakenFree Nonlogical.BasicSetTheory.SetSort.set)

/-- 输出集合恰好收集给定母集中的实际证明码；两个自由槽为输出、母集。 -/
def proofSetGraph (formula : SetSentence) : Formula ℒ [] [setSort,setSort] :=
  .forallE setSort (.iff (levyBound.membership (.bvar .here) (.fvar .here))
    (.conj (levyBound.membership (.bvar .here) (.fvar (.there .here)))
      (applyTemplate (proofCondition formula) (.cons (.bvar .here) .nil))))

theorem proofSetGraph_correct (hℳ : Theory.Models ℳ theory) (formula : SetSentence)
    (output ambient : Carrier ℳ) :
    (proofSetGraph formula).satisfies (templateEnv (.cons output (.cons ambient .nil))) ↔
      ∀ code, membership ℳ code output ↔ membership ℳ code ambient ∧
        PureNaturalRosserAgreement.Proof (E hℳ).model code formula := by
  simp only [proofSetGraph, Formula.satisfies, applyTemplate_satisfies,
    Arguments.eval, Term.eval, proofCondition_correct hℳ]
  rfl

/-- 三个参数为内部 ω、该句子的证明码集、其否定的证明码集；定义正文不计入 Δ₀ 矩阵。 -/
def parameters (formula : SetSentence) : Formula ℒ [] [setSort,setSort,setSort] :=
  .conj (applyTemplate (PureCompletedStage.interpretation.function .omega) (.cons (.fvar .here) .nil))
    (.conj (applyTemplate (proofSetGraph formula)
      (.cons (.fvar (.there .here)) (.cons (.fvar .here) .nil)))
      (applyTemplate (proofSetGraph (.neg formula))
        (.cons (.fvar (.there (.there .here))) (.cons (.fvar .here) .nil))))

theorem parameters_correct (hℳ : Theory.Models ℳ theory) (formula : SetSentence)
    (omega positive negative : Carrier ℳ) :
    (parameters formula).satisfies (templateEnv (.cons omega (.cons positive (.cons negative .nil)))) ↔
      omega = PureFinalArithmetic.w (E hℳ).model ∧
        (∀ code, membership ℳ code positive ↔ membership ℳ code omega ∧
          PureNaturalRosserAgreement.Proof (E hℳ).model code formula) ∧
        (∀ code, membership ℳ code negative ↔ membership ℳ code omega ∧
          PureNaturalRosserAgreement.Proof (E hℳ).model code (.neg formula)) := by
  simp only [parameters, Formula.satisfies, applyTemplate_satisfies, Arguments.eval,
    Term.eval, proofSetGraph_correct hℳ]
  exact and_congr ((PureCompletedStage.realizes hℳ).function .omega .nil omega) Iff.rfl

/-- 裸 ZFC 的实际纯分离给出两侧证明码集合，不添加集合存在性假设。 -/
theorem parameters_exists (hℳ : Theory.Models ℳ theory) (formula : SetSentence) :
    ∃ omega positive negative, (parameters formula).satisfies
      (templateEnv (.cons omega (.cons positive (.cons negative .nil))) :
        Env ℳ [] [setSort,setSort,setSort]) := by
  let omega := PureFinalArithmetic.w (E hℳ).model
  obtain ⟨positive, hPositive⟩ := PureSeparation.exists_subset hℳ (proofCondition formula) .nil omega
  obtain ⟨negative, hNegative⟩ := PureSeparation.exists_subset hℳ (proofCondition (.neg formula)) .nil omega
  refine ⟨omega, positive, negative, (parameters_correct hℳ formula omega positive negative).mpr ⟨rfl, ?_, ?_⟩⟩
  · intro code
    exact (hPositive code).trans (and_congr Iff.rfl (proofCondition_correct hℳ formula code))
  · intro code
    exact (hNegative code).trans (and_congr Iff.rfl (proofCondition_correct hℳ (.neg formula) code))

/-- 参数由原模型的规范解释唯一确定，不能任意挑选以改变矩阵真值。 -/
theorem parameters_unique (hℳ : Theory.Models ℳ theory) (formula : SetSentence)
    {omega positive negative otherOmega otherPositive otherNegative : Carrier ℳ}
    (hFirst : (parameters formula).satisfies
      (templateEnv (.cons omega (.cons positive (.cons negative .nil)))))
    (hSecond : (parameters formula).satisfies
      (templateEnv (.cons otherOmega (.cons otherPositive (.cons otherNegative .nil))))) :
    omega = otherOmega ∧ positive = otherPositive ∧ negative = otherNegative := by
  obtain ⟨hOmega, hPositive, hNegative⟩ := (parameters_correct hℳ formula _ _ _).mp hFirst
  obtain ⟨hOtherOmega, hOtherPositive, hOtherNegative⟩ := (parameters_correct hℳ formula _ _ _).mp hSecond
  have hSame := hOmega.trans hOtherOmega.symm
  cases hSame
  exact ⟨rfl, extensionality hℳ _ _ (fun code => (hPositive code).trans (hOtherPositive code).symm),
    extensionality hℳ _ _ (fun code => (hNegative code).trans (hOtherNegative code).symm)⟩

/-- 指定实际集合参数后，纯 Δ₀ 矩阵精确表示规范扩张中的 Rosser 比较式否定。 -/
theorem matrix_correct (hℳ : Theory.Models ℳ theory) (formula : SetSentence)
    (omega positive negative : Carrier ℳ)
    (hParameters : (parameters formula).satisfies
      (templateEnv (.cons omega (.cons positive (.cons negative .nil))))) :
    (matrix (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).satisfies
      (templateEnv (.cons omega (.cons positive (.cons negative .nil)))) ↔
        ¬ (ReducedRosser.presentation.predicate_of formula).TrueIn (E hℳ).model := by
  obtain ⟨rfl, hPositive, hNegative⟩ := (parameters_correct hℳ formula _ _ _).mp hParameters
  rw [matrix_satisfies]
  apply not_congr
  rw [PureNaturalRosserAgreement.comparison_naturals (PureZFCModels.models hℳ) formula]
  change (∃ code, membership ℳ code (PureFinalArithmetic.w (E hℳ).model) ∧
    membership ℳ code positive ∧ ∀ smaller, membership ℳ smaller code → ¬ membership ℳ smaller negative) ↔
    (∃ code, membership ℳ code (PureFinalArithmetic.w (E hℳ).model) ∧
      PureNaturalRosserAgreement.Proof (E hℳ).model code formula ∧
        ∀ smaller, membership ℳ smaller code → ¬ PureNaturalRosserAgreement.Proof (E hℳ).model smaller (.neg formula))
  constructor
  · rintro ⟨code, hCode, hMember, hSmaller⟩
    exact ⟨code, hCode, ((hPositive code).mp hMember).2, fun smaller hLess hProof =>
      hSmaller smaller hLess ((hNegative smaller).mpr
        ⟨(PureFinalArithmetic.mem_final hℳ _ _).mp
          (PureSourceInfinity.member_natural (PureZFCModels.models hℳ)
            ((PureFinalArithmetic.mem_final hℳ _ _).mpr hCode)
            ((PureFinalArithmetic.mem_final hℳ _ _).mpr hLess)), hProof⟩)⟩
  · rintro ⟨code, hCode, hProof, hSmaller⟩
    exact ⟨code, hCode, (hPositive code).mpr ⟨hCode, hProof⟩, fun smaller hLess hMember =>
      hSmaller smaller hLess (((hNegative smaller).mp hMember).2)⟩

theorem sentence_iff_matrix (hℳ : Theory.Models ℳ theory) (omega positive negative : Carrier ℳ)
    (hParameters : (parameters ReducedRosser.sentence).satisfies
      (templateEnv (.cons omega (.cons positive (.cons negative .nil))))) :
    PureRosser.sentence.TrueIn ℳ ↔
      (matrix (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).satisfies
        (templateEnv (.cons omega (.cons positive (.cons negative .nil)))) := by
  have hComparison := PureRosser.translate_truth_iff hℳ
    (ReducedRosser.presentation.predicate_of ReducedRosser.sentence)
  exact (PureRosser.fixed_point_truth hℳ).trans
    ((not_congr hComparison).trans (matrix_correct hℳ ReducedRosser.sentence _ _ _ hParameters).symm)

def matrixBody : Formula ℒ [] [setSort,setSort,setSort] :=
  matrix (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

/-- 参数定义和存在量词显式保留在矩阵外；整个闭句未分类为 Δ₀。 -/
def representation (formula : SetSentence) : Sentence ℒ :=
  existsBlock [setSort,setSort,setSort]
    (.conj (applyTemplate (parameters formula)
      (witnesses (τ := ℒ) (bound := []) (free := []) [setSort,setSort,setSort]))
      (applyTemplate matrixBody
        (witnesses (τ := ℒ) (bound := []) (free := []) [setSort,setSort,setSort])))

theorem representation_satisfies (formula : SetSentence) :
    (representation formula).TrueIn ℳ ↔ ∃ omega positive negative,
      (parameters formula).satisfies (templateEnv (.cons omega (.cons positive (.cons negative .nil))) :
        Env ℳ [] [setSort,setSort,setSort]) ∧
      matrixBody.satisfies (templateEnv (.cons omega (.cons positive (.cons negative .nil)))) := by
  simp only [representation, Formula.TrueIn, existsBlock_satisfies, Formula.satisfies,
    applyTemplate_satisfies, witnesses_eval]
  constructor
  · rintro ⟨values, hParameters, hMatrix⟩
    cases values with
    | cons omega rest =>
      cases rest with
      | cons positive rest =>
        cases rest with
        | cons negative rest =>
          cases rest
          exact ⟨omega, positive, negative, hParameters, hMatrix⟩
  · rintro ⟨omega, positive, negative, hParameters, hMatrix⟩
    exact ⟨.cons omega (.cons positive (.cons negative .nil)), hParameters, hMatrix⟩

theorem representation_correct (hℳ : Theory.Models ℳ theory) :
    PureRosser.sentence.TrueIn ℳ ↔ (representation ReducedRosser.sentence).TrueIn ℳ := by
  rw [representation_satisfies]
  constructor
  · intro hSentence
    obtain ⟨omega, positive, negative, hParameters⟩ := parameters_exists hℳ ReducedRosser.sentence
    exact ⟨omega, positive, negative, hParameters,
      (sentence_iff_matrix hℳ omega positive negative hParameters).mp hSentence⟩
  · rintro ⟨omega, positive, negative, hParameters, hMatrix⟩
    exact (sentence_iff_matrix hℳ omega positive negative hParameters).mpr hMatrix

/-- 参数存在性及精确语义经已配置的纯公平调度给出裸 ZFC 普通推导等价。 -/
theorem representation_derives : Derives theory []
    (.iff PureRosser.sentence (representation ReducedRosser.sentence)) := by
  apply Completeness.strong_completeness PureRosserSchedule.target
  intro ℳ hℳ
  exact representation_correct hℳ

theorem representation_not_delta0 (formula : SetSentence) :
    ¬ Formula.IsDelta0 levyBound (representation formula) :=
  FunctionFreeDelta0.exists_not_delta0 levyBound (fun symbol => nomatch symbol) _ _

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureRosserDelta0
