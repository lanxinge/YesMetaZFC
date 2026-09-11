import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureArithmeticSpecifications

/-! # 任意可定义全函数的内部 ω 迭代

由零、后继、极限三分支的序数递归构造 ω 长序列。对 ω 的成员，原零步与
后继步精确恢复给定函数迭代；不对模型成员施加外部良基性。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureOmegaIteration
open PureModel PureNaturalInduction PureArithmeticSpecifications
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model Project.FirstOrderSemantics.reduct
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}

/-- 把一个无参数二元 schema 提升为带初值的历史递归算子。 -/
def history (step : Project.BinarySchema 0) : Project.BinarySchema 1 where
  body :=
    .disj (.conj (Project.Formula.isZeroLengthSequence PureKuratowskiProject.convention (.bound 1))
      (Project.Formula.extensionalEq (.bound 0) (.bound 2))) <|
    .disj (.existsE <| .conj (Project.Formula.isSuccessorLengthSequenceWithLast PureKuratowskiProject.convention (.bound 2) (.bound 0))
      (Project.Formula.related step .empty (.bound 0) (.bound 1)))
      (Project.Formula.isLimitLengthSequenceWithUnion PureKuratowskiProject.convention (.bound 1) (.bound 0))
def Operator (hℳ : Theory.Models ℳ theory) (relation : Carrier ℳ → Carrier ℳ → Prop) (seed : Carrier ℳ) :
    Carrier ℳ → Carrier ℳ → Prop :=
  (Project.FirstOrderSemantics.reduct ℳ).IsZeroSuccessorLimitStep (PureKuratowskiProject.interpretation hℳ)
    (fun output => output = seed) relation

def Represents (step : Project.BinarySchema 0) (relation : Carrier ℳ → Carrier ℳ → Prop) : Prop :=
  ∀ (env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 0) input output,
    step.denote env input output ↔ relation input output

theorem history_correct (hℳ : Theory.Models ℳ theory) {step : Project.BinarySchema 0}
    {relation : Carrier ℳ → Carrier ℳ → Prop} (hRep : Represents step relation)
    (env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 1) (sequence output : Carrier ℳ) :
    (history step).denote env sequence output ↔ Operator hℳ relation (env.bound 0) sequence output := by
  change Project.Formula.satisfies ((env.push sequence).push output) (history step).body ↔ _
  simp only [history,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isZeroLengthSequence_iff (PureKuratowskiProject.interpretation hℳ) (project_models hℳ).1,
    Project.Formula.satisfies_isSuccessorLengthSequenceWithLast_iff (PureKuratowskiProject.interpretation hℳ) (project_models hℳ).1,
    Project.Formula.satisfies_isLimitLengthSequenceWithUnion_iff (PureKuratowskiProject.interpretation hℳ) (project_models hℳ).1,
    Project.Formula.satisfies_extensionalEq_iff_eq (project_models hℳ).1,
    Project.Formula.satisfies_related_iff,
    Project.Term.eval_bound_zero_push,Project.Term.eval_bound_one_push,Project.Term.eval_bound_two_push]
  apply or_congr Iff.rfl
  apply or_congr _ Iff.rfl
  apply exists_congr
  intro previous
  exact and_congr Iff.rfl (hRep _ previous output)

def sequenceBody (step : Project.BinarySchema 0) : Project.Formula 1 3 :=
  Project.Formula.isRecursiveSequence PureKuratowskiProject.convention (history step)
    (TermVector.boundParameters 1 2) (.bound 0) (.bound 1)

theorem sequenceBody_closed (step : Project.BinarySchema 0) : (sequenceBody step).FreeClosed := by
  simpa only [Project.BinarySchema.recursiveSequenceExistence, Formula.FreeClosed, sequenceBody, Term.newest] using
    ((history step).recursiveSequenceExistence PureKuratowskiProject.convention).freeClosed

def sequencePure (step : Project.BinarySchema 0) : Formula ℒ [] [setSort,setSort,setSort] :=
  PureProjectTemplate.toPure (sequenceBody step) (sequenceBody_closed step)

theorem sequencePure_correct (hℳ : Theory.Models ℳ theory) {step : Project.BinarySchema 0}
    {relation : Carrier ℳ → Carrier ℳ → Prop} (hRep : Represents step relation) (sequence length seed : Carrier ℳ) :
    (sequencePure step).satisfies (templateEnv (.cons sequence (.cons length (.cons seed .nil)))) ↔
      (Project.FirstOrderSemantics.reduct ℳ).IsRecursiveSequence (PureKuratowskiProject.interpretation hℳ)
        (Operator hℳ relation seed) sequence length := by
  apply (PureProjectTemplate.correct hℳ (sequenceBody step) (sequenceBody_closed step)
    (.cons sequence (.cons length (.cons seed .nil))) sequence).trans
  rw [sequenceBody,Project.Formula.satisfies_isRecursiveSequence_iff (PureKuratowskiProject.interpretation hℳ) (project_models hℳ).1]
  have hOperator : (history step).denote
      ((TermVector.boundParameters 1 2).evalEnv (PureProjectTemplate.parameterEnv (.cons sequence (.cons length (.cons seed .nil))) sequence)) =
      Operator hℳ relation seed := by
    funext prior output
    exact propext (history_correct hℳ hRep _ prior output)
  rw [hOperator]
  rfl

def graph (step : Project.BinarySchema 0) : Formula ℒ [] [setSort,setSort] :=
  .existsE setSort <| .conj (applyTemplate PureOmegaAndReverse.omegaGraph (.cons (.bvar .here) .nil))
    (applyTemplate (sequencePure step) (.cons (.fvar .here) (.cons (.bvar .here) (.cons (.fvar (.there .here)) .nil))))

theorem graph_correct (hℳ : Theory.Models ℳ theory) {step : Project.BinarySchema 0}
    {relation : Carrier ℳ → Carrier ℳ → Prop} (hRep : Represents step relation) (sequence seed : Carrier ℳ) :
    (graph step).satisfies (templateEnv (.cons sequence (.cons seed .nil))) ↔
      (Project.FirstOrderSemantics.reduct ℳ).IsRecursiveSequence (PureKuratowskiProject.interpretation hℳ)
        (Operator hℳ relation seed) sequence (omega hℳ) := by
  simp only [graph,Formula.satisfies,applyTemplate_satisfies]
  change (∃ ω, PureOmegaAndReverse.omegaGraph.satisfies (templateEnv (.cons ω .nil)) ∧
    (sequencePure step).satisfies (templateEnv (.cons sequence (.cons ω (.cons seed .nil))))) ↔ _
  constructor
  · rintro ⟨ω,hω,hSequence⟩
    have hEqual : ω = omega hℳ := ((PureDifferenceStage.realizes hℳ).function .omega .nil ω).mp hω
    subst ω
    exact (sequencePure_correct hℳ hRep sequence (omega hℳ) seed).mp hSequence
  · intro hSequence
    exact ⟨omega hℳ,((PureDifferenceStage.realizes hℳ).function .omega .nil _).mpr rfl,
      (sequencePure_correct hℳ hRep sequence (omega hℳ) seed).mpr hSequence⟩

theorem operator_functional (hℳ : Theory.Models ℳ theory) {relation : Carrier ℳ → Carrier ℳ → Prop}
    (hTotal : ∀ input, ∃ output, relation input output ∧ ∀ other, relation input other → other = output) (seed : Carrier ℳ) :
    (Project.FirstOrderSemantics.reduct ℳ).IsClassFunctionOnTransfiniteSequences (PureKuratowskiProject.interpretation hℳ)
      (Operator hℳ relation seed) :=
  _root_.YesMetaZFC.SetTheory.ZF.zeroSuccessorLimitStep_isClassFunctionOnTransfiniteSequences
    (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) _ _ ⟨seed,rfl,fun _ h => h⟩ hTotal

/-- 给定全定义单值步的纯图在任意初值上都有唯一 ω 长输出。 -/
theorem functional (hℳ : Theory.Models ℳ theory) {step : Project.BinarySchema 0}
    {relation : Carrier ℳ → Carrier ℳ → Prop} (hRep : Represents step relation)
    (hTotal : ∀ input, ∃ output, relation input output ∧ ∀ other, relation input other → other = output) (seed : Carrier ℳ) :
    ∃ sequence, (graph step).satisfies (templateEnv (.cons sequence (.cons seed .nil))) ∧
      ∀ other, (graph step).satisfies (templateEnv (.cons other (.cons seed .nil))) → other = sequence := by
  let env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) 1 := {bound := fun _ => seed,free := fun _ => seed}
  have hOperator : (history step).denote env = Operator hℳ relation seed := by
    funext sequence output
    exact propext (history_correct hℳ hRep env sequence output)
  have hFunction : (Project.FirstOrderSemantics.reduct ℳ).IsClassFunctionOnTransfiniteSequences
      (PureKuratowskiProject.interpretation hℳ) ((history step).denote env) :=
    hOperator.symm ▸ operator_functional hℳ hTotal seed
  obtain ⟨sequence,hSequence⟩ := _root_.YesMetaZFC.SetTheory.ZF.recursiveSequence_exists
    (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) env (history step) hFunction
    ((omega_project hℳ).isOrdinal (project_modelsZF hℳ))
  refine ⟨sequence,(graph_correct hℳ hRep sequence seed).mpr (hOperator ▸ hSequence),?_⟩
  intro other hOther
  have hOther := (graph_correct hℳ hRep other seed).mp hOther
  exact _root_.YesMetaZFC.SetTheory.ZF.recursiveSequence_unique (project_modelsZF hℳ)
    (PureKuratowskiProject.interpretation hℳ) env (history step) hFunction (hOperator.symm ▸ hOther) hSequence

/-- ω 迭代的函数图、精确定义域、初值和后继方程。 -/
def Iterates (hℳ : Theory.Models ℳ theory) (relation : Carrier ℳ → Carrier ℳ → Prop) (sequence seed : Carrier ℳ) : Prop :=
  PureKuratowski.IsFunction ℳ sequence ∧
    (∀ input, membership ℳ input (omega hℳ) ↔ ∃ output, PureKuratowski.PairMember ℳ input output sequence) ∧
      value hℳ sequence (zero hℳ) = seed ∧
        ∀ input, membership ℳ input (omega hℳ) → relation (value hℳ sequence input) (value hℳ sequence (succ hℳ input))

theorem iterates_of_graph (hℳ : Theory.Models ℳ theory) {step : Project.BinarySchema 0}
    {relation : Carrier ℳ → Carrier ℳ → Prop} (hRep : Represents step relation)
    (hTotal : ∀ input, ∃ output, relation input output ∧ ∀ other, relation input other → other = output)
    {sequence seed : Carrier ℳ} (hGraph : (graph step).satisfies (templateEnv (.cons sequence (.cons seed .nil)))) :
    Iterates hℳ relation sequence seed := by
  have hSequence := (graph_correct hℳ hRep sequence seed).mp hGraph
  have hValue {input : Carrier ℳ} (hInput : membership ℳ input (omega hℳ)) :
      PureKuratowski.PairMember ℳ input (value hℳ sequence input) sequence :=
    (PureRelationFunctions.application_spec hSequence.1.2.1 ((hSequence.1.2.2 input).mp hInput) _).mp
      (((PureDifferenceStage.realizes hℳ).function .application (.cons sequence (.cons input .nil)) _).mpr rfl)
  refine ⟨hSequence.1.2.1,hSequence.1.2.2,?_,?_⟩
  · obtain ⟨restricted,hRestricted,hOutput⟩ := hSequence.2 (zero hℳ) (zero_mem hℳ) _ (hValue (zero_mem hℳ))
    have hRestriction := hSequence.1.restriction (zero_mem hℳ) hRestricted
    obtain ⟨_,_,hUnique⟩ := operator_functional hℳ hTotal seed restricted ⟨zero hℳ,hRestriction⟩
    exact (hUnique _ hOutput).trans (hUnique seed (Or.inl ⟨⟨zero hℳ,hRestriction,zero_spec hℳ⟩,rfl⟩)).symm
  · intro input hInput
    obtain ⟨restricted,hRestricted,hOutput⟩ := hSequence.2 (succ hℳ input) (succ_mem hℳ hInput) _ (hValue (succ_mem hℳ hInput))
    have hRestriction := hSequence.1.restriction (succ_mem hℳ hInput) hRestricted
    have hLast := (hRestricted.2 input (value hℳ sequence input)).mpr
      ⟨(succ_spec hℳ input input).mpr (Or.inr rfl),hValue hInput⟩
    have hSuccessor : (Project.FirstOrderSemantics.reduct ℳ).IsSuccessorLengthSequenceWithLast
        (PureKuratowskiProject.interpretation hℳ) restricted (value hℳ sequence input) :=
      ⟨input,(omega_project hℳ).members_areOrdinals (project_modelsZF hℳ) input hInput,
        succ hℳ input,succ_project hℳ input,hRestriction,hLast⟩
    obtain ⟨next,hNext,_⟩ := hTotal (value hℳ sequence input)
    obtain ⟨_,_,hUnique⟩ := operator_functional hℳ hTotal seed restricted ⟨succ hℳ input,hRestriction⟩
    have hEqual := (hUnique _ hOutput).trans (hUnique next (Or.inr (Or.inl ⟨_,hSuccessor,hNext⟩))).symm
    exact hEqual.symm ▸ hNext

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureOmegaIteration
