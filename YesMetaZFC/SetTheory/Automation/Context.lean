import YesMetaZFC.SetTheory.Automation

/-!
# `prove_auto` 的集合论上下文来源

本模块把同一理论下的局部语义定理转换为 proof-carrying source premises。元层过滤只决定
哪些局部定理值得送入搜索；最终 soundness 仍由 `ContextSlice.soundOfSearch` 和 canonical
DAG source table 承担。

相关性采用伪类型式的层级 key：

* 高层句子定义用 `@[prove_auto_unfold key]` 标记；
* 目标与候选 key 必须相等，或位于同一祖先/后代链；
* 未标记、跨理论、含局部动态句子值的候选不会进入搜索；
* 候选按 key 距离排序，并受 `prove_auto.context.maxFacts` 限制。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Automation

open Lean Meta
open _root_.YesMetaZFC.Automation
open _root_.YesMetaZFC.Automation.CoreSyntax
open _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm

/-- 一条由原理论语义推出的上下文句子。 -/
structure ContextFact (theory : Theory) where
  sentence : ProjectSentence
  sound : SemanticallyEntails.{0} theory sentence

/-- 显式理论切片加上经过相关性过滤的局部定理。 -/
structure ContextSlice (theory : Theory) where
  base : TheorySlice theory
  facts : List (ContextFact theory)
  premises : List ProjectSentence
  premisesAligned :
    premises = base.axioms ++ facts.map ContextFact.sentence

namespace ContextSlice

/--
从独立的句子表和 proof-carrying facts 构造上下文切片。

`sentences` 是搜索实际消费的纯数据；`hSentences` 只用于 soundness 对齐。
-/
@[reducible] def ofFacts {theory : Theory} (base : TheorySlice theory)
    (facts : List (ContextFact theory)) (sentences : List ProjectSentence)
    (hSentences : facts.map ContextFact.sentence = sentences) :
    ContextSlice theory where
  base := base
  facts := facts
  premises := base.axioms ++ sentences
  premisesAligned := by rw [hSentences]

/-- 上下文切片中的每个句子都由原理论语义推出。 -/
theorem entails {theory : Theory} (slice : ContextSlice theory)
    {sentence : ProjectSentence} (hSentence : sentence ∈ slice.premises) :
    SemanticallyEntails.{0} theory sentence := by
  have hAligned :
      sentence ∈
        slice.base.axioms ++
          slice.facts.map ContextFact.sentence := by
    rw [← slice.premisesAligned]
    exact hSentence
  rcases List.mem_append.mp hAligned with hBase | hContext
  · exact Theory.entails_of_mem (slice.base.member sentence hBase)
  · rcases List.mem_map.mp hContext with ⟨fact, hFact, rfl⟩
    exact fact.sound

/-- 一张纯句子表进入 preprocessing core。 -/
def sourceProblemOfPremises (premises : List ProjectSentence)
    (target : ProjectSentence) : SourcePreprocessing.Problem := {
  premises := premises.map fun sentence =>
    Translate.coreFormula sentence.formula
  target := Translate.coreFormula target.formula
}

/-- 一张纯句子表进入 SearchSignature 深问题。 -/
def deepProblemOfPremises (premises : List ProjectSentence)
    (target : ProjectSentence) : SourcePreprocessing.DeepProblem := {
  premises := premises.map fun sentence =>
    Translate.searchFormula sentence.formula
  target := Translate.searchFormula target.formula
}

/-- 上下文句子进入 preprocessing core。 -/
def sourceProblem {theory : Theory} (slice : ContextSlice theory)
    (target : ProjectSentence) : SourcePreprocessing.Problem :=
  sourceProblemOfPremises slice.premises target

/-- 上下文句子进入 SearchSignature 深问题。 -/
def deepProblem {theory : Theory} (slice : ContextSlice theory)
    (target : ProjectSentence) : SourcePreprocessing.DeepProblem :=
  deepProblemOfPremises slice.premises target

/-- 搜索层定理经 proof-carrying 上下文切片提升回原集合论理论。 -/
theorem soundOfSearch {theory : Theory} (slice : ContextSlice theory)
    (target : ProjectSentence)
    (hSearch :
      LogicSoundness.SetLevel.SemanticallyEntails
        (slice.deepProblem target).theory
        (slice.deepProblem target).target) :
    SemanticallyEntails.{0} theory target := by
  intro M hModels free
  let env : SetTheory.Env M 0 := {
    bound := Fin.elim0
    free := free
  }
  let searchEnv := searchEnvOfSet env
  have hAgreement : SearchAgreement env searchEnv :=
    searchEnvOfSet_agrees env
  have hSearchTarget :=
    hSearch searchEnv (by
      intro formula hFormula
      rcases List.mem_map.mp hFormula with
        ⟨sentence, hSentence, rfl⟩
      exact
        (Translate.satisfies_searchFormula hAgreement
          sentence.formula).mp
          (slice.entails hSentence M hModels free))
  exact
    (Translate.satisfies_searchFormula hAgreement
      target.formula).mpr hSearchTarget

/-- 上下文 source/deep 问题之间的纯一阶反模型桥。 -/
def firstOrderBridge {theory : Theory} (slice : ContextSlice theory)
    (target : ProjectSentence) :
    SourcePreprocessing.FirstOrderProblemBridge
      (slice.sourceProblem target) (slice.deepProblem target) := by
  constructor
  intro M env hModels hTarget
  refine ⟨{
    model := coreModelOfSearch M
    functionSort := coreModel_functionSort M
    env := coreEnvOfSearch env
    respectsFree := coreEnv_respectsFree env
    satisfies := ?_
  }⟩
  unfold sourceProblem SourcePreprocessing.Problem.refutationSource
  apply coreSatisfiesConjunctionList
  intro formula hFormula
  simp only [List.mem_append, List.mem_singleton] at hFormula
  rcases hFormula with hPremise | hTargetFormula
  · rcases List.mem_map.mp hPremise with
      ⟨sentence, hSentence, rfl⟩
    exact
      (satisfies_coreFormula env sentence.formula).mpr <|
        hModels (Translate.searchFormula sentence.formula) <| by
          exact List.mem_map.mpr ⟨sentence, hSentence, rfl⟩
  · subst formula
    have hCoreTarget :
        ¬ Semantics.Formula.Satisfies
          (coreEnvOfSearch env)
          (Translate.coreFormula target.formula) := by
      intro hCore
      exact hTarget <|
        (satisfies_coreFormula env target.formula).mp hCore
    simpa [Semantics.Formula.Satisfies, Semantics.Formula.eval] using
      hCoreTarget

/--
从 proof-carrying 切片和独立的纯问题快照构造后端请求。

两个等同性只连接 soundness；可执行 closed 状态完全由纯问题快照计算。
-/
def goalAttemptFromProblems {theory : Theory} (slice : ContextSlice theory)
    (target : ProjectSentence) (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = slice.sourceProblem target)
    (hProblem : problem = slice.deepProblem target)
    (settings : SourcePreprocessing.FirstOrderSettings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (label : String := "pure set theory with context") :
    ProveAutoRequest.GoalAttempt
      (SemanticallyEntails.{0} theory target) := by
  let bridge : SourcePreprocessing.FirstOrderProblemBridge sourceProblem problem := by
    rw [hSource, hProblem]
    exact slice.firstOrderBridge target
  let attempt :=
    SourcePreprocessing.runFirstOrderProvider
      sourceProblem problem bridge settings avatarConfig label
  exact {
    closed :=
      SourcePreprocessing.runFirstOrderProviderClosed
        sourceProblem problem settings avatarConfig label
    summary :=
      SourcePreprocessing.runFirstOrderProviderSummary
        sourceProblem problem settings avatarConfig label
    sound := by
      intro hClosed
      have hAttemptClosed : attempt.closed = true := by
        dsimp [attempt]
        exact
          (SourcePreprocessing.runFirstOrderProvider_closed
            sourceProblem problem bridge settings avatarConfig label).trans hClosed
      have hSearch :
          LogicSoundness.SetLevel.SemanticallyEntails
            problem.theory problem.target :=
        ProveAutoRequest.GoalAttempt.backendSoundOfClosed
          problem attempt hAttemptClosed
      apply slice.soundOfSearch target
      rw [← hProblem]
      exact hSearch
  }

/-- 元层搜索只引用 checked preprocessing 与 DAG replay，集合论切片负责最终提升。 -/
def goalAttemptFromReplay {theory : Theory} (slice : ContextSlice theory)
    (target : ProjectSentence) (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = slice.sourceProblem target)
    (hProblem : problem = slice.deepProblem target)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check sourceProblem payload = true)
    (label : String)
    (data :
      SearchMaterialization.SearchCertificateProvider.PreparedReplaySearchData
        (SourcePreprocessing.FirstOrderReplay.searchInput
          payload problem search label)) :
    ProveAutoRequest.GoalAttempt
      (SemanticallyEntails.{0} theory target) := by
  let bridge : SourcePreprocessing.FirstOrderProblemBridge sourceProblem problem := by
    rw [hSource, hProblem]
    exact slice.firstOrderBridge target
  let replay :=
    SourcePreprocessing.FirstOrderReplay.ofCheck
      sourceProblem payload hReplay
  let attempt : LogicSoundness.SetLevel.BackendAttempt problem :=
    .success (data.backendSuccessAt (replay.refutationBridgeAt bridge))
  exact {
    closed := true
    summary := "DAG reflection/DAG check: closed"
    sound := by
      intro _
      have hAttemptClosed :
          LogicSoundness.SetLevel.BackendAttempt.closed attempt = true := rfl
      have hSearch :
          LogicSoundness.SetLevel.SemanticallyEntails
            problem.theory problem.target :=
        ProveAutoRequest.GoalAttempt.backendSoundOfClosed
          problem attempt hAttemptClosed
      apply slice.soundOfSearch target
      rw [← hProblem]
      exact hSearch
  }

/-- 从一个上下文切片构造完整的 proof-carrying 后端请求。 -/
def goalAttempt {theory : Theory} (slice : ContextSlice theory)
    (target : ProjectSentence)
    (settings : SourcePreprocessing.FirstOrderSettings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (label : String := "pure set theory with context") :
    ProveAutoRequest.GoalAttempt
      (SemanticallyEntails.{0} theory target) :=
  goalAttemptFromProblems slice target
    (slice.sourceProblem target) (slice.deepProblem target)
    rfl rfl settings avatarConfig label

end ContextSlice

/--
集合论目标的静态搜索配置。

局部上下文 provider 在保留此配置的前提下追加相关定理；没有相关定理时，普通
`GoalRequest` 仍然沿原路径运行。
-/
class GoalProfile (theory : Theory) (target : ProjectSentence) where
  slice : TheorySlice theory
  settings : SourcePreprocessing.FirstOrderSettings := {}
  avatarConfig : SourcePreprocessing.AvatarConfig := {}
  label : String := "pure set theory"

namespace GoalProfile

/-- 没有显式公理切片的默认上下文配置，只供 provider 找到相关局部定理时使用。 -/
@[reducible] def empty (theory : Theory) (target : ProjectSentence) :
    GoalProfile theory target where
  slice := TheorySlice.empty theory

/-- profile 的无局部上下文请求。 -/
@[reducible] def request {theory : Theory} {target : ProjectSentence}
    (profile : GoalProfile theory target) :
    ProveAutoRequest.GoalRequest
      (SemanticallyEntails.{0} theory target) where
  run :=
    ContextSlice.goalAttempt
      (ContextSlice.ofFacts profile.slice [] [] rfl)
      target profile.settings profile.avatarConfig profile.label

end GoalProfile

/-- 声明了 `GoalProfile` 的目标自动获得原有裸 `prove_auto` 请求。 -/
instance {theory : Theory} {target : ProjectSentence}
    [profile : GoalProfile theory target] :
    ProveAutoRequest.GoalRequest
      (SemanticallyEntails.{0} theory target) :=
  profile.request

/-! ## 元层强相关过滤 -/

private def matchEntails? (type : Expr) : Option (Expr × Expr) :=
  let (head, arguments) := type.getAppFnArgs
  if head == ``SemanticallyEntails && arguments.size == 2 then
    some (arguments[0]!, arguments[1]!)
  else
    none

private structure Candidate where
  name : Name
  sentence : Expr
  proof : Expr
  keys : Array Name
  score : Nat

private def theoremCandidate? (goalTheory : Expr) (targetKeys : Array Name)
    (localDecl : LocalDecl) : MetaM (Option Candidate) := do
  if localDecl.isImplementationDetail || localDecl.isAuxDecl ||
      localDecl.isLet then
    return none
  let some (candidateTheory, sentence) := matchEntails? localDecl.type
    | return none
  unless ← isDefEq candidateTheory goalTheory do
    return none
  if sentence.hasFVar then
    return none
  let keys ← ProveAutoRequest.ContextRelevance.collectUnfoldKeys sentence
  let score :=
    ProveAutoRequest.ContextRelevance.unfoldScore targetKeys keys
  if score == 0 then
    return none
  return some {
    name := localDecl.userName
    sentence := sentence
    proof := localDecl.toExpr
    keys := keys
    score := score
  }

private def collectCandidates (goalTheory targetSentence : Expr) :
    MetaM (Array Candidate) := do
  let targetKeys ←
    ProveAutoRequest.ContextRelevance.collectUnfoldKeys targetSentence
  if targetKeys.isEmpty then
    return #[]
  let mut candidates := #[]
  for localDecl in (← getLCtx) do
    if let some candidate ←
        theoremCandidate? goalTheory targetKeys localDecl then
      if !candidates.any fun existing =>
          existing.sentence == candidate.sentence then
        candidates := candidates.push candidate
  let ordered := candidates.qsort fun left right =>
    left.score > right.score
  let maxFacts : Nat :=
    (← getOptions).get `prove_auto.context.maxFacts 16
  let selected := ordered.take maxFacts
  let selectedSummary :=
    selected.map fun candidate =>
      (candidate.name, candidate.keys, candidate.score)
  trace[YesMetaZFC.proveAuto.context]
    "target keys={targetKeys}; selected={selectedSummary}"
  return selected

private def profileFor (theory target : Expr) : MetaM Expr := do
  let profileType := mkApp2 (mkConst ``GoalProfile) theory target
  try
    synthInstance profileType
  catch _ =>
    mkAppM ``GoalProfile.empty #[theory, target]

private def contextFactExpr (theory : Expr) (candidate : Candidate) :
    MetaM Expr := do
  let factType := mkApp (mkConst ``ContextFact) theory
  let fact ← mkAppM ``ContextFact.mk #[candidate.sentence, candidate.proof]
  let actualType ← inferType fact
  unless ← isDefEq actualType factType do
    throwError
      "internal context fact type mismatch:{indentExpr actualType}\nexpected:{indentExpr factType}"
  return fact

private unsafe def buildContextAttemptImpl?
    (request : ProveAutoRequest.PreparedContextRequest) :
    MetaM (Option Expr) := do
  let goal := request.goal
  let some (theory, target) := matchEntails? goal
    | return none
  if target.hasFVar then
    return none
  let candidates ← collectCandidates theory target
  let profile ← profileFor theory target
  let base :=
    mkApp3 (mkConst ``GoalProfile.slice) theory target profile
  let settings :=
    mkApp3 (mkConst ``GoalProfile.settings) theory target profile
  let avatarConfig :=
    mkApp3 (mkConst ``GoalProfile.avatarConfig) theory target profile
  let label :=
    mkApp3 (mkConst ``GoalProfile.label) theory target profile
  let factType := mkApp (mkConst ``ContextFact) theory
  let facts ← candidates.toList.mapM (contextFactExpr theory)
  let factList ← mkListLit factType facts
  let sentences ←
    mkListLit (mkConst ``ProjectSentence)
      (candidates.toList.map Candidate.sentence)
  let hSentences ← mkEqRefl sentences
  let slice ← mkAppM ``ContextSlice.ofFacts
    #[base, factList, sentences, hSentences]
  let baseAxioms ← mkAppM ``TheorySlice.axioms #[base]
  let premises ← mkAppM ``List.append #[baseAxioms, sentences]
  let sourceProblem ←
    mkAppM ``ContextSlice.sourceProblemOfPremises #[premises, target]
  let problem ←
    mkAppM ``ContextSlice.deepProblemOfPremises #[premises, target]
  let expectedSource ← mkAppM ``ContextSlice.sourceProblem #[slice, target]
  let expectedProblem ← mkAppM ``ContextSlice.deepProblem #[slice, target]
  unless ← isDefEq sourceProblem expectedSource do
    throwError "internal context source problem lost premise alignment"
  unless ← isDefEq problem expectedProblem do
    throwError "internal context deep problem lost premise alignment"
  let hSource ← mkEqRefl sourceProblem
  let hProblem ← mkEqRefl problem
  let sourceProblemValue ←
    evalExpr SourcePreprocessing.Problem
      (mkConst ``SourcePreprocessing.Problem) sourceProblem
  let settingsValue ←
    evalExpr SourcePreprocessing.FirstOrderSettings
      (mkConst ``SourcePreprocessing.FirstOrderSettings) settings
  let avatarConfigValue ←
    evalExpr SourcePreprocessing.AvatarConfig
      (mkConst ``SourcePreprocessing.AvatarConfig) avatarConfig
  let labelValue ← evalExpr String (mkConst ``String) label
  let attempt ←
    match SourcePreprocessing.runFirstOrder sourceProblemValue settingsValue with
    | Except.error error =>
        pure <| KernelReplay.failureAttemptExpr goal error.label
    | Except.ok firstOrder =>
        match firstOrder.result.runAvatar? avatarConfigValue with
        | Except.error error =>
            pure <| KernelReplay.failureAttemptExpr goal error.label
        | Except.ok artifact =>
            let settingsExpr := toExpr settingsValue.toSettings
            let replay ←
              KernelReplay.firstOrderReplayExprs sourceProblem problem
                settingsExpr firstOrder.result.checked.payload artifact
                labelValue
            mkAppM ``ContextSlice.goalAttemptFromReplay
              #[slice, target, sourceProblem, problem, hSource, hProblem,
                replay.payload, replay.search, replay.checked, label,
                replay.data]
  return some attempt

/-- provider 常量保持安全；编译期元层运行使用闭合数据求值实现。 -/
@[implemented_by buildContextAttemptImpl?]
private def buildContextAttempt?
    (_request : ProveAutoRequest.PreparedContextRequest) :
    MetaM (Option Expr) :=
  pure none

/-- 纯集合论局部定理 provider。 -/
def contextProvider : ProveAutoRequest.ContextProvider where
  priority := 200
  preparation := .providerManaged
  build? := buildContextAttempt?

register_prove_auto_context_provider contextProvider

end Automation
end SetTheory
end YesMetaZFC
