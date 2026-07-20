import YesMetaZFC.Automation.CoreNormalForm.FirstOrderProjectionSoundness
import YesMetaZFC.Automation.LazyDefinitionRegistry
import YesMetaZFC.Automation.Avatar
import YesMetaZFC.Automation.HORefutationProvider

/-!
# 新主线整问题 source preprocessing 入口

本模块替换旧 `Preprocess.run` / `ScopeNormalization.run` / `Clausification.run` 入口。
一次调用先把有限前提和目标否定合成单个 refutation source，再统一完成：

1. core normal form；
2. dependency-driven anti-prenex / mini-scoping；
3. 局部 Skolem 化；
4. 保留等词可见性的定义性 CNF。
5. 共享一次 first-order projection 状态；
6. 直接材料化 `ClauseProblem.initialClauses`。

整个问题只运行一个 checked preprocessing payload，因此 fresh variable、Skolem、
定义谓词和投影符号状态不会按 premise 重置。
-/

namespace YesMetaZFC
namespace Automation
namespace SourcePreprocessing

universe x

abbrev Settings := CoreSyntax.NormalForm.CheckedPreprocessing.Settings
abbrev Checked := CoreSyntax.NormalForm.CheckedPreprocessing.Checked
abbrev Payload := CoreSyntax.NormalForm.CheckedPreprocessing.Payload
abbrev Clause := CoreSyntax.NormalForm.Clause
abbrev ClauseSet := CoreSyntax.NormalForm.ClauseSet
abbrev SearchClause := CoreSyntax.Search.Clause
abbrev SearchInput := SearchMaterialization.SearchCertificateProvider.Input
abbrev PreprocessedSearchInput :=
  SearchMaterialization.SearchCertificateProvider.PreprocessedSearchInput
abbrev PreprocessedInput :=
  SearchMaterialization.SearchCertificateProvider.PreprocessedInput
abbrev PreprocessedInputAt :=
  SearchMaterialization.SearchCertificateProvider.PreprocessedInputAt.{x}
abbrev DeepProblem := SearchMaterialization.DeepProblem
abbrev ClauseProblem := SearchMaterialization.ClauseProblem
abbrev Dependency := CoreSyntax.NormalForm.AntiPrenex.Dependency
abbrev AvatarConfig := Avatar.Config
abbrev HOAvatarConfig := HOAvatar.Config

/--
纯一阶 source 的预处理配置。

normalization 固定为恒等配置；调用方只配置后续 anti-prenex、Skolem 和定义性 CNF，
从类型边界上排除对 FOOL/lambda 合同的隐式依赖。
-/
structure FirstOrderSettings where
  antiPrenex : CoreSyntax.NormalForm.AntiPrenex.Config := {}
  localSkolem : CoreSyntax.NormalForm.LocalSkolem.Config := {}
  definitionalCnf : CoreSyntax.NormalForm.DefinitionalCnf.Config := {}
  lazyDefinitions : LazyDefinitionRegistry.Policy := {}
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace FirstOrderSettings

/-- 降到公共 checked preprocessing 配置。 -/
def toSettings (settings : FirstOrderSettings) : Settings := {
  normalForm := CoreSyntax.NormalForm.Config.firstOrderIdentity
  antiPrenex := settings.antiPrenex
  localSkolem := settings.localSkolem
  definitionalCnf := settings.definitionalCnf
}

end FirstOrderSettings

/-- 原生初始字句问题由唯一的 initial table 外延确定。 -/
theorem clauseProblem_eq_of_initialClauses_eq
    (left right : ClauseProblem)
    (h : left.initialClauses = right.initialClauses) :
    left = right := by
  cases left
  cases right
  cases h
  rfl

/-- core 预处理器消费的有限问题。 -/
structure Problem where
  premises : List CoreSyntax.Formula := []
  target : CoreSyntax.Formula
  deriving Repr, Lean.ToExpr

namespace Problem

/-- 把全部前提与目标否定组装成唯一的 refutation source。 -/
def refutationSource (problem : Problem) : CoreSyntax.Formula :=
  CoreSyntax.Formula.conjunctionList
    (problem.premises ++ [CoreSyntax.Formula.neg problem.target])

end Problem

/-- 一个完整的 universe-polymorphic core refutation model witness。 -/
structure CoreCountermodelAt (sourceProblem : Problem) where
  model : CoreSyntax.NormalForm.Semantics.Model.{x}
  contract : CoreSyntax.NormalForm.Semantics.FoolLambdaContract model
  env : CoreSyntax.NormalForm.Semantics.Env model
  respectsFree : CoreSyntax.NormalForm.Semantics.Env.RespectsFree env
  satisfies :
    CoreSyntax.NormalForm.Semantics.Formula.Satisfies
      env sourceProblem.refutationSource

/-- 现有 provider 使用的零 universe core 反模型。 -/
abbrev CoreCountermodel (sourceProblem : Problem) :=
  CoreCountermodelAt.{0} sourceProblem

/-- 纯一阶 source 的反模型只要求函数解释保持 codomain sort。 -/
structure FirstOrderCountermodelAt (sourceProblem : Problem) where
  model : CoreSyntax.NormalForm.Semantics.Model.{x}
  functionSort :
    ∀ symbol arguments,
      model.sortInterp symbol.outputSort
        (model.functionInterp symbol arguments)
  env : CoreSyntax.NormalForm.Semantics.Env model
  respectsFree : CoreSyntax.NormalForm.Semantics.Env.RespectsFree env
  satisfies :
    CoreSyntax.NormalForm.Semantics.Formula.Satisfies
      env sourceProblem.refutationSource

/-- 现有 provider 使用的零 universe 纯一阶反模型。 -/
abbrev FirstOrderCountermodel (sourceProblem : Problem) :=
  FirstOrderCountermodelAt.{0} sourceProblem

/--
公式问题与 core source problem 之间的显式反模型桥。

桥只负责把 deep problem 的反模型解释成 core refutation source；后续 Skolem、定义性 CNF、
canonical clause validity 全部由 checked preprocessing soundness 机械完成。
-/
structure ProblemBridgeAt (sourceProblem : Problem)
    (problem : DeepProblem) : Prop where
  coreCountermodel :
    ∀ {M : LogicSoundness.SetLevel.StructureAt.{x}
        SearchMaterialization.SearchSignature}
      (env : LogicSoundness.SetLevel.EnvAt.{x} M),
      Logic.FirstOrder.Theory.Models problem.theory env →
        ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
          Nonempty (CoreCountermodelAt.{x} sourceProblem)

/-- 现有 provider 使用的零 universe source/deep bridge。 -/
abbrev ProblemBridge (sourceProblem : Problem) (problem : DeepProblem) :=
  ProblemBridgeAt.{0} sourceProblem problem

/--
纯一阶公式问题与 core source 之间的反模型桥。

该桥不要求、也不能要求任意一阶模型携带完整的 lambda 函数空间合同。
-/
structure FirstOrderProblemBridgeAt (sourceProblem : Problem)
    (problem : DeepProblem) : Prop where
  coreCountermodel :
    ∀ {M : LogicSoundness.SetLevel.StructureAt.{x}
        SearchMaterialization.SearchSignature}
      (env : LogicSoundness.SetLevel.EnvAt.{x} M),
      Logic.FirstOrder.Theory.Models problem.theory env →
        ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
          Nonempty (FirstOrderCountermodelAt.{x} sourceProblem)

/-- 现有 provider 使用的零 universe 纯一阶 source/deep bridge。 -/
abbrev FirstOrderProblemBridge (sourceProblem : Problem) (problem : DeepProblem) :=
  FirstOrderProblemBridgeAt.{0} sourceProblem problem

/-- FO 与原生 HO 分支共享的 checked preprocessing 结果。 -/
structure CheckedResult (problem : Problem) where
  checked : Checked
  sourceIsRefutation : checked.payload.source = problem.refutationSource
  antiPrenexFreeClosed :
    CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
      checked.payload.antiPrenex.result = true

namespace CheckedResult

open CoreSyntax.NormalForm

/-- 共享结果暴露的最终 equality-visible 字句集。 -/
def clauses {problem : Problem} (result : CheckedResult problem) : ClauseSet :=
  result.checked.payload.clauses

/-- 为闭合 anti-prenex source 构造共享 Skolem/CNF 模型扩张。 -/
theorem modelExtension
    {problem : Problem} (result : CheckedResult problem)
    (M : Semantics.Model.{x}) (base : Semantics.Env M) :
    Nonempty
      (CheckedPreprocessing.ModelExtension result.checked M base) :=
  CheckedPreprocessing.modelExtension
    result.checked
      (CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed_sound
        result.antiPrenexFreeClosed)
      M base

/-- 原问题反模型在共享 payload 的 source 字段中成立。 -/
theorem sourceSatisfied_of_refutation
    {problem : Problem} (result : CheckedResult problem)
    {M : Semantics.Model.{x}} {env : Semantics.Env M}
    (hRefutation : Semantics.Formula.Satisfies env problem.refutationSource) :
    Semantics.Formula.Satisfies env result.checked.payload.source := by
  rw [result.sourceIsRefutation]
  exact hRefutation

/-- witness-aware HO-DAG 反证产物降为任意模型 universe 的语义后端成功对象。 -/
def higherOrderBackendSuccessAt
    {sourceProblem : Problem} (result : CheckedResult sourceProblem)
    {problem : DeepProblem} (bridge : ProblemBridgeAt.{x} sourceProblem problem)
    (artifact : HORefutationProvider.CheckedArtifact result.clauses)
    (label : String := "checked preprocessing + native HO superposition") :
    LogicSoundness.SetLevel.BackendSuccessAt.{x} problem where
  backend := .hoLambdaSuperposition
  phase := .replay
  cert := {
    entails := by
      intro M env hModels
      apply Classical.byContradiction
      intro hTarget
      rcases bridge.coreCountermodel env hModels hTarget with ⟨countermodel⟩
      rcases result.modelExtension countermodel.model countermodel.env with
        ⟨extension⟩
      have hSource :
          Semantics.Formula.Satisfies
            countermodel.env result.checked.payload.source :=
        result.sourceSatisfied_of_refutation countermodel.satisfies
      apply artifact.refutesCoreModel
        extension.target
        (extension.contract countermodel.contract)
        (extension.functionSort countermodel.contract)
        (extension.rebase countermodel.env)
      intro targetEnv hFree hBound
      simpa [CheckedResult.clauses] using
        extension.clausesSatisfiedTarget
          countermodel.contract countermodel.respectsFree hSource
          targetEnv hFree hBound
  }
  note := label

/-- witness-aware HO-DAG 反证产物降为现有零 universe 后端成功对象。 -/
def higherOrderBackendSuccess
    {sourceProblem : Problem} (result : CheckedResult sourceProblem)
    {problem : DeepProblem} (bridge : ProblemBridge sourceProblem problem)
    (artifact : HORefutationProvider.CheckedArtifact result.clauses)
    (label : String := "checked preprocessing + native HO superposition") :
    LogicSoundness.SetLevel.BackendSuccess problem :=
  result.higherOrderBackendSuccessAt bridge artifact label

end CheckedResult

/-- 新主线整问题 preprocessing 的 checked 批量结果。 -/
structure Result (problem : Problem) where
  checked : Checked
  sourceIsRefutation : checked.payload.source = problem.refutationSource
  antiPrenexFreeClosed :
    CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
      checked.payload.antiPrenex.result = true
  clausesProjectable :
    CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
      checked.payload.clauses = true
  searchClauses : Array SearchClause
  projectionState : CoreSyntax.NormalForm.FirstOrderProjection.State
  projectionRun :
    (CoreSyntax.NormalForm.FirstOrderProjection.projectClauseSet {}
      checked.payload.clauses)
      (CoreSyntax.NormalForm.FirstOrderProjection.initialState checked.payload.source) =
        some (searchClauses, projectionState)
  clauseProblem : ClauseProblem
  clauseProblemCanonical :
    clauseProblem.initialClauses =
      SearchMaterialization.coreClauseSet checked.payload.clauses
  materializationRun :
    searchClauses.mapM SearchMaterialization.clause =
      Except.ok clauseProblem.initialClauses
  lazyDefinitions : LazyDefinitionRegistry.Checked
  lazyDefinitionsSource :
    lazyDefinitions.payload.projectionSource = checked.payload.source
  lazyDefinitionsCnf :
    lazyDefinitions.payload.cnf = checked.payload.definitionalCnf
  lazyDefinitionsClauses :
    lazyDefinitions.payload.initialClauses = searchClauses

namespace Result

open CoreSyntax.NormalForm

/-- 取出完整 checked preprocessing payload。 -/
def payload {problem : Problem} (result : Result problem) : Payload :=
  result.checked.payload

/-- 唯一的整问题 refutation source。 -/
def source {problem : Problem} (result : Result problem) : CoreSyntax.Formula :=
  result.payload.source

/-- checked preprocessing 的 source 确实是问题级 refutation source。 -/
theorem source_eq_refutationSource {problem : Problem} (result : Result problem) :
    result.source = problem.refutationSource := by
  simpa [source, payload] using result.sourceIsRefutation

/-- 交给搜索器的 equality-visible 定义性 CNF 字句集。 -/
def clauses {problem : Problem} (result : Result problem) : ClauseSet :=
  result.payload.clauses

/-- core CNF 到搜索层字句投影已经由确定性投影器复算。 -/
def searchProjectionChecked {problem : Problem} (result : Result problem) :
    (CoreSyntax.NormalForm.FirstOrderProjection.projectClauseSet {}
      result.clauses)
      (CoreSyntax.NormalForm.FirstOrderProjection.initialState result.source) =
        some (result.searchClauses, result.projectionState) :=
  result.projectionRun

/-- search clauses 已经完整、一一对应地材料化为原生 DAG 初始字句。 -/
def clauseMaterializationChecked {problem : Problem} (result : Result problem) :
    result.searchClauses.mapM SearchMaterialization.clause =
      Except.ok result.clauseProblem.initialClauses :=
  result.materializationRun

/-- 从批量结果建立持有 canonical initial table 的空 search-DAG。 -/
def searchDAG {problem : Problem} (result : Result problem) :
    SearchMaterialization.SearchDAG :=
  SearchMaterialization.SearchDAG.ofInitialClauses result.searchClauses

/-- 搜索期 lazy fold/unfold 注册表已经与本次 checked preprocessing 投影对齐。 -/
def lazyDefinitionRegistry {problem : Problem} (result : Result problem) :
    LazyDefinitionRegistry.Checked :=
  result.lazyDefinitions

@[simp]
theorem searchDAG_initialClauses {problem : Problem} (result : Result problem) :
    result.searchDAG.initialClauses = result.searchClauses :=
  rfl

/-- 预处理审计统计。 -/
def stats {problem : Problem} (result : Result problem) : Certificate.Stats :=
  result.payload.stats

/-- 定义性 CNF checker 是否确认源等词字面量仍然可见。 -/
def equalityVisible {problem : Problem} (result : Result problem) : Bool :=
  result.payload.definitionalCnf.equalityVisible

/-- 反前束前的依赖摘要直接来自整问题 checked payload。 -/
def sourceDependency {problem : Problem} (result : Result problem) : Dependency :=
  result.payload.antiPrenex.sourceDependency

/-- 反前束后的依赖摘要直接来自整问题 checked payload。 -/
def resultDependency {problem : Problem} (result : Result problem) : Dependency :=
  result.payload.antiPrenex.resultDependency

/-- checked preprocessing 的结构 soundness 骨架。 -/
def structuralSound {problem : Problem} (result : Result problem) :
    CoreSyntax.NormalForm.CheckedPreprocessing.Sound result.payload :=
  CoreSyntax.NormalForm.CheckedPreprocessing.sound result.checked

/-- 整问题 anti-prenex payload 已由总 checker 验证，依赖摘要不会在批量入口丢失。 -/
theorem antiPrenexChecked {problem : Problem} (result : Result problem) :
    CoreSyntax.NormalForm.AntiPrenexPayload.check result.payload.antiPrenex = true := by
  have hPhases := result.structuralSound.phasesChecked
  simp only [CoreSyntax.NormalForm.CheckedPreprocessing.Payload.phaseCheck,
    Bool.and_eq_true_iff] at hPhases
  exact hPhases.1.1.2

/--
整问题 refutation source 在同一合同模型和环境中，当且仅当 anti-prenex 输出成立。
-/
theorem satisfies_refutationSource_iff_antiPrenexResult
    {problem : Problem} (result : Result problem) {M : Semantics.Model.{x}}
    (contract : Semantics.FoolLambdaContract M)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) :
    Semantics.Formula.Satisfies env problem.refutationSource ↔
      Semantics.Nnf.Satisfies env result.payload.antiPrenex.result := by
  rw [← result.source_eq_refutationSource]
  exact
    CheckedPreprocessing.satisfies_source_iff_antiPrenexResult
      result.checked contract env hFree

/-- 整问题 Local Skolem trace 的共享 freshness 与依赖参数均已通过 checker。 -/
theorem localSkolemSharedStateSound
    {problem : Problem} (result : Result problem) :
    LocalSkolemPayload.SharedStateSound result.payload.localSkolem :=
  CheckedPreprocessing.localSkolem_sharedStateSound result.checked

/--
原问题反模型可扩张为满足批量 Local Skolem 输出的新模型；结论显式返回扩张证书。
-/
theorem localSkolemExtension_of_refutationModel
    {problem : Problem} (result : Result problem) {M : Semantics.Model.{x}}
    (contract : Semantics.FoolLambdaContract M)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env)
    (hRefutation :
      Semantics.Formula.Satisfies env problem.refutationSource) :
    Nonempty
      (Semantics.LocalSkolemSoundness.SoundExtension
        (LocalSkolem.initialState result.payload.antiPrenex.result)
        result.payload.localSkolem.result M env) := by
  rw [← result.source_eq_refutationSource] at hRefutation
  exact
    CheckedPreprocessing.localSkolem_soundExtension_of_source
      result.checked contract env hFree hRefutation

/-- 整问题定义性 CNF payload 已由总 checker 验证。 -/
theorem definitionalCnfChecked {problem : Problem} (result : Result problem) :
    CoreSyntax.NormalForm.DefinitionalCnfPayload.check
      result.payload.definitionalCnf = true :=
  CheckedPreprocessing.definitionalCnf_checked result.checked

/--
为闭合 anti-prenex source 构造批量 Local Skolem 与定义性 CNF 的统一环境族扩张。
-/
theorem modelExtension
    {problem : Problem} (result : Result problem)
    (M : Semantics.Model.{x}) (base : Semantics.Env M) :
    Nonempty
      (CheckedPreprocessing.ModelExtension result.checked M base) :=
  CheckedPreprocessing.modelExtension
    result.checked
      (CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed_sound
        result.antiPrenexFreeClosed)
      M base

/-- 原问题反模型可扩张为满足批量定义性 CNF 字句集的模型。 -/
theorem clausesSatisfiable_of_refutationModel
    {problem : Problem} (result : Result problem) {M : Semantics.Model.{x}}
    (contract : Semantics.FoolLambdaContract M)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env)
    (hRefutation :
    Semantics.Formula.Satisfies env problem.refutationSource) :
    Semantics.ClauseSet.Satisfiable.{x} result.payload.clauses := by
  rcases result.modelExtension M env with ⟨extension⟩
  have hSource :
      Semantics.Formula.Satisfies env result.payload.source := by
    have hSourceEq :
        result.payload.source = problem.refutationSource := by
      simpa [Result.source, Result.payload] using
        result.source_eq_refutationSource
    rw [hSourceEq]
    exact hRefutation
  exact ⟨
    extension.target,
    extension.rebase env,
    extension.clausesSatisfied contract hFree hSource env hFree
      (by intro index; rfl)⟩

/--
原问题反模型可扩张为一个使 canonical DAG 初始字句问题有效的一阶结构。
-/
theorem clauseProblemValid_of_refutationModel
    {problem : Problem} (result : Result problem) {M : Semantics.Model.{x}}
    (contract : Semantics.FoolLambdaContract M)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env)
    (hRefutation :
      Semantics.Formula.Satisfies env problem.refutationSource) :
    ∃ (target : LogicSoundness.SetLevel.StructureAt.{x}
        SearchMaterialization.SearchSignature),
      ∃ (targetEnv : LogicSoundness.SetLevel.EnvAt.{x} target),
        result.clauseProblem.Valid targetEnv := by
  rcases result.modelExtension M env with ⟨extension⟩
  have hSource :
      Semantics.Formula.Satisfies env result.payload.source := by
    have hSourceEq :
        result.payload.source = problem.refutationSource := by
      simpa [Result.source, Result.payload] using
        result.source_eq_refutationSource
    rw [hSourceEq]
    exact hRefutation
  let functionSort := extension.functionSort contract
  let target :=
    SearchMaterialization.CoreProjectionSoundness.searchStructure
      extension.target functionSort
  let targetBase :=
    SearchMaterialization.CoreProjectionSoundness.searchEnv
      functionSort (extension.rebase env) (extension.respectsFree hFree)
  have hCanonical :
      (DAGCertificate.ClauseProblem.mk
        (SearchMaterialization.coreClauseSet result.payload.clauses)).Valid
          targetBase := by
    apply SearchMaterialization.CoreProjectionSoundness.coreClauseSet_valid
      functionSort (extension.rebase env) (extension.respectsFree hFree)
      result.payload.clauses result.clausesProjectable
    intro targetEnv hTargetFree hTargetBound
    exact extension.clausesSatisfiedTarget contract hFree hSource
      targetEnv hTargetFree hTargetBound
  have hValid : result.clauseProblem.Valid targetBase := by
    have hProblem :
        result.clauseProblem =
          DAGCertificate.ClauseProblem.mk
            (SearchMaterialization.coreClauseSet result.payload.clauses) :=
      clauseProblem_eq_of_initialClauses_eq _ _
        result.clauseProblemCanonical
    rw [hProblem]
    exact hCanonical
  exact ⟨target, targetBase, hValid⟩

/--
恒等 normalization 的纯一阶反模型可扩张为 canonical DAG 初始字句问题的模型。
-/
theorem clauseProblemValid_of_firstOrderRefutationModel
    {problem : Problem} (result : Result problem)
    (hNormalized :
      result.payload.normalized = result.payload.source)
    {M : Semantics.Model.{x}}
    (hFunctionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort
          (M.functionInterp symbol arguments))
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env)
    (hRefutation :
      Semantics.Formula.Satisfies env problem.refutationSource) :
    ∃ (target : LogicSoundness.SetLevel.StructureAt.{x}
        SearchMaterialization.SearchSignature),
      ∃ (targetEnv : LogicSoundness.SetLevel.EnvAt.{x} target),
        result.clauseProblem.Valid targetEnv := by
  rcases result.modelExtension M env with ⟨extension⟩
  have hSource :
      Semantics.Formula.Satisfies env result.payload.source := by
    have hSourceEq :
        result.payload.source = problem.refutationSource := by
      simpa [Result.source, Result.payload] using
        result.source_eq_refutationSource
    rw [hSourceEq]
    exact hRefutation
  let functionSort := extension.functionSort_of hFunctionSort
  let target :=
    SearchMaterialization.CoreProjectionSoundness.searchStructure
      extension.target functionSort
  let targetBase :=
    SearchMaterialization.CoreProjectionSoundness.searchEnv
      functionSort (extension.rebase env) (extension.respectsFree hFree)
  have hCanonical :
      (DAGCertificate.ClauseProblem.mk
        (SearchMaterialization.coreClauseSet result.payload.clauses)).Valid
          targetBase := by
    apply SearchMaterialization.CoreProjectionSoundness.coreClauseSet_valid
      functionSort (extension.rebase env) (extension.respectsFree hFree)
      result.payload.clauses result.clausesProjectable
    intro targetEnv hTargetFree hTargetBound
    exact extension.clausesSatisfiedTarget_of_normalized_eq
      hNormalized hSource targetEnv hTargetFree hTargetBound
  have hValid : result.clauseProblem.Valid targetBase := by
    have hProblem :
        result.clauseProblem =
          DAGCertificate.ClauseProblem.mk
            (SearchMaterialization.coreClauseSet result.payload.clauses) :=
      clauseProblem_eq_of_initialClauses_eq _ _
        result.clauseProblemCanonical
    rw [hProblem]
    exact hCanonical
  exact ⟨target, targetBase, hValid⟩

/-- 显式 source/deep bridge 与预处理 soundness 合成为同 universe validity bridge。 -/
theorem refutationBridgeAt
    {sourceProblem : Problem} (result : Result sourceProblem)
    {problem : DeepProblem} (bridge : ProblemBridgeAt.{x} sourceProblem problem) :
    SearchMaterialization.SearchCertificateProvider.RefutationBridgeAt.{x}
      problem result.clauseProblem := by
  constructor
  intro M env hModels hTarget
  rcases bridge.coreCountermodel env hModels hTarget with ⟨countermodel⟩
  exact result.clauseProblemValid_of_refutationModel
    countermodel.contract countermodel.env countermodel.respectsFree
      countermodel.satisfies

/-- 零 universe source/deep bridge 与预处理 soundness 合成。 -/
theorem refutationBridge
    {sourceProblem : Problem} (result : Result sourceProblem)
    {problem : DeepProblem} (bridge : ProblemBridge sourceProblem problem) :
    SearchMaterialization.SearchCertificateProvider.RefutationBridge
      problem result.clauseProblem :=
  result.refutationBridgeAt bridge

/-- 完整构造审计通过时，批量结果中的等词可见性标记为真。 -/
theorem equalityVisible_eq_true_of_auditCheck
    {problem : Problem} (result : Result problem)
    (hAudit :
      CoreSyntax.NormalForm.DefinitionalCnfPayload.auditCheck
        result.payload.definitionalCnf = true) :
    result.equalityVisible = true := by
  have hRest := (Bool.and_eq_true_iff.mp hAudit).2
  exact (Bool.and_eq_true_iff.mp hRest).1

/-- 把 checked source preprocessing 结果组装成 proof-free DAG 搜索输入。 -/
def toProviderSearchInput {sourceProblem : Problem} (result : Result sourceProblem)
    (problem : DeepProblem)
    (search? : Option SearchInput := none)
    (label : String := "checked source preprocessing") :
    PreprocessedSearchInput := {
  problem := problem
  clauseProblem := result.clauseProblem
  preprocessing := result.checked
  search? := search?
  label := label
}

/-- 把 checked source preprocessing 结果和同 universe 反模型 bridge 组装成 provider 输入。 -/
def toProviderInputAt {sourceProblem : Problem} (result : Result sourceProblem)
    (problem : DeepProblem) (bridge : ProblemBridgeAt.{x} sourceProblem problem)
    (search? : Option SearchInput := none)
    (label : String := "checked source preprocessing") : PreprocessedInputAt.{x} := {
  search := result.toProviderSearchInput problem search? label
  bridge := result.refutationBridgeAt bridge
}

/-- 把 checked source preprocessing 结果和零 universe 反模型 bridge 组装成 provider 输入。 -/
def toProviderInput {sourceProblem : Problem} (result : Result sourceProblem)
    (problem : DeepProblem) (bridge : ProblemBridge sourceProblem problem)
    (search? : Option SearchInput := none)
    (label : String := "checked source preprocessing") : PreprocessedInput :=
  result.toProviderInputAt problem bridge search? label

/-- 预处理结果运行 AVATAR 后保留的搜索与证书材料化产物。 -/
structure AvatarRunArtifact where
  run : Avatar.RunResult
  dag : SearchMaterialization.SearchDAG
  root : SearchMaterialization.ClauseInfo

namespace AvatarRunArtifact

/-- AVATAR 产物降为预处理 provider 消费的 search-DAG 输入。 -/
def toSearchInput (artifact : AvatarRunArtifact)
    (label : String := "checked preprocessing + AVATAR") : SearchInput :=
  {
    dag := artifact.dag
    root? := some artifact.root.id
    label := label
  }

end AvatarRunArtifact

/-- AVATAR 非 UNSAT 搜索结果对应的结构化诊断。 -/
private def avatarOutcomeDiagnostic (run : Avatar.RunResult) :
    Certificate.Diagnostic :=
  let failure := Certificate.Diagnostic.ofMessage .composite .saturation
  match run.search.outcome with
  | .unsat =>
      failure
        "internal error: AVATAR UNSAT outcome reached the failure diagnostic"
  | .model _ =>
      failure
        (s!"AVATAR found a model after {run.search.theoryRounds} theory rounds")
  | .limitExhausted snapshot =>
      failure
        (s!"AVATAR CDCL exhausted its search limit " ++
          s!"(level={snapshot.level}, clauses={snapshot.clauses}, " ++
          s!"learned={snapshot.learned})")
  | .invariantViolation message snapshot =>
      failure
        (s!"AVATAR invariant violation at level {snapshot.level}: {message}")
  | .theoryUnknown message =>
      failure
        (s!"AVATAR theory search stopped after {run.search.theoryRounds} rounds: " ++
          message)

/--
把同一次 checked preprocessing 产生的共享 search clauses 直接交给 AVATAR。

只有联合搜索报告 UNSAT 且完整 SearchDAG/root 材料化通过时才返回成功产物。
-/
def runAvatar? {problem : Problem} (result : Result problem)
    (config : AvatarConfig := {}) :
    Except Certificate.Diagnostic AvatarRunArtifact :=
  let run :=
    Avatar.runWithLazyDefinitions config result.lazyDefinitionRegistry
  match run.search.outcome with
  | .unsat => do
      let (dag, root) ← run.searchDAG? config
      pure { run := run, dag := dag, root := root }
  | _ =>
      throw (avatarOutcomeDiagnostic run)

/--
已完成 preprocessing 的结果直接运行 AVATAR，并进入 universe-polymorphic provider。
-/
def runAvatarProviderAt {sourceProblem : Problem}
    (result : Result sourceProblem) (problem : DeepProblem)
    (bridge : ProblemBridgeAt.{x} sourceProblem problem)
    (config : AvatarConfig := {})
    (label : String := "checked preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  match result.runAvatar? config with
  | Except.ok artifact =>
      SearchMaterialization.SearchCertificateProvider.runPreprocessedMatchedAt
        (result.toProviderInputAt problem bridge
          (some (artifact.toSearchInput label)) label)
  | Except.error error =>
      .failure error

/-- 已完成 preprocessing 的结果运行零 universe AVATAR provider。 -/
def runAvatarProvider {sourceProblem : Problem}
    (result : Result sourceProblem) (problem : DeepProblem)
    (bridge : ProblemBridge sourceProblem problem)
    (config : AvatarConfig := {})
    (label : String := "checked preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  result.runAvatarProviderAt problem bridge config label

end Result

/-- 纯一阶批量预处理结果额外钉住恒等 normalization 不变量。 -/
structure FirstOrderResult (problem : Problem) where
  result : Result problem
  normalizationIdentity :
    result.payload.normalized = result.payload.source

namespace FirstOrderResult

/-- 纯一阶 source/deep bridge 与 CNF soundness 合成为同 universe validity bridge。 -/
theorem refutationBridgeAt
    {sourceProblem : Problem} (firstOrder : FirstOrderResult sourceProblem)
    {problem : DeepProblem}
    (bridge : FirstOrderProblemBridgeAt.{x} sourceProblem problem) :
    SearchMaterialization.SearchCertificateProvider.RefutationBridgeAt.{x}
      problem firstOrder.result.clauseProblem := by
  constructor
  intro M env hModels hTarget
  rcases bridge.coreCountermodel env hModels hTarget with ⟨countermodel⟩
  exact firstOrder.result.clauseProblemValid_of_firstOrderRefutationModel
    firstOrder.normalizationIdentity countermodel.functionSort
      countermodel.env countermodel.respectsFree countermodel.satisfies

/-- 零 universe 纯一阶 source/deep bridge 与 CNF soundness 合成。 -/
theorem refutationBridge
    {sourceProblem : Problem} (firstOrder : FirstOrderResult sourceProblem)
    {problem : DeepProblem}
    (bridge : FirstOrderProblemBridge sourceProblem problem) :
    SearchMaterialization.SearchCertificateProvider.RefutationBridge
      problem firstOrder.result.clauseProblem :=
  firstOrder.refutationBridgeAt bridge

/-- 把纯一阶预处理结果组装成 proof-free DAG 搜索输入。 -/
def toProviderSearchInput
    {sourceProblem : Problem} (firstOrder : FirstOrderResult sourceProblem)
    (problem : DeepProblem)
    (search? : Option SearchInput := none)
    (label : String := "checked first-order preprocessing") :
    PreprocessedSearchInput := {
  problem := problem
  clauseProblem := firstOrder.result.clauseProblem
  preprocessing := firstOrder.result.checked
  search? := search?
  label := label
}

/-- 把纯一阶预处理结果和同 universe 反模型 bridge 组装成 provider 输入。 -/
def toProviderInputAt
    {sourceProblem : Problem} (firstOrder : FirstOrderResult sourceProblem)
    (problem : DeepProblem)
    (bridge : FirstOrderProblemBridgeAt.{x} sourceProblem problem)
    (search? : Option SearchInput := none)
    (label : String := "checked first-order preprocessing") :
    PreprocessedInputAt.{x} := {
  search := firstOrder.toProviderSearchInput problem search? label
  bridge := firstOrder.refutationBridgeAt bridge
}

/-- 把纯一阶预处理结果和零 universe 反模型 bridge 组装成 provider 输入。 -/
def toProviderInput
    {sourceProblem : Problem} (firstOrder : FirstOrderResult sourceProblem)
    (problem : DeepProblem)
    (bridge : FirstOrderProblemBridge sourceProblem problem)
    (search? : Option SearchInput := none)
    (label : String := "checked first-order preprocessing") :
    PreprocessedInput :=
  firstOrder.toProviderInputAt problem bridge search? label

/-- 纯一阶 checked preprocessing 结果运行同 universe AVATAR/DAG 回放。 -/
def runAvatarProviderAt
    {sourceProblem : Problem} (firstOrder : FirstOrderResult sourceProblem)
    (problem : DeepProblem)
    (bridge : FirstOrderProblemBridgeAt.{x} sourceProblem problem)
    (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  match firstOrder.result.runAvatar? config with
  | Except.ok artifact =>
      SearchMaterialization.SearchCertificateProvider.runPreprocessedMatchedAt
        (firstOrder.toProviderInputAt problem bridge
          (some (artifact.toSearchInput label)) label)
  | Except.error error =>
      .failure error

/-- 纯一阶 checked preprocessing 结果运行零 universe AVATAR/DAG 回放。 -/
def runAvatarProvider
    {sourceProblem : Problem} (firstOrder : FirstOrderResult sourceProblem)
    (problem : DeepProblem)
    (bridge : FirstOrderProblemBridge sourceProblem problem)
    (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  firstOrder.runAvatarProviderAt problem bridge config label

/-- 纯一阶 AVATAR/provider 在任意模型 universe 下的 proof-free 闭合状态。 -/
def runAvatarProviderClosedAt
    {sourceProblem : Problem} (firstOrder : FirstOrderResult sourceProblem)
    (problem : DeepProblem)
    (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") : Bool :=
  match firstOrder.result.runAvatar? config with
  | Except.ok artifact =>
      SearchMaterialization.SearchCertificateProvider.runPreprocessedClosedAt
        (firstOrder.toProviderSearchInput problem
          (some (artifact.toSearchInput label)) label)
  | Except.error _ => false

/-- 纯一阶 AVATAR/provider 在零模型 universe 下的 proof-free 闭合状态。 -/
def runAvatarProviderClosed
    {sourceProblem : Problem} (firstOrder : FirstOrderResult sourceProblem)
    (problem : DeepProblem)
    (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") : Bool :=
  runAvatarProviderClosedAt firstOrder problem config label

/-- 纯一阶 AVATAR/provider 的 proof-free 结构化摘要。 -/
def runAvatarProviderSummary
    {sourceProblem : Problem} (firstOrder : FirstOrderResult sourceProblem)
    (problem : DeepProblem)
    (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") : String :=
  match firstOrder.result.runAvatar? config with
  | Except.ok artifact =>
      SearchMaterialization.SearchCertificateProvider.runPreprocessedSummary
        (firstOrder.toProviderSearchInput problem
          (some (artifact.toSearchInput label)) label)
  | Except.error error => error.label

/-- 同 universe proof-carrying AVATAR provider 与纯计算闭合状态保持一致。 -/
theorem runAvatarProviderAt_closed
    {sourceProblem : Problem} (firstOrder : FirstOrderResult sourceProblem)
    (problem : DeepProblem)
    (bridge : FirstOrderProblemBridgeAt.{x} sourceProblem problem)
    (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.closed
        (firstOrder.runAvatarProviderAt problem bridge config label) =
      runAvatarProviderClosedAt firstOrder problem config label := by
  unfold runAvatarProviderAt runAvatarProviderClosedAt
  generalize hRun : firstOrder.result.runAvatar? config = run
  cases run with
  | error error =>
      simp [LogicSoundness.SetLevel.BackendAttemptAt.closed]
  | ok artifact =>
      simpa [hRun] using
        SearchMaterialization.SearchCertificateProvider.runPreprocessedMatchedAt_closed
          (firstOrder.toProviderInputAt problem bridge
            (some (artifact.toSearchInput label)) label)

/-- 零 universe proof-carrying AVATAR provider 与纯计算闭合状态保持一致。 -/
theorem runAvatarProvider_closed
    {sourceProblem : Problem} (firstOrder : FirstOrderResult sourceProblem)
    (problem : DeepProblem)
    (bridge : FirstOrderProblemBridge sourceProblem problem)
    (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") :
    (firstOrder.runAvatarProvider problem bridge config label).closed =
      firstOrder.runAvatarProviderClosed problem config label :=
  firstOrder.runAvatarProviderAt_closed problem bridge config label

end FirstOrderResult

/-- 新 source preprocessing checker 失败时的结构化诊断。 -/
def diagnostic (message : String) : Certificate.Diagnostic :=
  Certificate.Diagnostic.ofMessage .coreNormalForm .backendCheck message

/-- 执行一次整问题 checked preprocessing，暂不决定 FO/HO 后端。 -/
def runChecked (problem : Problem) (settings : Settings := {}) :
    Except Certificate.Diagnostic (CheckedResult problem) :=
  let source := problem.refutationSource
  let payload :=
    CoreSyntax.NormalForm.CheckedPreprocessing.Payload.build settings source
  if hChecked :
      CoreSyntax.NormalForm.CheckedPreprocessing.Payload.check payload = true then
    let checked : Checked := { payload := payload, checked := hChecked }
    if hFreeClosed :
        CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
          checked.payload.antiPrenex.result = true then
      pure {
        checked := checked
        sourceIsRefutation := rfl
        antiPrenexFreeClosed := hFreeClosed
      }
    else
      throw (diagnostic <|
        "whole-problem anti-prenex output contains free variables; uniform preprocessing " ++
          "model extension requires a free-closed refutation source")
  else
    throw (diagnostic
      "generated whole-problem preprocessing payload failed the checked normal-form pipeline")

/--
重放元层已经生成的 preprocessing payload。

这里只重新运行 payload checker 与 source/free-closed 对齐，不重新执行预处理构造器。
-/
def replayChecked (problem : Problem) (payload : Payload) :
    Except Certificate.Diagnostic (CheckedResult problem) :=
  if hChecked :
      CoreSyntax.NormalForm.CheckedPreprocessing.Payload.check payload = true then
    let checked : Checked := { payload := payload, checked := hChecked }
    if hSource :
        CoreSyntax.NormalForm.SyntaxEq.formulaEq
          checked.payload.source problem.refutationSource = true then
      if hFreeClosed :
          CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
            checked.payload.antiPrenex.result = true then
        pure {
          checked := checked
          sourceIsRefutation :=
            CoreSyntax.NormalForm.SyntaxEq.formulaEq_eq_true.mp hSource
          antiPrenexFreeClosed := hFreeClosed
        }
      else
        throw (diagnostic <|
          "replayed anti-prenex output contains free variables; uniform preprocessing " ++
            "model extension requires a free-closed refutation source")
    else
      throw (diagnostic
        "replayed preprocessing payload does not match the requested refutation source")
  else
    throw (diagnostic
      "replayed whole-problem preprocessing payload failed the checked normal-form pipeline")

/-- 共享 checked 结果进入一阶投影与 canonical DAG 初始问题。 -/
def projectFirstOrder {problem : Problem} (shared : CheckedResult problem)
    (lazyPolicy : LazyDefinitionRegistry.Policy := {}) :
    Except Certificate.Diagnostic (Result problem) :=
  if hProjectable :
      CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
        shared.checked.payload.clauses = true then
    match hProjection :
        (CoreSyntax.NormalForm.FirstOrderProjection.projectClauseSet {}
          shared.checked.payload.clauses)
          (CoreSyntax.NormalForm.FirstOrderProjection.initialState
            shared.checked.payload.source) with
    | some (searchClauses, projectionState) =>
        match hMaterialization :
            searchClauses.mapM SearchMaterialization.clause with
        | Except.ok projectedClauses =>
            let coreClauses :=
              SearchMaterialization.coreClauseSet shared.checked.payload.clauses
            if hClauses :
                SearchMaterialization.clauseArrayEq
                  projectedClauses coreClauses = true then
              have hProjectedEq : projectedClauses = coreClauses :=
                SearchMaterialization.clauseArrayEq_sound hClauses
              let lazyPayload :=
                LazyDefinitionRegistry.Payload.build
                  shared.checked.payload.source
                  shared.checked.payload.definitionalCnf searchClauses
                  lazyPolicy
              if hLazy :
                  LazyDefinitionRegistry.Payload.check lazyPayload = true then
                let lazyDefinitions : LazyDefinitionRegistry.Checked := {
                  payload := lazyPayload
                  checked := hLazy
                }
                pure {
                  checked := shared.checked
                  sourceIsRefutation := shared.sourceIsRefutation
                  antiPrenexFreeClosed := shared.antiPrenexFreeClosed
                  clausesProjectable := hProjectable
                  searchClauses := searchClauses
                  projectionState := projectionState
                  projectionRun := hProjection
                  clauseProblem := { initialClauses := coreClauses }
                  clauseProblemCanonical := rfl
                  materializationRun := by
                    simpa [hProjectedEq] using hMaterialization
                  lazyDefinitions := lazyDefinitions
                  lazyDefinitionsSource := rfl
                  lazyDefinitionsCnf := rfl
                  lazyDefinitionsClauses := rfl
                }
              else
                throw (diagnostic
                  "checked definitional CNF failed lazy fold/unfold registry alignment")
            else
              throw (diagnostic
                "search projection disagrees with direct trusted core-to-DAG materialization")
        | Except.error error => throw error
    | none =>
        throw (diagnostic
          "checked whole-problem clauses failed projection to the search clause syntax")
  else
    throw (diagnostic <|
      "checked whole-problem clauses retain bound, FOOL, or lambda terms outside " ++
        "the proved first-order projection fragment")

/-- 执行整问题 checked preprocessing，并直接得到一阶初始字句问题。 -/
def run (problem : Problem) (settings : Settings := {})
    (lazyPolicy : LazyDefinitionRegistry.Policy := {}) :
    Except Certificate.Diagnostic (Result problem) := do
  let shared ← runChecked problem settings
  projectFirstOrder shared lazyPolicy

/--
执行纯一阶整问题预处理。

除公共 checker 外再次复核 `normalized = source`，确保该入口不会因配置漂移静默重新引入
FOOL/lambda 语义前提。
-/
def runFirstOrder (problem : Problem)
    (settings : FirstOrderSettings := {}) :
    Except Certificate.Diagnostic (FirstOrderResult problem) := do
  let result ← run problem settings.toSettings
    settings.lazyDefinitions
  if hIdentity :
      CoreSyntax.NormalForm.SyntaxEq.formulaEq
        result.payload.normalized result.payload.source = true then
    pure {
      result := result
      normalizationIdentity :=
        CoreSyntax.NormalForm.SyntaxEq.formulaEq_eq_true.mp hIdentity
    }
  else
    throw (diagnostic
      "pure first-order preprocessing changed the source during normalization")

/--
从元层生成的纯数据 payload 重建一阶 checked 结果。

重放仍会执行 preprocessing、投影、材料化与 lazy registry checker，但不会再次运行
normalization/Skolem/CNF 构造器。
-/
def replayFirstOrder (problem : Problem) (payload : Payload)
    (settings : FirstOrderSettings := {}) :
    Except Certificate.Diagnostic (FirstOrderResult problem) := do
  let shared ← replayChecked problem payload
  let result ← projectFirstOrder shared settings.lazyDefinitions
  if hIdentity :
      CoreSyntax.NormalForm.SyntaxEq.formulaEq
        result.payload.normalized result.payload.source = true then
    pure {
      result := result
      normalizationIdentity :=
        CoreSyntax.NormalForm.SyntaxEq.formulaEq_eq_true.mp hIdentity
    }
  else
    throw (diagnostic
      "replayed pure first-order preprocessing changed the source during normalization")

/--
已完成搜索的纯一阶 replay 只需要的 checked preprocessing 语义核心。

projection state 与 lazy registry 负责生成搜索 DAG；DAG 已生成后，可信回放只需确认
canonical core clause problem 与 source preprocessing 语义。
-/
structure FirstOrderReplay (problem : Problem) where
  payload : Payload
  checked : CoreSyntax.NormalForm.CheckedPreprocessing.Payload.check payload = true
  sourceIsRefutation : payload.source = problem.refutationSource
  antiPrenexFreeClosed :
    CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
      payload.antiPrenex.result = true
  clausesProjectable :
    CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
      payload.clauses = true
  normalizationIdentity : payload.normalized = payload.source

namespace FirstOrderReplay

open CoreSyntax.NormalForm

/-- 固定 SearchSignature 的父字句快照数组 checker。 -/
def searchParentSnapshotsChecked (dag : SearchMaterialization.DAG) : Bool :=
  dag.parentSnapshotsChecked

/-- 固定 SearchSignature 的父字句快照列表 checker。 -/
def searchParentSnapshotsListChecked (dag : SearchMaterialization.DAG) : Bool :=
  dag.parentSnapshotsListChecked

/-- 固定 SearchSignature 的父字句快照列表 checker 合成。 -/
theorem searchParentSnapshotsChecked_eq_true_of_listCheck
    (dag : SearchMaterialization.DAG)
    (checked : searchParentSnapshotsListChecked dag = true) :
    searchParentSnapshotsChecked dag = true :=
  DAGCertificate.DAG.parentSnapshotsChecked_eq_true_of_listCheck dag checked

/-- 固定 SearchSignature 的 guard 数组 checker。 -/
def searchGuardsChecked (dag : SearchMaterialization.DAG) : Bool :=
  dag.guardsChecked

/-- 固定 SearchSignature 的 guard 列表 checker。 -/
def searchGuardsListChecked (dag : SearchMaterialization.DAG) : Bool :=
  dag.guardsListChecked

/-- 固定 SearchSignature 的 guard 列表 checker 合成。 -/
theorem searchGuardsChecked_eq_true_of_listCheck
    (dag : SearchMaterialization.DAG)
    (checked : searchGuardsListChecked dag = true) :
    searchGuardsChecked dag = true :=
  DAGCertificate.DAG.guardsChecked_eq_true_of_listCheck dag checked

/-- 固定 SearchSignature 的八个命名结构检查合成整张 DAG checker。 -/
theorem searchDagCheck_eq_true_of_components
    (dag : SearchMaterialization.DAG)
    (hRootExists : dag.rootExists = true)
    (hRootClosed : dag.rootClosed = true)
    (hDenseIds : dag.denseIds = true)
    (hParentsBefore : dag.parentsBefore = true)
    (hPayloadsChecked : dag.payloadsChecked = true)
    (hParentSnapshotsChecked : searchParentSnapshotsChecked dag = true)
    (hGuardsChecked : searchGuardsChecked dag = true)
    (hSourceIndicesUnique : dag.sourceIndicesUnique = true) :
    dag.check = true :=
  DAGCertificate.DAG.check_eq_true_of_components dag
    hRootExists hRootClosed hDenseIds hParentsBefore hPayloadsChecked
    hParentSnapshotsChecked hGuardsChecked hSourceIndicesUnique

/-- 纯一阶 replay 的全部 kernel-checkable 前置条件。 -/
def check (problem : Problem) (payload : Payload) : Bool :=
  CoreSyntax.NormalForm.CheckedPreprocessing.Payload.check payload &&
    (CoreSyntax.NormalForm.SyntaxEq.formulaEq
      payload.source problem.refutationSource &&
      (CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
        payload.antiPrenex.result &&
        (CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
          payload.clauses &&
          CoreSyntax.NormalForm.SyntaxEq.formulaEq
            payload.normalized payload.source)))

/-- 六个预处理阶段 checker 的独立等式证明合成公共 phase checker。 -/
theorem phaseCheck_eq_true_of_components
    (payload : Payload)
    (hSource : payload.source.check? = true)
    (hNormalized : payload.normalized.check? = true)
    (hTrace :
      CoreSyntax.NormalForm.Trace.check
        payload.settings.normalForm payload.normalizationTrace = true)
    (hAntiPrenex :
      CoreSyntax.NormalForm.AntiPrenexPayload.check payload.antiPrenex = true)
    (hLocalSkolem :
      CoreSyntax.NormalForm.LocalSkolemPayload.check payload.localSkolem = true)
    (hDefinitionalCnf :
      CoreSyntax.NormalForm.DefinitionalCnfPayload.check
        payload.definitionalCnf = true) :
    CoreSyntax.NormalForm.CheckedPreprocessing.Payload.phaseCheck payload = true := by
  have hSyntax :
      (payload.source.check? && payload.normalized.check?) = true :=
    Bool.and_eq_true_iff.mpr ⟨hSource, hNormalized⟩
  have hTracePrefix :
      (payload.source.check? && payload.normalized.check? &&
          CoreSyntax.NormalForm.Trace.check
            payload.settings.normalForm payload.normalizationTrace) = true :=
    Bool.and_eq_true_iff.mpr ⟨hSyntax, hTrace⟩
  have hAntiPrenexPrefix :
      (payload.source.check? && payload.normalized.check? &&
          CoreSyntax.NormalForm.Trace.check
            payload.settings.normalForm payload.normalizationTrace &&
          CoreSyntax.NormalForm.AntiPrenexPayload.check payload.antiPrenex) = true :=
    Bool.and_eq_true_iff.mpr ⟨hTracePrefix, hAntiPrenex⟩
  have hLocalSkolemPrefix :
      (payload.source.check? && payload.normalized.check? &&
          CoreSyntax.NormalForm.Trace.check
            payload.settings.normalForm payload.normalizationTrace &&
          CoreSyntax.NormalForm.AntiPrenexPayload.check payload.antiPrenex &&
          CoreSyntax.NormalForm.LocalSkolemPayload.check payload.localSkolem) = true :=
    Bool.and_eq_true_iff.mpr ⟨hAntiPrenexPrefix, hLocalSkolem⟩
  exact Bool.and_eq_true_iff.mpr ⟨hLocalSkolemPrefix, hDefinitionalCnf⟩

/-- 各命名 checker 的独立等式证明合成完整一阶 replay 边界。 -/
theorem check_eq_true_of_components
    (problem : Problem) (payload : Payload)
    (hPhase :
      CoreSyntax.NormalForm.CheckedPreprocessing.Payload.phaseCheck payload = true)
    (hLink :
      CoreSyntax.NormalForm.CheckedPreprocessing.Payload.linkCheck payload = true)
    (hSource :
      CoreSyntax.NormalForm.SyntaxEq.formulaEq
        payload.source problem.refutationSource = true)
    (hFree :
      CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
        payload.antiPrenex.result = true)
    (hProjectable :
      CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
        payload.clauses = true)
    (hNormalization :
      CoreSyntax.NormalForm.SyntaxEq.formulaEq
        payload.normalized payload.source = true) :
    check problem payload = true := by
  have hPayload :
      CoreSyntax.NormalForm.CheckedPreprocessing.Payload.check payload = true := by
    exact Bool.and_eq_true_iff.mpr ⟨hPhase, hLink⟩
  exact Bool.and_eq_true_iff.mpr
    ⟨hPayload, Bool.and_eq_true_iff.mpr
      ⟨hSource, Bool.and_eq_true_iff.mpr
        ⟨hFree, Bool.and_eq_true_iff.mpr ⟨hProjectable, hNormalization⟩⟩⟩⟩

/-- checker 为真时构造最小 replay 语义核心。 -/
def ofCheck (problem : Problem) (payload : Payload)
    (hCheck : check problem payload = true) : FirstOrderReplay problem := by
  have hOuter := Bool.and_eq_true_iff.mp hCheck
  have hSource := Bool.and_eq_true_iff.mp hOuter.2
  have hFree := Bool.and_eq_true_iff.mp hSource.2
  have hProjectable := Bool.and_eq_true_iff.mp hFree.2
  exact {
    payload := payload
    checked := hOuter.1
    sourceIsRefutation :=
      CoreSyntax.NormalForm.SyntaxEq.formulaEq_eq_true.mp hSource.1
    antiPrenexFreeClosed := hFree.1
    clausesProjectable := hProjectable.1
    normalizationIdentity :=
      CoreSyntax.NormalForm.SyntaxEq.formulaEq_eq_true.mp hProjectable.2
  }

/-- replay payload 重新包装为公共 checked preprocessing。 -/
def checkedPayload {problem : Problem} (replay : FirstOrderReplay problem) : Checked := {
  payload := replay.payload
  checked := replay.checked
}

/-- replay 直接消费的 canonical DAG 初始字句问题。 -/
@[reducible] def clauseProblemOf (payload : Payload) : ClauseProblem :=
  {
    initialClauses :=
      SearchMaterialization.ReplayCoreProjection.clauseSet payload.clauses
  }

/-- 当前 replay 的 canonical DAG 初始字句问题。 -/
def clauseProblem {problem : Problem} (replay : FirstOrderReplay problem) : ClauseProblem :=
  clauseProblemOf replay.payload

/-- free-closed checked preprocessing 构造统一模型扩张。 -/
theorem modelExtension
    {problem : Problem} (replay : FirstOrderReplay problem)
    (M : Semantics.Model.{x}) (base : Semantics.Env M) :
    Nonempty
      (CheckedPreprocessing.ModelExtension replay.checkedPayload M base) :=
  CheckedPreprocessing.modelExtension
    replay.checkedPayload
    (CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed_sound
      replay.antiPrenexFreeClosed)
    M base

/-- 恒等 normalization 的 replay 反模型产生 canonical DAG 初始字句模型。 -/
theorem clauseProblemValid_of_firstOrderRefutationModel
    {problem : Problem} (replay : FirstOrderReplay problem)
    {M : Semantics.Model.{x}}
    (hFunctionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort
          (M.functionInterp symbol arguments))
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env)
    (hRefutation :
      Semantics.Formula.Satisfies env problem.refutationSource) :
    ∃ (target : LogicSoundness.SetLevel.StructureAt.{x}
        SearchMaterialization.SearchSignature),
      ∃ (targetEnv : LogicSoundness.SetLevel.EnvAt.{x} target),
        replay.clauseProblem.Valid targetEnv := by
  rcases replay.modelExtension M env with ⟨extension⟩
  have hSource :
      Semantics.Formula.Satisfies env replay.payload.source := by
    rw [replay.sourceIsRefutation]
    exact hRefutation
  let functionSort := extension.functionSort_of hFunctionSort
  let target :=
    SearchMaterialization.CoreProjectionSoundness.searchStructure
      extension.target functionSort
  let targetBase :=
    SearchMaterialization.CoreProjectionSoundness.searchEnv
      functionSort (extension.rebase env) (extension.respectsFree hFree)
  have hCanonical : replay.clauseProblem.Valid targetBase := by
    change
      (DAGCertificate.ClauseProblem.mk
        (SearchMaterialization.ReplayCoreProjection.clauseSet
          replay.payload.clauses)).Valid targetBase
    rw [SearchMaterialization.ReplayCoreProjection.clauseSet_eq_coreClauseSet]
    apply SearchMaterialization.CoreProjectionSoundness.coreClauseSet_valid
      functionSort (extension.rebase env) (extension.respectsFree hFree)
      replay.payload.clauses replay.clausesProjectable
    intro targetEnv hTargetFree hTargetBound
    exact extension.clausesSatisfiedTarget_of_normalized_eq
      replay.normalizationIdentity hSource targetEnv hTargetFree hTargetBound
  exact ⟨target, targetBase, hCanonical⟩

/-- 最小 replay 语义核心与 host 一阶 bridge 合成同 universe validity bridge。 -/
theorem refutationBridgeAt
    {sourceProblem : Problem} (replay : FirstOrderReplay sourceProblem)
    {problem : DeepProblem}
    (bridge : FirstOrderProblemBridgeAt.{x} sourceProblem problem) :
    SearchMaterialization.SearchCertificateProvider.RefutationBridgeAt.{x}
      problem replay.clauseProblem := by
  constructor
  intro M env hModels hTarget
  rcases bridge.coreCountermodel env hModels hTarget with ⟨countermodel⟩
  exact replay.clauseProblemValid_of_firstOrderRefutationModel
    countermodel.functionSort countermodel.env countermodel.respectsFree
      countermodel.satisfies

/-- 零模型 universe 的最小 replay validity bridge。 -/
theorem refutationBridge
    {sourceProblem : Problem} (replay : FirstOrderReplay sourceProblem)
    {problem : DeepProblem}
    (bridge : FirstOrderProblemBridge sourceProblem problem) :
    SearchMaterialization.SearchCertificateProvider.RefutationBridge
      problem replay.clauseProblem :=
  replay.refutationBridgeAt bridge

/-- 纯 replay search terminal 输入。 -/
def searchInput (payload : Payload) (problem : DeepProblem)
    (search : SearchInput)
    (label : String := "replayed first-order preprocessing + AVATAR") :
    SearchMaterialization.SearchCertificateProvider.ReplaySearchInput := {
  problem := problem
  clauseProblem := clauseProblemOf payload
  search? := some search
  label := label
}

end FirstOrderReplay

/-- 给定元层搜索 DAG，重放纯一阶 preprocessing、材料化与 checked soundness。 -/
def replayFirstOrderProviderAt
    (sourceProblem : Problem) (payload : Payload)
    (problem : DeepProblem)
    (bridge : FirstOrderProblemBridgeAt.{x} sourceProblem problem)
    (search : SearchInput)
    (_settings : FirstOrderSettings := {})
    (label : String := "replayed first-order preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  if hReplay : FirstOrderReplay.check sourceProblem payload = true then
    let replay := FirstOrderReplay.ofCheck sourceProblem payload hReplay
    SearchMaterialization.SearchCertificateProvider.runReplayMatchedAt
      (FirstOrderReplay.searchInput payload problem search label)
      (replay.refutationBridgeAt bridge)
  else
    .failure <| diagnostic
      "replayed first-order payload failed the kernel-checkable semantic boundary"

/-- 给定元层搜索 DAG 的现有零 universe 一阶 checked 重放。 -/
def replayFirstOrderProvider
    (sourceProblem : Problem) (payload : Payload)
    (problem : DeepProblem)
    (bridge : FirstOrderProblemBridge sourceProblem problem)
    (search : SearchInput)
    (settings : FirstOrderSettings := {})
    (label : String := "replayed first-order preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  replayFirstOrderProviderAt
    sourceProblem payload problem bridge search settings label

/-- 给定元层搜索 DAG 时，一阶 checked 重放的 proof-free 闭合状态。 -/
def replayFirstOrderProviderClosedAt
    (sourceProblem : Problem) (payload : Payload)
    (problem : DeepProblem)
    (search : SearchInput)
    (_settings : FirstOrderSettings := {})
    (label : String := "replayed first-order preprocessing + AVATAR") : Bool :=
  FirstOrderReplay.check sourceProblem payload &&
    SearchMaterialization.SearchCertificateProvider.runReplayClosed
      (FirstOrderReplay.searchInput payload problem search label)

/-- 给定元层搜索 DAG 时，零模型 universe 的 proof-free 闭合状态。 -/
def replayFirstOrderProviderClosed
    (sourceProblem : Problem) (payload : Payload)
    (problem : DeepProblem)
    (search : SearchInput)
    (settings : FirstOrderSettings := {})
    (label : String := "replayed first-order preprocessing + AVATAR") : Bool :=
  replayFirstOrderProviderClosedAt
    sourceProblem payload problem search settings label

/-- 给定元层搜索 DAG 时，一阶 checked 重放的 proof-free 结构化摘要。 -/
def replayFirstOrderProviderSummary
    (sourceProblem : Problem) (payload : Payload)
    (problem : DeepProblem)
    (search : SearchInput)
    (_settings : FirstOrderSettings := {})
    (label : String := "replayed first-order preprocessing + AVATAR") : String :=
  if FirstOrderReplay.check sourceProblem payload then
    SearchMaterialization.SearchCertificateProvider.runReplaySummary
      (FirstOrderReplay.searchInput payload problem search label)
  else
    "replayed first-order payload failed the kernel-checkable semantic boundary"

/-- proof-carrying 一阶重放与 proof-free 闭合状态保持一致。 -/
theorem replayFirstOrderProviderAt_closed
    (sourceProblem : Problem) (payload : Payload)
    (problem : DeepProblem)
    (bridge : FirstOrderProblemBridgeAt.{x} sourceProblem problem)
    (search : SearchInput)
    (settings : FirstOrderSettings := {})
    (label : String := "replayed first-order preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.closed
        (replayFirstOrderProviderAt
          sourceProblem payload problem bridge search settings label) =
      replayFirstOrderProviderClosedAt
        sourceProblem payload problem search settings label := by
  unfold replayFirstOrderProviderAt replayFirstOrderProviderClosedAt
  by_cases hReplay : FirstOrderReplay.check sourceProblem payload = true
  · simp only [hReplay, Bool.true_and]
    exact
      SearchMaterialization.SearchCertificateProvider.runReplayMatchedAt_closed
        (FirstOrderReplay.searchInput payload problem search label)
        ((FirstOrderReplay.ofCheck sourceProblem payload hReplay).refutationBridgeAt bridge)
  · simp [hReplay, LogicSoundness.SetLevel.BackendAttemptAt.closed]

/-- 零模型 universe 的 proof-carrying 重放与 proof-free 闭合状态保持一致。 -/
theorem replayFirstOrderProvider_closed
    (sourceProblem : Problem) (payload : Payload)
    (problem : DeepProblem)
    (bridge : FirstOrderProblemBridge sourceProblem problem)
    (search : SearchInput)
    (settings : FirstOrderSettings := {})
    (label : String := "replayed first-order preprocessing + AVATAR") :
    (replayFirstOrderProvider
        sourceProblem payload problem bridge search settings label).closed =
      replayFirstOrderProviderClosed
        sourceProblem payload problem search settings label :=
  replayFirstOrderProviderAt_closed
    sourceProblem payload problem bridge search settings label

/-- 共享 checked 结果进入任意模型 universe 的原生 HO-AVATAR 与专用 DAG 回放。 -/
def runHigherOrderProviderAt {sourceProblem : Problem}
    (result : CheckedResult sourceProblem) (problem : DeepProblem)
    (bridge : ProblemBridgeAt.{x} sourceProblem problem)
    (config : HOAvatarConfig := {})
    (label : String := "checked preprocessing + native HO AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  if hNative :
      HOSearchMaterialization.CoreProjectionSoundness.Native.clauseSet
        result.checked.payload.clauses = true then
    match HORefutationProvider.run result.checked.payload.clauses hNative config with
    | Except.ok artifact =>
        .success (result.higherOrderBackendSuccessAt bridge artifact label)
    | Except.error error =>
        .failure error
  else
    .failure <| diagnostic
      ("checked preprocessing retains constructs or extensional-witness symbols outside " ++
        "the native apply/lam HO fragment; no sound HO projection is available")

/-- 共享 checked 结果进入现有零 universe 的原生 HO-AVATAR 与专用 DAG 回放。 -/
def runHigherOrderProvider {sourceProblem : Problem}
    (result : CheckedResult sourceProblem) (problem : DeepProblem)
    (bridge : ProblemBridge sourceProblem problem)
    (config : HOAvatarConfig := {})
    (label : String := "checked preprocessing + native HO AVATAR") :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  runHigherOrderProviderAt result problem bridge config label

/--
默认能力分流：严格一阶字句与含原生 `apply/lam` 的字句分别进入 FO/HO
AVATAR saturation/CDCL 双核；其余残留返回结构化 unsupported 诊断。模型 universe
只出现在反模型 bridge 与语义后端结果中。
-/
def runRoutedProviderAt (sourceProblem : Problem) (problem : DeepProblem)
    (bridge : ProblemBridgeAt.{x} sourceProblem problem)
    (settings : Settings := {}) (avatarConfig : AvatarConfig := {})
    (hoConfig : HOAvatarConfig := {})
    (label : String := "checked source preprocessing") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  match runChecked sourceProblem settings with
  | Except.error error =>
      .failure error
  | Except.ok shared =>
      if
          CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
            shared.checked.payload.clauses then
        match projectFirstOrder shared with
        | Except.ok firstOrder =>
            firstOrder.runAvatarProviderAt problem bridge avatarConfig
              (label ++ " / FO AVATAR")
        | Except.error error =>
            .failure error
      else
        runHigherOrderProviderAt shared problem bridge hoConfig
          (label ++ " / native HO")

/-- 默认 FO/HO 能力分流的现有零 universe 包装。 -/
def runRoutedProvider (sourceProblem : Problem) (problem : DeepProblem)
    (bridge : ProblemBridge sourceProblem problem)
    (settings : Settings := {}) (avatarConfig : AvatarConfig := {})
    (hoConfig : HOAvatarConfig := {})
    (label : String := "checked source preprocessing") :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  runRoutedProviderAt sourceProblem problem bridge settings avatarConfig hoConfig label

/-- 从整问题运行任意模型 universe 的 checked preprocessing、AVATAR 和 DAG 回放。 -/
def runAvatarProviderAt (sourceProblem : Problem) (problem : DeepProblem)
    (bridge : ProblemBridgeAt.{x} sourceProblem problem)
    (settings : Settings := {}) (config : AvatarConfig := {})
    (label : String := "checked preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  match run sourceProblem settings with
  | Except.ok result =>
      result.runAvatarProviderAt problem bridge config label
  | Except.error error =>
      .failure error

/-- 从整问题运行零 universe checked preprocessing、AVATAR 和 DAG 回放。 -/
def runAvatarProvider (sourceProblem : Problem) (problem : DeepProblem)
    (bridge : ProblemBridge sourceProblem problem)
    (settings : Settings := {}) (config : AvatarConfig := {})
    (label : String := "checked preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  runAvatarProviderAt sourceProblem problem bridge settings config label

/-- 从纯一阶整问题运行任意模型 universe 的 normalization、AVATAR 和 DAG 回放。 -/
def runFirstOrderProviderAt
    (sourceProblem : Problem) (problem : DeepProblem)
    (bridge : FirstOrderProblemBridgeAt.{x} sourceProblem problem)
    (settings : FirstOrderSettings := {})
    (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  match runFirstOrder sourceProblem settings with
  | Except.ok result =>
      result.runAvatarProviderAt problem bridge config label
  | Except.error error =>
      .failure error

/-- 从纯一阶整问题运行零 universe normalization、AVATAR 和 DAG 回放。 -/
def runFirstOrderProvider
    (sourceProblem : Problem) (problem : DeepProblem)
    (bridge : FirstOrderProblemBridge sourceProblem problem)
    (settings : FirstOrderSettings := {})
    (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  runFirstOrderProviderAt sourceProblem problem bridge settings config label

/-- 整问题纯一阶 provider 在任意模型 universe 下的 proof-free 闭合状态。 -/
def runFirstOrderProviderClosedAt
    (sourceProblem : Problem) (problem : DeepProblem)
    (settings : FirstOrderSettings := {})
    (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") : Bool :=
  match runFirstOrder sourceProblem settings with
  | Except.ok result =>
      FirstOrderResult.runAvatarProviderClosedAt
        result problem config label
  | Except.error _ => false

/-- 整问题纯一阶 provider 在零模型 universe 下的 proof-free 闭合状态。 -/
def runFirstOrderProviderClosed
    (sourceProblem : Problem) (problem : DeepProblem)
    (settings : FirstOrderSettings := {})
    (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") : Bool :=
  runFirstOrderProviderClosedAt
    sourceProblem problem settings config label

/-- 整问题纯一阶 provider 的 proof-free 结构化摘要。 -/
def runFirstOrderProviderSummary
    (sourceProblem : Problem) (problem : DeepProblem)
    (settings : FirstOrderSettings := {})
    (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") : String :=
  match runFirstOrder sourceProblem settings with
  | Except.ok result =>
      result.runAvatarProviderSummary problem config label
  | Except.error error => error.label

/-- 整问题纯一阶 provider 的同 universe proof-carrying 与纯计算闭合状态一致。 -/
theorem runFirstOrderProviderAt_closed
    (sourceProblem : Problem) (problem : DeepProblem)
    (bridge : FirstOrderProblemBridgeAt.{x} sourceProblem problem)
    (settings : FirstOrderSettings := {})
    (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.closed
        (runFirstOrderProviderAt
          sourceProblem problem bridge settings config label) =
      runFirstOrderProviderClosedAt
        sourceProblem problem settings config label := by
  unfold runFirstOrderProviderAt runFirstOrderProviderClosedAt
  generalize hRun : runFirstOrder sourceProblem settings = run
  cases run with
  | error error =>
      simp [LogicSoundness.SetLevel.BackendAttemptAt.closed]
  | ok result =>
      simpa [hRun] using
        FirstOrderResult.runAvatarProviderAt_closed
          result problem bridge config label

/-- 整问题纯一阶 provider 的零 universe proof-carrying 与纯计算闭合状态一致。 -/
theorem runFirstOrderProvider_closed
    (sourceProblem : Problem) (problem : DeepProblem)
    (bridge : FirstOrderProblemBridge sourceProblem problem)
    (settings : FirstOrderSettings := {})
    (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") :
    (runFirstOrderProvider sourceProblem problem bridge settings config label).closed =
      runFirstOrderProviderClosed sourceProblem problem settings config label :=
  runFirstOrderProviderAt_closed
    sourceProblem problem bridge settings config label

/--
从整问题运行新预处理，并进入 `SearchCertificateProvider.runPreprocessed`。

显式给出 `search?` 时消费调用者提供的一阶 SearchDAG；默认 `none` 时按 FO/HO 能力分流。
-/
def runProviderAt (sourceProblem : Problem) (problem : DeepProblem)
    (bridge : ProblemBridgeAt.{x} sourceProblem problem)
    (settings : Settings := {}) (search? : Option SearchInput := none)
    (avatarConfig : AvatarConfig := {})
    (hoConfig : HOAvatarConfig := {})
    (label : String := "checked source preprocessing") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  match search? with
  | none =>
      runRoutedProviderAt sourceProblem problem bridge settings avatarConfig hoConfig label
  | some search =>
      match run sourceProblem settings with
      | Except.ok result =>
          SearchMaterialization.SearchCertificateProvider.runPreprocessedAt
            (result.toProviderInputAt problem bridge (some search) label) problem
      | Except.error error => .failure error

/-- 整问题 preprocessing provider 的现有零 universe 包装。 -/
def runProvider (sourceProblem : Problem) (problem : DeepProblem)
    (bridge : ProblemBridge sourceProblem problem)
    (settings : Settings := {}) (search? : Option SearchInput := none)
    (avatarConfig : AvatarConfig := {})
    (hoConfig : HOAvatarConfig := {})
    (label : String := "checked source preprocessing") :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  runProviderAt sourceProblem problem bridge settings search?
    avatarConfig hoConfig label

/-- 可直接放入任意模型 universe portfolio 的纯一阶 preprocessing + AVATAR provider。 -/
def firstOrderProviderAt (sourceProblem : Problem) (problem : DeepProblem)
    (bridge : FirstOrderProblemBridgeAt.{x} sourceProblem problem)
    (settings : FirstOrderSettings := {})
    (avatarConfig : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") :
    LogicSoundness.SetLevel.ProviderAt.{x} SearchMaterialization.SearchSignature where
  name := label
  backend := .composite
  run := fun targetProblem =>
    if hProblem :
        SearchMaterialization.SearchCertificateProvider.deepProblemEq
          targetProblem problem = true then
      have hEq : targetProblem = problem :=
        SearchMaterialization.SearchCertificateProvider.deepProblemEq_sound hProblem
      hEq.symm ▸
        runFirstOrderProviderAt sourceProblem problem bridge settings avatarConfig label
    else
      .failure <| diagnostic
        "first-order source preprocessing provider was invoked on a different deep problem"

/-- 可直接放入现有零 universe portfolio 的纯一阶 preprocessing + AVATAR provider。 -/
def firstOrderProvider (sourceProblem : Problem) (problem : DeepProblem)
    (bridge : FirstOrderProblemBridge sourceProblem problem)
    (settings : FirstOrderSettings := {})
    (avatarConfig : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") :
    LogicSoundness.SetLevel.Provider SearchMaterialization.SearchSignature :=
  firstOrderProviderAt sourceProblem problem bridge settings avatarConfig label

/-- 可直接放入任意模型 universe portfolio 的 preprocessing + FO/HO routed provider。 -/
def providerAt (sourceProblem : Problem) (problem : DeepProblem)
    (bridge : ProblemBridgeAt.{x} sourceProblem problem)
    (settings : Settings := {})
    (search? : Option SearchInput := none)
    (avatarConfig : AvatarConfig := {})
    (hoConfig : HOAvatarConfig := {})
    (label : String := "checked source preprocessing") :
    LogicSoundness.SetLevel.ProviderAt.{x} SearchMaterialization.SearchSignature where
  name := label
  backend := .composite
  run := fun targetProblem =>
    if hProblem :
        SearchMaterialization.SearchCertificateProvider.deepProblemEq
          targetProblem problem = true then
      have hEq : targetProblem = problem :=
        SearchMaterialization.SearchCertificateProvider.deepProblemEq_sound hProblem
      hEq.symm ▸
        runProviderAt sourceProblem problem bridge settings search?
          avatarConfig hoConfig label
    else
      .failure <| diagnostic
        "source preprocessing provider was invoked on a different deep problem"

/-- 可直接放入现有零 universe portfolio 的 preprocessing + FO/HO routed provider。 -/
def provider (sourceProblem : Problem) (problem : DeepProblem)
    (bridge : ProblemBridge sourceProblem problem)
    (settings : Settings := {})
    (search? : Option SearchInput := none)
    (avatarConfig : AvatarConfig := {})
    (hoConfig : HOAvatarConfig := {})
    (label : String := "checked source preprocessing") :
    LogicSoundness.SetLevel.Provider SearchMaterialization.SearchSignature :=
  providerAt sourceProblem problem bridge settings search?
    avatarConfig hoConfig label

end SourcePreprocessing
end Automation
end YesMetaZFC
