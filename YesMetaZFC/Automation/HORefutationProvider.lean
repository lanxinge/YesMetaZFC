import YesMetaZFC.Automation.CoreNormalForm.HigherOrderProjectionSoundness
import YesMetaZFC.Automation.HOAvatar
import YesMetaZFC.Automation.HOAvatarSoundness
import YesMetaZFC.Automation.HOExtensionalWitnessSoundness

/-!
# 原生高阶 AVATAR 双核到 HO-DAG 的可信 provider

本模块只处理 checked preprocessing 已经消去 FOOL 辅助项、但仍保留 `apply/lam` 的
原生高阶字句。HO saturation 与 CDCL 通过显式 `TheoryResponse` 循环共享 persistent
clause/DAG arena；最终产物由 `CheckedAvatarDAG` 专用整图 soundness 消费。
-/

namespace YesMetaZFC
namespace Automation
namespace HORefutationProvider

open HOSearchMaterialization
open HOSearchMaterialization.CoreProjectionSoundness

abbrev CoreClauseSet := CoreSyntax.NormalForm.ClauseSet
abbrev SearchClause := CoreSyntax.Search.Clause
abbrev Diagnostic := Certificate.Diagnostic

/-- HO provider 的统一结构化诊断。 -/
def diagnostic (phase : Certificate.Phase) (message : String) : Diagnostic :=
  Certificate.Diagnostic.ofMessage .superposition phase message

private def clauseListEq :
    List HOSearchMaterialization.Clause → List HOSearchMaterialization.Clause → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      HODAGCertificate.Clause.eq left right && clauseListEq leftRest rightRest
  | _, _ => false

private theorem clauseListEq_sound :
    ∀ {left right : List HOSearchMaterialization.Clause},
      clauseListEq left right = true → left = right
  | [], [], _ => rfl
  | left :: leftRest, right :: rightRest, hEq => by
      simp only [clauseListEq, Bool.and_eq_true_iff] at hEq
      have hHead := HODAGCertificate.Clause.eq_sound left right hEq.1
      have hRest := clauseListEq_sound hEq.2
      cases hHead
      cases hRest
      rfl
  | [], _ :: _, hEq => by
      simp [clauseListEq] at hEq
  | _ :: _, [], hEq => by
      simp [clauseListEq] at hEq

/-- HO 初始问题的顺序敏感结构比较。 -/
def problemEq (left right : HOSearchMaterialization.Problem) : Bool :=
  clauseListEq left.initialClauses.toList right.initialClauses.toList

/-- persistent saturation arena 的每个 clause 槽都必须命中同结论 DAG 节点。 -/
def arenaMappingCheck (dag : HOSearchMaterialization.DAG)
    (clauses : Array SearchClause) (nodeIds : Array Nat) : Bool :=
  clauses.size == nodeIds.size &&
    (clauses.mapIdx fun clauseId clause =>
      match nodeIds[clauseId]? with
      | none => false
      | some nodeId =>
          match dag.node? nodeId with
          | none => false
          | some node =>
              match node.conclusion? dag.problem with
              | none => false
              | some conclusion =>
                  match HOSearch.searchClause? conclusion with
                  | none => false
                  | some projected => CoreSyntax.Search.clauseEq projected clause).all id

/-- HO 初始问题结构比较通过时，两侧问题实际相等。 -/
theorem problemEq_sound {left right : HOSearchMaterialization.Problem}
    (hEq : problemEq left right = true) : left = right := by
  have hClauses := clauseListEq_sound hEq
  have hArray : left.initialClauses = right.initialClauses :=
    Array.toList_inj.mp hClauses
  cases left with
  | mk leftClauses =>
      cases right with
      | mk rightClauses =>
          simp only at hArray
          cases hArray
          rfl

/-- 沿 core problem 等式搬运初始字句的局部 checker 证明。 -/
theorem initialChecks_of_problem_eq
    {left right : HOSearchMaterialization.Problem}
    (hEq : left = right)
    (hChecks :
      left.initialClauses.all HODAGCertificate.Clause.check = true) :
    right.initialClauses.all HODAGCertificate.Clause.check = true := by
  cases hEq
  exact hChecks

/-- HO soundness 真正消费的最小 checked replay 证书。 -/
structure CheckedReplayArtifact (clauses : CoreClauseSet) where
  checked : HOAvatar.CheckedAvatarDAG
  witnessRegistry :
    HOExtensionalWitnessRegistry.CheckedRegistry checked.checked
  problem_eq : checked.checked.dag.problem = coreProblem clauses
  native : Native.clauseSet clauses = true
  initialChecks :
    (coreProblem clauses).initialClauses.all
      HODAGCertificate.Clause.check = true
  avatarSoundnessSupported :
    checked.checked.dag.avatarSoundnessSupported = true

/--
完整 provider 产物在 semantic replay 字段之外保留 arena 映射与性能审计。
-/
structure CheckedArtifact (clauses : CoreClauseSet) where
  checked : HOAvatar.CheckedAvatarDAG
  witnessRegistry :
    HOExtensionalWitnessRegistry.CheckedRegistry checked.checked
  problem_eq : checked.checked.dag.problem = coreProblem clauses
  native : Native.clauseSet clauses = true
  initialChecks :
    (coreProblem clauses).initialClauses.all
      HODAGCertificate.Clause.check = true
  avatarSoundnessSupported :
    checked.checked.dag.avatarSoundnessSupported = true
  searchClauses : Array SearchClause
  arenaClauses : Array SearchClause
  clauseNodeIds : Array Nat
  arenaAligned : arenaClauses.size = clauseNodeIds.size
  arenaMappingChecked :
    arenaMappingCheck checked.checked.dag arenaClauses clauseNodeIds = true
  seedSize : Nat
  proofJournalSize : Nat
  arenaSize : clauseNodeIds.size = seedSize + proofJournalSize
  hoStats : HOSearch.Stats
  stats : Certificate.Stats
  theoryRounds : Nat
  cdclStats : PropCdcl.SearchStats

namespace CheckedArtifact

/-- 完整搜索 artifact 投影到 soundness 唯一消费的最小 replay 证书。 -/
def replay {clauses : CoreClauseSet}
    (artifact : CheckedArtifact clauses) : CheckedReplayArtifact clauses := {
  checked := artifact.checked
  witnessRegistry := artifact.witnessRegistry
  problem_eq := artifact.problem_eq
  native := artifact.native
  initialChecks := artifact.initialChecks
  avatarSoundnessSupported := artifact.avatarSoundnessSupported
}

/-- artifact 直接携带的 canonical selector registry。 -/
def selectorRegistry {clauses : CoreClauseSet}
    (artifact : CheckedArtifact clauses) :
    List
      (HODAGCertificate.AvatarSelectorComponent
        HOSearchMaterialization.SearchSignature) :=
  artifact.checked.checked.dag.avatarSelectorRegistry

/-- 固定模型与 bound 栈后，由 checked registry 诱导 selector valuation。 -/
def selectorValuation {clauses : CoreClauseSet}
    (artifact : CheckedArtifact clauses)
    {M :
      Logic.HigherOrder.Structure
        HOSearchMaterialization.SearchSignature}
    (base : Logic.HigherOrder.Env M) : PropResolution.Valuation :=
  artifact.checked.selectorValuation base

/-- 按 persistent saturation clause id 读取真实 DAG node id。 -/
def clauseNodeId? {clauses : CoreClauseSet}
    (artifact : CheckedArtifact clauses) (clauseId : Nat) : Option Nat :=
  artifact.clauseNodeIds[clauseId]?

/-- proof journal 的第 `stepIndex` 步对应的真实 DAG node id。 -/
def proofJournalNodeId? {clauses : CoreClauseSet}
    (artifact : CheckedArtifact clauses) (stepIndex : Nat) : Option Nat :=
  artifact.clauseNodeId? (artifact.seedSize + stepIndex)

end CheckedArtifact

namespace CheckedReplayArtifact

private theorem problemValidAfterExpansion {clauses : CoreClauseSet}
    (artifact : CheckedReplayArtifact clauses)
    (M : CoreSyntax.NormalForm.Semantics.Model)
    (contract : CoreSyntax.NormalForm.Semantics.FoolLambdaContract M)
    (functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments))
    (base : CoreSyntax.NormalForm.Semantics.Env M)
    (hClauses :
      ∀ env, CoreSyntax.NormalForm.Semantics.Env.RespectsFree env →
        CoreSyntax.NormalForm.Semantics.LocalSkolemChoice.SameBoundStack env
          base →
          CoreSyntax.NormalForm.Semantics.ClauseSet.Satisfies env clauses) :
    let target := searchStructure M contract functionSort
    let targetContract := extensionalContract M contract functionSort
    artifact.checked.checked.dag.problem.Valid
      (HOExtensionalWitnessSoundness.Structure.overrideExtensionalWitnesses
        target targetContract) := by
  dsimp
  have hCoreValid :
      (coreProblem clauses).Valid
        (searchStructure M contract functionSort) :=
    coreProblem_valid contract functionSort base clauses artifact.native
      artifact.initialChecks hClauses
  have hProblemValid :
      artifact.checked.checked.dag.problem.Valid
        (searchStructure M contract functionSort) := by
    rw [artifact.problem_eq]
    exact hCoreValid
  exact
    HOExtensionalWitnessSoundness.checkedRegistry_problemValidAfterExpansion
      artifact.witnessRegistry
      (extensionalContract M contract functionSort) hProblemValid

/--
core 模型满足全部原生高阶初始字句时，HO-AVATAR residual 空根推出矛盾。
-/
theorem refutesCoreModel {clauses : CoreClauseSet}
    (artifact : CheckedReplayArtifact clauses)
    (M : CoreSyntax.NormalForm.Semantics.Model)
    (contract : CoreSyntax.NormalForm.Semantics.FoolLambdaContract M)
    (functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments))
    (base : CoreSyntax.NormalForm.Semantics.Env M)
    (hClauses :
      ∀ env, CoreSyntax.NormalForm.Semantics.Env.RespectsFree env →
        CoreSyntax.NormalForm.Semantics.LocalSkolemChoice.SameBoundStack env
          base →
          CoreSyntax.NormalForm.Semantics.ClauseSet.Satisfies env clauses) :
    False := by
  let target := searchStructure M contract functionSort
  let targetContract := extensionalContract M contract functionSort
  let expanded :=
    HOExtensionalWitnessSoundness.Structure.overrideExtensionalWitnesses
      target targetContract
  have hExpandedProblem :
      artifact.checked.checked.dag.problem.Valid expanded :=
    artifact.problemValidAfterExpansion M contract functionSort base hClauses
  exact artifact.checked.rootEmptyContradiction
    (HOExtensionalWitnessSoundness.extensionalContractPreserved
      targetContract)
    (HOExtensionalWitnessSoundness.extensionalWitnessContract
      targetContract)
    (Logic.HigherOrder.Env.canonical expanded)
    (Logic.HigherOrder.Env.canonical_wellSorted expanded)
    hExpandedProblem artifact.avatarSoundnessSupported

end CheckedReplayArtifact

namespace CheckedArtifact

/-- 完整 provider artifact 的旧消费面统一投影到最小 replay soundness。 -/
theorem refutesCoreModel {clauses : CoreClauseSet}
    (artifact : CheckedArtifact clauses)
    (M : CoreSyntax.NormalForm.Semantics.Model)
    (contract : CoreSyntax.NormalForm.Semantics.FoolLambdaContract M)
    (functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments))
    (base : CoreSyntax.NormalForm.Semantics.Env M)
    (hClauses :
      ∀ env, CoreSyntax.NormalForm.Semantics.Env.RespectsFree env →
        CoreSyntax.NormalForm.Semantics.LocalSkolemChoice.SameBoundStack env
          base →
          CoreSyntax.NormalForm.Semantics.ClauseSet.Satisfies env clauses) :
    False :=
  artifact.replay.refutesCoreModel
    M contract functionSort base hClauses

end CheckedArtifact

/-- 将增量 CDCL 的停止原因转换为 provider 诊断。 -/
private def requireUnsat (result : HOAvatar.RunResult) :
    Except Diagnostic Unit :=
  match result.search.outcome with
  | .unsat =>
      pure ()
  | .model _ =>
      throw (diagnostic .saturation
        "native HO-AVATAR saturation/CDCL reached a theory model")
  | .limitExhausted _ =>
      throw (diagnostic .saturation
        "native HO-AVATAR CDCL exhausted its search limit")
  | .invariantViolation message _ =>
      throw (diagnostic .backendCheck
        ("native HO-AVATAR CDCL invariant violation: " ++ message))
  | .theoryUnknown message =>
      throw (diagnostic .saturation
        ("native HO-AVATAR theory loop stopped: " ++ message))

/--
原生 HO core 字句进入真正的 AVATAR saturation/CDCL 双核，并材料化
`CheckedAvatarDAG` residual 空根。
-/
def run (clauses : CoreClauseSet)
    (hNative : Native.clauseSet clauses = true)
    (config : HOAvatar.Config := {}) :
    Except Diagnostic (CheckedArtifact clauses) := do
  let projectionState :=
    CoreSyntax.NormalForm.FirstOrderProjection.initialState
      (CoreSyntax.Formula.conjunctionList [])
  let (searchClauses, _) ←
    match
        (CoreSyntax.NormalForm.FirstOrderProjection.projectClauseSet {} clauses)
          projectionState with
    | some result =>
        pure result
    | none =>
        throw (diagnostic .sourceMaterialization
          "native HO clauses failed projection to the shared search syntax")
  let projectedProblem ←
    match HOSearchMaterialization.problem? searchClauses with
    | some problem =>
        pure problem
    | none =>
        throw (diagnostic .sourceMaterialization
          "native HO search clauses failed typed HO source materialization")
  let directProblem := coreProblem clauses
  if _hProblemEq : problemEq projectedProblem directProblem = true then
    let result ← HOAvatar.run config searchClauses
    let _ ← requireUnsat result
    let materialized ← result.materializeCertificate? config
    let checked := materialized.checked
    let arena := result.search.state.arena
    let arenaClauses := arena.saturation.clauses
    let clauseNodeIds := arena.clauseNodeIds
    let arenaAlignedProof :
        PLift (arenaClauses.size = clauseNodeIds.size) ←
      if h : arenaClauses.size = clauseNodeIds.size then
        pure (PLift.up h)
      else
        throw (diagnostic .sourceMaterialization
          "persistent HO saturation clauses and DAG ids are not aligned")
    let hArenaAligned := PLift.down arenaAlignedProof
    let arenaSizeProof :
        PLift
          (clauseNodeIds.size =
            arena.seedSize + arena.saturation.steps.size) ←
      if h :
          clauseNodeIds.size =
            arena.seedSize + arena.saturation.steps.size then
        pure (PLift.up h)
      else
        throw (diagnostic .sourceMaterialization
          "persistent HO arena is not seed plus proof journal size")
    let hArenaSize := PLift.down arenaSizeProof
    let witnessRegistry ←
      match
          HOExtensionalWitnessRegistry.CheckedRegistry.mk?
            checked.checked with
      | some registry =>
          pure registry
      | none =>
          throw (diagnostic .dagCheck
            "HO-AVATAR graph failed extensional witness registry checks")
    if hChecks :
        directProblem.initialClauses.all HODAGCertificate.Clause.check =
          true then
      if hCheckedProblem :
          problemEq checked.checked.dag.problem directProblem = true then
        if hMapping :
            arenaMappingCheck checked.checked.dag arenaClauses
              clauseNodeIds = true then
          if hSupported :
              checked.checked.dag.avatarSoundnessSupported = true then
            pure {
              checked := checked
              witnessRegistry := witnessRegistry
              problem_eq := problemEq_sound hCheckedProblem
              native := hNative
              initialChecks := hChecks
              avatarSoundnessSupported := hSupported
              searchClauses := searchClauses
              arenaClauses := arenaClauses
              clauseNodeIds := clauseNodeIds
              arenaAligned := hArenaAligned
              arenaMappingChecked := hMapping
              seedSize := arena.seedSize
              proofJournalSize := arena.saturation.steps.size
              arenaSize := hArenaSize
              hoStats := result.higherOrderSearch.stats
              stats := result.stats
              theoryRounds := result.search.theoryRounds
              cdclStats := result.search.stats
            }
          else
            throw (diagnostic .dagCheck
              "HO-AVATAR graph is outside dedicated soundness support")
        else
          throw (diagnostic .sourceMaterialization
            "persistent HO arena mapping failed the final DAG checker")
      else
        throw (diagnostic .dagCheck
          "checked HO-AVATAR graph no longer carries the core problem")
    else
      throw (diagnostic .sourceMaterialization
        "direct core-to-HO initial clauses failed the typed checker")
  else
    throw (diagnostic .sourceMaterialization
      "shared search projection disagrees with direct HO materialization")

end HORefutationProvider
end Automation
end YesMetaZFC
