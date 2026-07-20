import YesMetaZFC.Automation.Request
import YesMetaZFC.Automation.KernelReplay
import YesMetaZFC.Automation.ReplayQuotation

/-!
# 普通 Lean `Prop` 到 checked 自动化主线

本模块给 `prove_auto USE ...` 提供第一层宿主命题入口：

* Lean 的命题连接词重化为公共 `CoreSyntax.Formula`；
* 未被宿主 FO/HO provider 接受的量词、等式与谓词作为零元 source atom；
* 搜索仍经过整问题 preprocessing、AVATAR、canonical source table 与 checked DAG；
* 最终结论通过一个显式宿主模型回到原 Lean `Prop`，不直接生成绕过证书的证明项。

本模块只声称命题骨架能力；原生 FO/HO 重化分别由 `HostFirstOrder` 和
`HostHigherOrder` provider 负责。
-/

namespace YesMetaZFC
namespace Automation
namespace HostProp

universe x

open Lean Meta
open CoreSyntax
open CoreSyntax.NormalForm

/-- 宿主原子的稳定编号。 -/
structure Atom where
  id : Nat
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- `prove_auto` 宿主层当前可信消费的命题骨架。 -/
inductive Formula where
  | atom (value : Atom)
  | falsum
  | truth
  | neg (body : Formula)
  | conj (left right : Formula)
  | disj (left right : Formula)
  | imp (left right : Formula)
  | iff (left right : Formula)
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace Formula

/-- 命题骨架在宿主 atom 表中的直接解释。 -/
def eval (atoms : Nat → Prop) : Formula → Prop
  | .atom value => atoms value.id
  | .falsum => False
  | .truth => True
  | .neg body => ¬ eval atoms body
  | .conj left right => eval atoms left ∧ eval atoms right
  | .disj left right => eval atoms left ∨ eval atoms right
  | .imp left right => eval atoms left → eval atoms right
  | .iff left right => eval atoms left ↔ eval atoms right

/-- 宿主 atom 使用普通关系角色；定义性 CNF 仍保留自己的 definition 角色。 -/
def predicate (atom : Atom) : CoreSyntax.PredicateSymbol := {
  id := atom.id
  arity := 0
  role := .relation
  inputSorts := []
}

/-- 命题骨架进入统一 preprocessing core。 -/
def toCore : Formula → CoreSyntax.Formula
  | .atom value => .atom (predicate value) []
  | .falsum => .falseE
  | .truth => .trueE
  | .neg body => .neg body.toCore
  | .conj left right => .conj left.toCore right.toCore
  | .disj left right => .disj left.toCore right.toCore
  | .imp left right => .imp left.toCore right.toCore
  | .iff left right => .iffE left.toCore right.toCore

/-- 命题骨架进入 canonical DAG 使用的搜索签名。 -/
def toSearch : Formula →
    Logic.FirstOrder.Formula SearchMaterialization.SearchSignature
  | .atom value => .rel (.predicate (predicate value)) []
  | .falsum => .falsum
  | .truth => .truth
  | .neg body => .neg body.toSearch
  | .conj left right => .conj left.toSearch right.toSearch
  | .disj left right => .disj left.toSearch right.toSearch
  | .imp left right => .imp left.toSearch right.toSearch
  | .iff left right => .iff left.toSearch right.toSearch

end Formula

/-- 一张 proof-carrying 宿主事实表。 -/
inductive Facts where
  | nil
  | cons (proposition : Prop) (proof : proposition) (tail : Facts)

namespace Facts

/-- 擦除 proof 后得到搜索所需的命题列表。 -/
@[reducible] def propositions : Facts → List Prop
  | .nil => []
  | .cons proposition _ tail => proposition :: tail.propositions

/-- 事实表中的每个命题都有对应的 Lean 证明。 -/
theorem holds : ∀ (facts : Facts) (proposition : Prop),
    proposition ∈ facts.propositions → proposition
  | .nil, proposition, hMem => by
      simp [propositions] at hMem
  | .cons head proof tail, proposition, hMem => by
      simp only [propositions, List.mem_cons] at hMem
      rcases hMem with hHead | hTail
      · simpa [hHead] using proof
      · exact tail.holds proposition hTail

end Facts

/--
元层重化的 proof-carrying 结果。

两个 alignment 字段把纯语法快照钉回原 Lean 命题；后端 closed 计算不读取它们。
-/
structure CheckedInput (goal : Prop) where
  atoms : Nat → Prop
  facts : Facts
  premises : List Formula
  target : Formula
  premisesAligned :
    premises.map (Formula.eval atoms) = facts.propositions
  targetAligned :
    Formula.eval atoms target = goal

namespace CheckedInput

/-- 对齐后的每个 source premise 都由显式 `USE` proof 支持。 -/
theorem premiseHolds {goal : Prop} (input : CheckedInput goal)
    {formula : Formula} (hFormula : formula ∈ input.premises) :
    Formula.eval input.atoms formula := by
  apply input.facts.holds
  rw [← input.premisesAligned]
  exact List.mem_map.mpr ⟨formula, hFormula, rfl⟩

/-- 对齐后的目标解释可以回到原 Lean 目标。 -/
theorem goalOfTarget {goal : Prop} (input : CheckedInput goal)
    (hTarget : Formula.eval input.atoms input.target) : goal := by
  rw [← input.targetAligned]
  exact hTarget

/-- 一张纯命题骨架进入整问题 preprocessing source。 -/
def sourceProblemOfSyntax (premises : List Formula) (target : Formula) :
    SourcePreprocessing.Problem := {
  premises := premises.map Formula.toCore
  target := target.toCore
}

/-- 一张纯命题骨架进入 SearchSignature 深问题。 -/
def deepProblemOfSyntax (premises : List Formula) (target : Formula) :
    SourcePreprocessing.DeepProblem := {
  premises := premises.map Formula.toSearch
  target := target.toSearch
}

/-- 宿主重化结果进入整问题 preprocessing source。 -/
def sourceProblem {goal : Prop} (input : CheckedInput goal) :
    SourcePreprocessing.Problem :=
  sourceProblemOfSyntax input.premises input.target

/-- 宿主重化结果进入 SearchSignature 深问题。 -/
def deepProblem {goal : Prop} (input : CheckedInput goal) :
    SourcePreprocessing.DeepProblem :=
  deepProblemOfSyntax input.premises input.target

abbrev SearchStructureAt :=
  LogicSoundness.SetLevel.StructureAt.{x}
    SearchMaterialization.SearchSignature

/-- 现有宿主命题入口使用的零 universe 搜索结构。 -/
abbrev SearchStructure := SearchStructureAt.{0}

abbrev SearchEnvAt (M : SearchStructureAt.{x}) :=
  LogicSoundness.SetLevel.EnvAt.{x} M

/-- 现有宿主命题入口使用的零 universe 搜索环境。 -/
abbrev SearchEnv (M : SearchStructure) := SearchEnvAt.{0} M

/-- 任意搜索反模型扩张为只解释宿主 atom 的纯一阶 core 模型。 -/
@[reducible] noncomputable def coreModelOfSearch
    (M : SearchStructureAt.{x}) : Semantics.Model.{x} := by
  classical
  exact {
    Carrier := M.Domain
    default := Classical.choice M.nonempty
    sortInterp := M.sortInterp
    sortNonempty := M.sortNonempty
    functionInterp := fun symbol arguments =>
      if hArguments :
          Logic.FirstOrder.ArgsSatisfy M.sortInterp arguments
            (SearchMaterialization.SearchSignature.funcDomain
              (FirstOrderProjection.functionSymbol symbol)) then
        M.funcInterp (FirstOrderProjection.functionSymbol symbol) arguments
      else
        Classical.choose (M.sortNonempty symbol.outputSort)
    predicateInterp := fun predicate arguments =>
      M.relInterp (.predicate predicate) arguments
    applyInterp := fun _ _ => Classical.choice M.nonempty
    boolValue := fun _ => Classical.choice M.nonempty
    notValue := fun _ => Classical.choice M.nonempty
    andValue := fun _ _ => Classical.choice M.nonempty
    orValue := fun _ _ => Classical.choice M.nonempty
    impValue := fun _ _ => Classical.choice M.nonempty
    iffValue := fun _ _ => Classical.choice M.nonempty
    quoteValue := fun _ => Classical.choice M.nonempty
    lambdaValue := fun _ _ _ => Classical.choice M.nonempty
    iteValue := fun _ _ _ => Classical.choice M.nonempty
    boolHolds := fun _ => False
  }

/-- 搜索环境在宿主 core 模型中的对应环境。 -/
@[reducible] noncomputable def coreEnvOfSearch
    {M : SearchStructureAt.{x}} (env : SearchEnvAt.{x} M) :
    Semantics.Env (coreModelOfSearch M) where
  boundVal := fun index => env.boundVal .object index
  freeVal := env.freeVal

/-- 宿主 core 模型中的函数解释保持 codomain sort。 -/
theorem coreModel_functionSort (M : SearchStructureAt.{x}) :
    ∀ symbol arguments,
      (coreModelOfSearch M).sortInterp symbol.outputSort
        ((coreModelOfSearch M).functionInterp symbol arguments) := by
  intro symbol arguments
  classical
  by_cases hArguments :
      Logic.FirstOrder.ArgsSatisfy M.sortInterp arguments
        (SearchMaterialization.SearchSignature.funcDomain
          (FirstOrderProjection.functionSymbol symbol))
  · simpa only [coreModelOfSearch, hArguments, ↓reduceDIte] using
      M.funcSort (FirstOrderProjection.functionSymbol symbol)
        arguments hArguments
  · simpa only [coreModelOfSearch, hArguments, ↓reduceDIte] using
      Classical.choose_spec (M.sortNonempty symbol.outputSort)

/-- 搜索环境保持全部 typed free assignment。 -/
theorem coreEnv_respectsFree {M : SearchStructureAt.{x}}
    (env : SearchEnvAt.{x} M) :
    Semantics.Env.RespectsFree (coreEnvOfSearch env) := by
  intro sort id
  exact env.freeSort sort id

/-- 宿主命题骨架的 core/search 翻译语义一致。 -/
theorem satisfies_coreFormula {M : SearchStructureAt.{x}}
    (env : SearchEnvAt.{x} M) :
    ∀ formula : Formula,
      Semantics.Formula.Satisfies
          (coreEnvOfSearch env) formula.toCore ↔
        Logic.FirstOrder.Formula.satisfies env formula.toSearch
  | .atom value => by
      simp [Formula.toCore, Formula.toSearch, Formula.predicate,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies, coreModelOfSearch]
  | .falsum => by
      simp [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
  | .truth => by
      simp [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
  | .neg body => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          not_congr (satisfies_coreFormula env body)
  | .conj left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          and_congr
            (satisfies_coreFormula env left)
            (satisfies_coreFormula env right)
  | .disj left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          or_congr
            (satisfies_coreFormula env left)
            (satisfies_coreFormula env right)
  | .imp left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          imp_congr
            (satisfies_coreFormula env left)
            (satisfies_coreFormula env right)
  | .iff left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          iff_congr
            (satisfies_coreFormula env left)
            (satisfies_coreFormula env right)

/-- core 合取列表逐项满足时，其整体也满足。 -/
theorem coreSatisfiesConjunctionList {M : Semantics.Model.{x}}
    (env : Semantics.Env M) (formulas : List CoreSyntax.Formula)
    (hFormulas :
      ∀ formula ∈ formulas, Semantics.Formula.Satisfies env formula) :
    Semantics.Formula.Satisfies env
      (CoreSyntax.Formula.conjunctionList formulas) := by
  induction formulas with
  | nil =>
      simp [CoreSyntax.Formula.conjunctionList,
        Semantics.Formula.Satisfies, Semantics.Formula.eval]
  | cons head tail ih =>
      cases tail with
      | nil =>
          simpa [CoreSyntax.Formula.conjunctionList] using
            hFormulas head (by simp)
      | cons next rest =>
          simp only [CoreSyntax.Formula.conjunctionList,
            Semantics.Formula.Satisfies, Semantics.Formula.eval]
          constructor
          · exact hFormulas head (by simp)
          · apply ih
            intro formula hFormula
            exact hFormulas formula (by simp [hFormula])

/-- 宿主 source/deep 问题之间任意模型 universe 的纯一阶反模型桥。 -/
def firstOrderBridgeAt {goal : Prop} (input : CheckedInput goal) :
    SourcePreprocessing.FirstOrderProblemBridgeAt.{x}
      input.sourceProblem input.deepProblem := by
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
      ⟨source, hSource, rfl⟩
    exact
      (satisfies_coreFormula env source).mpr <|
        hModels source.toSearch <|
          List.mem_map.mpr ⟨source, hSource, rfl⟩
  · subst formula
    have hCoreTarget :
        ¬ Semantics.Formula.Satisfies
          (coreEnvOfSearch env) input.target.toCore := by
      intro hCore
      exact hTarget <| (satisfies_coreFormula env input.target).mp hCore
    simpa [Semantics.Formula.Satisfies, Semantics.Formula.eval] using
      hCoreTarget

/-- 宿主 source/deep 问题之间现有零 universe 的纯一阶反模型桥。 -/
def firstOrderBridge {goal : Prop} (input : CheckedInput goal) :
    SourcePreprocessing.FirstOrderProblemBridge
      input.sourceProblem input.deepProblem :=
  input.firstOrderBridgeAt

/--
atom 表在任意模型 universe 中的标准宿主模型；所有 sort 共享提升后的 `Unit`，
关系解释回到原 Lean 命题。
-/
def hostStructureAt (atoms : Nat → Prop) : SearchStructureAt.{x} where
  Domain := ULift.{x, 0} Unit
  nonempty := ⟨ULift.up ()⟩
  sortInterp := fun _ _ => True
  sortNonempty := fun _ => ⟨ULift.up (), trivial⟩
  funcInterp := fun _ _ => ULift.up ()
  funcSort := by
    intro symbol arguments hArguments
    trivial
  relInterp := fun relation arguments =>
    match relation with
    | .predicate predicate =>
        if arguments.isEmpty then atoms predicate.id else False
    | _ => False

/-- atom 表在现有零 universe 中的标准宿主模型。 -/
def hostStructure (atoms : Nat → Prop) : SearchStructure :=
  hostStructureAt.{0} atoms

/-- 任意模型 universe 标准宿主模型的 canonical typed 环境。 -/
def hostEnvAt (atoms : Nat → Prop) :
    SearchEnvAt.{x} (hostStructureAt.{x} atoms) where
  boundVal := fun _ _ => ULift.up ()
  freeVal := fun _ _ => ULift.up ()
  boundSort := by simp [hostStructureAt]
  freeSort := by simp [hostStructureAt]

/-- 现有零 universe 标准宿主模型的 canonical typed 环境。 -/
def hostEnv (atoms : Nat → Prop) : SearchEnv (hostStructure atoms) :=
  hostEnvAt.{0} atoms

/-- 搜索签名在任意 universe 标准宿主模型中的满足关系就是命题骨架解释。 -/
theorem satisfies_searchFormula_hostAt (atoms : Nat → Prop) :
    ∀ formula : Formula,
      Logic.FirstOrder.Formula.satisfies
          (hostEnvAt.{x} atoms) formula.toSearch ↔
        formula.eval atoms
  | .atom value => by
      simp [Formula.toSearch, Formula.predicate,
        Logic.FirstOrder.Formula.satisfies, hostStructureAt, hostEnvAt,
        Formula.eval]
  | .falsum => by
      simp [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval]
  | .truth => by
      simp [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval]
  | .neg body => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          not_congr (satisfies_searchFormula_hostAt atoms body)
  | .conj left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          and_congr
            (satisfies_searchFormula_hostAt atoms left)
            (satisfies_searchFormula_hostAt atoms right)
  | .disj left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          or_congr
            (satisfies_searchFormula_hostAt atoms left)
            (satisfies_searchFormula_hostAt atoms right)
  | .imp left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          imp_congr
            (satisfies_searchFormula_hostAt atoms left)
            (satisfies_searchFormula_hostAt atoms right)
  | .iff left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          iff_congr
            (satisfies_searchFormula_hostAt atoms left)
            (satisfies_searchFormula_hostAt atoms right)

/-- 搜索签名在现有零 universe 标准宿主模型中的解释。 -/
theorem satisfies_searchFormula_host (atoms : Nat → Prop) :
    ∀ formula : Formula,
      Logic.FirstOrder.Formula.satisfies
          (hostEnv atoms) formula.toSearch ↔
        formula.eval atoms :=
  satisfies_searchFormula_hostAt.{0} atoms

/-- 任意模型 universe 的语义蕴涵经标准宿主模型回到原 Lean 目标。 -/
theorem soundOfSearchAt {goal : Prop} (input : CheckedInput goal)
    (hSearch :
      LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
        input.deepProblem.theory input.deepProblem.target) :
    goal := by
  have hTarget :
      Logic.FirstOrder.Formula.satisfies
        (hostEnvAt.{x} input.atoms) input.target.toSearch :=
    hSearch (hostEnvAt.{x} input.atoms) (by
      intro formula hFormula
      rcases List.mem_map.mp hFormula with
        ⟨source, hSource, rfl⟩
      exact
        (satisfies_searchFormula_hostAt input.atoms source).mpr
          (input.premiseHolds hSource))
  exact input.goalOfTarget <|
    (satisfies_searchFormula_hostAt input.atoms input.target).mp hTarget

/-- 现有零 universe 的语义蕴涵经标准宿主模型回到原 Lean 目标。 -/
theorem soundOfSearch {goal : Prop} (input : CheckedInput goal)
    (hSearch :
      LogicSoundness.SetLevel.SemanticallyEntails
        input.deepProblem.theory input.deepProblem.target) :
    goal :=
  input.soundOfSearchAt hSearch

/-- 纯问题快照对应的任意模型 universe proof-carrying 后端尝试。 -/
def backendAttemptFromProblemsAt {goal : Prop} (input : CheckedInput goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem)
    (settings : SourcePreprocessing.FirstOrderSettings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (label : String := "host Prop skeleton") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem := by
  let bridge :
      SourcePreprocessing.FirstOrderProblemBridgeAt.{x}
        sourceProblem problem := by
    rw [hSource, hProblem]
    exact input.firstOrderBridgeAt
  exact
    SourcePreprocessing.runFirstOrderProviderAt
      sourceProblem problem bridge settings avatarConfig label

/-- 纯问题快照对应的现有零 universe proof-carrying 后端尝试。 -/
def backendAttemptFromProblems {goal : Prop} (input : CheckedInput goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem)
    (settings : SourcePreprocessing.FirstOrderSettings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (label : String := "host Prop skeleton") :
    LogicSoundness.SetLevel.BackendAttempt problem :=
  backendAttemptFromProblemsAt input sourceProblem problem
    hSource hProblem settings avatarConfig label

/--
宿主重化结果与独立纯问题快照运行任意模型 universe 的公共纯一阶 AVATAR/DAG 主线。

该入口直接消费泛 universe attempt 的 closed 标记；搜索和 checker 计算仍完全位于
`Type 0`。
-/
def goalAttemptFromProblemsAt {goal : Prop} (input : CheckedInput goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem)
    (settings : SourcePreprocessing.FirstOrderSettings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (label : String := "host Prop skeleton") :
    ProveAutoRequest.GoalAttempt goal := by
  let attempt :=
    backendAttemptFromProblemsAt input sourceProblem problem
      hSource hProblem settings avatarConfig label
  exact {
    closed := LogicSoundness.SetLevel.BackendAttemptAt.closed attempt
    summary := LogicSoundness.SetLevel.BackendAttemptAt.summary attempt
    sound := by
      intro hClosed
      have hSearch :
          LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
            problem.theory problem.target :=
        ProveAutoRequest.GoalAttempt.backendSoundOfClosedAt
          problem attempt hClosed
      have hInputSearch :
          LogicSoundness.SetLevel.SemanticallyEntailsAt.{x}
            input.deepProblem.theory input.deepProblem.target := by
        rw [← hProblem]
        exact hSearch
      exact input.soundOfSearchAt hInputSearch
  }

/--
宿主重化结果与独立纯问题快照运行公共纯一阶 AVATAR/DAG 主线。

两个等同性只连接 soundness；closed 与 summary 完全由纯问题快照计算。
-/
def goalAttemptFromProblems {goal : Prop} (input : CheckedInput goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem)
    (settings : SourcePreprocessing.FirstOrderSettings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (label : String := "host Prop skeleton") :
    ProveAutoRequest.GoalAttempt goal := by
  let attempt :=
    backendAttemptFromProblems input sourceProblem problem
      hSource hProblem settings avatarConfig label
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
        let bridge :
            SourcePreprocessing.FirstOrderProblemBridge
              sourceProblem problem := by
          rw [hSource, hProblem]
          exact input.firstOrderBridge
        exact
          (SourcePreprocessing.runFirstOrderProvider_closed
            sourceProblem problem bridge settings avatarConfig label).trans hClosed
      have hSearch :
          LogicSoundness.SetLevel.SemanticallyEntails
            problem.theory problem.target :=
        ProveAutoRequest.GoalAttempt.backendSoundOfClosed
          problem attempt hAttemptClosed
      have hInputSearch :
          LogicSoundness.SetLevel.SemanticallyEntails
            input.deepProblem.theory input.deepProblem.target := by
        rw [← hProblem]
        exact hSearch
      exact input.soundOfSearch hInputSearch
  }

/-- 宿主重化结果运行任意模型 universe 的公共纯一阶 AVATAR/DAG 主线。 -/
def goalAttemptAt {goal : Prop} (input : CheckedInput goal)
    (settings : SourcePreprocessing.FirstOrderSettings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (label : String := "host Prop skeleton") :
    ProveAutoRequest.GoalAttempt goal :=
  goalAttemptFromProblemsAt.{x} input input.sourceProblem input.deepProblem
    rfl rfl settings avatarConfig label

/-- 宿主重化结果运行现有零 universe 的公共纯一阶 AVATAR/DAG 主线。 -/
def goalAttempt {goal : Prop} (input : CheckedInput goal)
    (settings : SourcePreprocessing.FirstOrderSettings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (label : String := "host Prop skeleton") :
    ProveAutoRequest.GoalAttempt goal :=
  goalAttemptFromProblems input input.sourceProblem input.deepProblem
    rfl rfl settings avatarConfig label

/-- 元层或显式调用者选择模型 universe 后使用的纯问题快照入口。 -/
@[reducible] def defaultGoalAttemptFromProblemsAt
    {goal : Prop} (input : CheckedInput goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem) :
    ProveAutoRequest.GoalAttempt goal :=
  goalAttemptFromProblemsAt.{x} input sourceProblem problem hSource hProblem

/-- 元层 provider 使用纯问题快照与默认搜索配置的稳定入口。 -/
@[reducible] def defaultGoalAttemptFromProblems
    {goal : Prop} (input : CheckedInput goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem) :
    ProveAutoRequest.GoalAttempt goal :=
  goalAttemptFromProblems input sourceProblem problem hSource hProblem

/-- 元层搜索结果只引用纯数据 payload/DAG，再由内核重放 checked 主线。 -/
def goalAttemptFromReplay {goal : Prop} (input : CheckedInput goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check sourceProblem payload = true)
    (data :
      SearchMaterialization.SearchCertificateProvider.PreparedReplaySearchData
        (SourcePreprocessing.FirstOrderReplay.searchInput
          payload problem search "host Prop skeleton"))
    : ProveAutoRequest.GoalAttempt goal := by
  let bridge :
      SourcePreprocessing.FirstOrderProblemBridge
        sourceProblem problem := by
    rw [hSource, hProblem]
    exact input.firstOrderBridge
  let replay :=
    SourcePreprocessing.FirstOrderReplay.ofCheck
      sourceProblem payload hReplay
  let attempt :
      LogicSoundness.SetLevel.BackendAttempt problem :=
    .success (data.backendSuccessAt (replay.refutationBridge bridge))
  exact {
    closed := true
    summary := "DAG reflection/DAG check: closed"
    sound := by
      intro _
      have hAttemptClosed : attempt.closed = true := rfl
      have hSearch :
          LogicSoundness.SetLevel.SemanticallyEntails
            problem.theory problem.target :=
        ProveAutoRequest.GoalAttempt.backendSoundOfClosed
          problem attempt hAttemptClosed
      have hInputSearch :
          LogicSoundness.SetLevel.SemanticallyEntails
            input.deepProblem.theory input.deepProblem.target := by
        rw [← hProblem]
        exact hSearch
      exact input.soundOfSearch hInputSearch
  }

/-- 元层 provider 使用默认配置引用搜索结果的稳定入口。 -/
@[reducible] def defaultGoalAttemptFromReplay
    {goal : Prop} (input : CheckedInput goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check sourceProblem payload = true)
    (data :
      SearchMaterialization.SearchCertificateProvider.PreparedReplaySearchData
        (SourcePreprocessing.FirstOrderReplay.searchInput
          payload problem search "host Prop skeleton")) :
    ProveAutoRequest.GoalAttempt goal :=
  goalAttemptFromReplay
    input sourceProblem problem hSource hProblem payload search hReplay data

end CheckedInput

/-! ## Lean 元层重化 -/

initialize registerTraceClass `YesMetaZFC.proveAuto.hostProp

private structure ReifyState where
  atoms : Array Expr := #[]

private abbrev ReifyM := StateRefT ReifyState MetaM

private def internAtom (expression : Expr) : ReifyM Atom := do
  let state ← get
  if let some index := state.atoms.findIdx? fun atom => atom == expression then
    return { id := index }
  let id := state.atoms.size
  set (show ReifyState from { atoms := state.atoms.push expression })
  return { id := id }

/-- 只展开 Lean 内建命题连接词；其他表达式保持稳定 atom。 -/
private partial def reifyFormula (expression : Expr) : ReifyM Formula := do
  let expression ← instantiateMVars expression
  let expression := expression.consumeMData
  if expression.isConstOf ``False then
    return .falsum
  if expression.isConstOf ``True then
    return .truth
  if expression.isAppOfArity ``Not 1 then
    return .neg (← reifyFormula expression.getAppArgs[0]!)
  if expression.isAppOfArity ``And 2 then
    return .conj
      (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Or 2 then
    return .disj
      (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Iff 2 then
    return .iff
      (← reifyFormula expression.getAppArgs[0]!)
      (← reifyFormula expression.getAppArgs[1]!)
  match expression with
  | .forallE _ domain body _ =>
      if !body.hasLooseBVar 0 && (← isProp domain) then
        return .imp
          (← reifyFormula domain)
          (← reifyFormula body)
      return .atom (← internAtom expression)
  | _ =>
      return .atom (← internAtom expression)

/-- 用同序 proposition 快照构造 proof-carrying 宿主事实表。 -/
def proofFactsExprWithTypes
    (proofs propositions : Array Expr) : MetaM Expr := do
  unless proofs.size == propositions.size do
    throwError
      "internal prove_auto fact proposition snapshot changed length"
  let mut tail := mkConst ``Facts.nil
  let mut index := proofs.size
  while index > 0 do
    index := index - 1
    let proposition := propositions[index]!
    unless ← isProp proposition do
      throwError
        "prove_auto USE expected a proof term, but got{indentExpr proposition}"
    tail ← mkAppM ``Facts.cons #[proposition, proofs[index]!, tail]
  return tail

/-- 兼容独立调用：先读取 proof 类型，再复用同一事实表构造入口。 -/
def proofFactsExpr (proofs : Array Expr) : MetaM Expr := do
  let propositions ← proofs.mapM fun proof => do
    instantiateMVars (← inferType proof)
  proofFactsExprWithTypes proofs propositions

private def atomFunctionExpr (atoms : Array Expr) : MetaM Expr := do
  withLocalDeclD `atomId (mkConst ``Nat) fun atomId => do
    let mut body := mkConst ``False
    for index in [0 : atoms.size] do
      let condition ← mkEq atomId (mkNatLit index)
      let decidable ← synthInstance (mkApp (mkConst ``Decidable) condition)
      body :=
        mkApp5 (mkConst ``ite [Level.succ Level.zero]) (mkSort Level.zero)
          condition decidable atoms[index]! body
    mkLambdaFVars #[atomId] body

private structure CheckedInputExpr where
  expression : Expr
  sourceProblem : SourcePreprocessing.Problem

private def checkedInputExpr
    (goal : Expr) (proofs factTypes : Array Expr) :
    MetaM CheckedInputExpr := do
  for factType in factTypes do
    unless ← isProp factType do
      throwError
        "prove_auto USE expected a proof term, but got{indentExpr factType}"
  let ((premises, target), state) ←
    (do
      let premises ← factTypes.toList.mapM reifyFormula
      let target ← reifyFormula goal
      pure (premises, target)).run {}
  let atoms ← atomFunctionExpr state.atoms
  let facts ← proofFactsExprWithTypes proofs factTypes
  let premiseList ←
    mkListLit (mkConst ``Formula)
      (premises.map toExpr)
  let targetFormula := toExpr target
  let evalFunction := mkApp (mkConst ``Formula.eval) atoms
  let premiseEvals ← mkAppM ``List.map #[evalFunction, premiseList]
  let factPropositions ← mkAppM ``Facts.propositions #[facts]
  let targetEval := mkApp2 (mkConst ``Formula.eval) atoms targetFormula
  let hPremises ← mkEqRefl premiseEvals
  unless ← isDefEq (← inferType hPremises)
      (← mkEq premiseEvals factPropositions) do
    throwError "internal HostProp premise alignment is not definitional"
  let hTarget ← mkEqRefl targetEval
  unless ← isDefEq (← inferType hTarget) (← mkEq targetEval goal) do
    throwError "internal HostProp target alignment is not definitional"
  trace[YesMetaZFC.proveAuto.hostProp]
    "atoms={state.atoms.size}; premises={premises.length}"
  return {
    expression := mkAppN (mkConst ``CheckedInput.mk)
      #[goal, atoms, facts, premiseList, targetFormula, hPremises, hTarget]
    sourceProblem := CheckedInput.sourceProblemOfSyntax premises target
  }

private partial def goalHasLogicalStructure (goal : Expr) : MetaM Bool := do
  let goal ← whnf (← instantiateMVars goal)
  if goal.isAppOfArity ``Not 1 ||
      goal.isAppOfArity ``And 2 ||
      goal.isAppOfArity ``Or 2 ||
      goal.isAppOfArity ``Iff 2 then
    return true
  match goal with
  | .forallE _ domain body _ =>
      return !body.hasLooseBVar 0 && (← isProp domain)
  | .letE _ _ value body _ =>
      goalHasLogicalStructure (body.instantiate1 value)
  | _ =>
      return false

private def buildAttempt? (request : ProveAutoRequest.PreparedContextRequest) :
    MetaM (Option Expr) := do
  unless ← isProp request.goal do
    return none
  let proofs := request.facts
  let factTypes := request.terminal.factPropositions
  trace[YesMetaZFC.proveAuto.hostProp]
    "context resources: {request.resourceSummary.render}"
  if proofs.isEmpty && !(← goalHasLogicalStructure request.goal) then
    return none
  let reified ← checkedInputExpr request.goal proofs factTypes
  let input := reified.expression
  let premiseList ← withTransparency .all do
    whnf (← mkAppM ``CheckedInput.premises #[input])
  let targetFormula ← withTransparency .all do
    whnf (← mkAppM ``CheckedInput.target #[input])
  let sourceProblem ←
    mkAppM ``CheckedInput.sourceProblemOfSyntax
      #[premiseList, targetFormula]
  let problem ←
    mkAppM ``CheckedInput.deepProblemOfSyntax
      #[premiseList, targetFormula]
  let expectedSource ← mkAppM ``CheckedInput.sourceProblem #[input]
  let expectedProblem ← mkAppM ``CheckedInput.deepProblem #[input]
  unless ← isDefEq sourceProblem expectedSource do
    throwError "internal HostProp source snapshot lost syntax alignment"
  unless ← isDefEq problem expectedProblem do
    throwError "internal HostProp deep snapshot lost syntax alignment"
  let hSourceSnapshot ← mkEqRefl sourceProblem
  let hProblem ← mkEqRefl problem
  let label := "host Prop skeleton"
  let attempt ←
    match SourcePreprocessing.runFirstOrder reified.sourceProblem with
    | Except.error error =>
        pure <| KernelReplay.failureAttemptExpr request.goal error.label
    | Except.ok firstOrder =>
        match firstOrder.result.runAvatar? with
        | Except.error error =>
            pure <| KernelReplay.failureAttemptExpr request.goal error.label
        | Except.ok artifact =>
            let settingsExpr :=
              toExpr (({} : SourcePreprocessing.FirstOrderSettings).toSettings)
            let replay ←
              KernelReplay.firstOrderReplayExprs sourceProblem problem
                settingsExpr firstOrder.result.checked.payload artifact label
            mkAppM ``CheckedInput.defaultGoalAttemptFromReplay
              #[input, sourceProblem, problem, hSourceSnapshot, hProblem,
                replay.payload, replay.search, replay.checked, replay.data]
  let attempt ← instantiateMVars attempt
  let (_, freeVariables) ← attempt.collectFVars.run {}
  let localContext ← getLCtx
  for freeVariable in freeVariables.fvarIds do
    unless localContext.contains freeVariable do
      throwError
        "internal HostProp request leaked a temporary free variable: {freeVariable.name}"
    let localDecl := localContext.get! freeVariable
    if localDecl.isImplementationDetail then
      throwError
        "internal HostProp request retained implementation-detail free variable \
        `{freeVariable.name}` of type{indentExpr localDecl.type}"
  return some attempt

/-- 普通 Lean `Prop` 的 proof-carrying context provider。 -/
def contextProvider : ProveAutoRequest.ContextProvider where
  build? := buildAttempt?

register_prove_auto_context_provider contextProvider

end HostProp
end Automation
end YesMetaZFC
