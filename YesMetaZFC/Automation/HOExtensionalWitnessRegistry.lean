import YesMetaZFC.Automation.HODAGCertificate

/-!
# 高阶外延见证全局注册表

注册表只从已经存在的 HO-DAG `functionExtensionality` 节点抽取，不接受搜索器额外
声明见证。全局 checker 复核见证符号类型、相对初始问题与先前节点的新鲜性，以及
不同外延步骤之间的符号唯一性。
-/

namespace YesMetaZFC
namespace Automation
namespace HOExtensionalWitnessRegistry

open HODAGCertificate
open Logic.HigherOrder

universe u v w

abbrev Signature := HODAGCertificate.Signature
abbrev SimpleType (σ : Signature) := HODAGCertificate.SimpleType σ
abbrev Term (σ : Signature) := HODAGCertificate.Term σ
abbrev Clause (σ : Signature) := HODAGCertificate.Clause σ
abbrev Node (σ : Signature) := HODAGCertificate.Node σ
abbrev DAG (σ : Signature) := HODAGCertificate.DAG σ
abbrev CheckedDAG (σ : Signature) [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] :=
  HODAGCertificate.CheckedDAG (σ := σ)
abbrev WitnessEvidence (σ : Signature) :=
  HODAGCertificate.FunctionExtensionality.Evidence σ

namespace Syntax

mutual
  /-- 项中是否出现指定函数符号。 -/
  def termContainsFunction {σ : Signature.{u, v, w}} [DecidableEq σ.FuncSymbol]
      (target : σ.FuncSymbol) : Term σ → Bool
    | .var _ => false
    | .app symbol arguments =>
        decide (symbol = target) || termListContainsFunction target arguments
    | .apply function argument =>
        termContainsFunction target function || termContainsFunction target argument
    | .lam _ _ body => termContainsFunction target body

  /-- 项列表中是否出现指定函数符号。 -/
  def termListContainsFunction {σ : Signature.{u, v, w}} [DecidableEq σ.FuncSymbol]
      (target : σ.FuncSymbol) : List (Term σ) → Bool
    | [] => false
    | term :: rest =>
        termContainsFunction target term || termListContainsFunction target rest
end

/-- 原子中是否出现指定函数符号。 -/
def atomContainsFunction {σ : Signature.{u, v, w}} [DecidableEq σ.FuncSymbol]
    (target : σ.FuncSymbol) : HODAGCertificate.Atom σ → Bool
  | .rel _ arguments => termListContainsFunction target arguments
  | .equal _ left right =>
      termContainsFunction target left || termContainsFunction target right

/-- 文字中是否出现指定函数符号。 -/
def literalContainsFunction {σ : Signature.{u, v, w}} [DecidableEq σ.FuncSymbol]
    (target : σ.FuncSymbol) (literal : HODAGCertificate.Literal σ) : Bool :=
  atomContainsFunction target literal.atom

/-- 子句中是否出现指定函数符号。 -/
def clauseContainsFunction {σ : Signature.{u, v, w}} [DecidableEq σ.FuncSymbol]
    (target : σ.FuncSymbol) (clause : Clause σ) : Bool :=
  clause.literals.any (literalContainsFunction target)

mutual
  /-- 项中不能出现任何签名标记的外延见证符号。 -/
  def termWitnessFree {σ : Signature.{u, v, w}} : Term σ → Bool
    | .var _ => true
    | .app symbol arguments =>
        !σ.isFunctionExtensionalityWitness symbol &&
          termListWitnessFree arguments
    | .apply function argument =>
        termWitnessFree function && termWitnessFree argument
    | .lam _ _ body =>
        termWitnessFree body

  /-- 项列表中不能出现任何签名标记的外延见证符号。 -/
  def termListWitnessFree {σ : Signature.{u, v, w}} : List (Term σ) → Bool
    | [] => true
    | term :: rest =>
        termWitnessFree term && termListWitnessFree rest
end

/-- 原子中不能出现任何签名标记的外延见证符号。 -/
def atomWitnessFree {σ : Signature.{u, v, w}} : HODAGCertificate.Atom σ → Bool
  | .rel _ arguments =>
      termListWitnessFree arguments
  | .equal _ left right =>
      termWitnessFree left && termWitnessFree right

/-- 文字中不能出现任何签名标记的外延见证符号。 -/
def literalWitnessFree {σ : Signature.{u, v, w}}
    (literal : HODAGCertificate.Literal σ) : Bool :=
  atomWitnessFree literal.atom

/-- 子句中不能出现任何签名标记的外延见证符号。 -/
def clauseWitnessFree {σ : Signature.{u, v, w}}
    (clause : Clause σ) : Bool :=
  clause.literals.all literalWitnessFree

end Syntax

/-- 一次显式函数外延步骤及其差异见证来源。 -/
structure Entry (σ : Signature.{u, v, w}) where
  nodeId : Nat
  evidence : WitnessEvidence σ

namespace Entry

/-- 从外延节点 payload 建立注册表条目。 -/
def ofEvidence {σ : Signature.{u, v, w}} (nodeId : Nat)
    (evidence : WitnessEvidence σ) : Entry σ := {
  nodeId := nodeId
  evidence := evidence
}

/-- 只有显式函数外延节点会产生注册表条目。 -/
def ofNode? {σ : Signature.{u, v, w}} (node : Node σ) : Option (Entry σ) :=
  match node.payload with
  | .functionExtensionality evidence => some (ofEvidence node.id evidence)
  | _ => none

/-- 当前条目使用的差异见证符号。 -/
def witnessSymbol {σ : Signature.{u, v, w}} (entry : Entry σ) : σ.FuncSymbol :=
  entry.evidence.witnessSymbol

/-- 当前条目的函数定义域。 -/
def domain {σ : Signature.{u, v, w}} (entry : Entry σ) : SimpleType σ :=
  entry.evidence.domain

/-- 当前条目的函数值域。 -/
def codomain {σ : Signature.{u, v, w}} (entry : Entry σ) : SimpleType σ :=
  entry.evidence.codomain

/-- 当前条目对应的左函数项。 -/
def left {σ : Signature.{u, v, w}} (entry : Entry σ) : Term σ :=
  entry.evidence.left

/-- 当前条目对应的右函数项。 -/
def right {σ : Signature.{u, v, w}} (entry : Entry σ) : Term σ :=
  entry.evidence.right

/-- 见证符号必须具有 canonical `diff` 类型。 -/
def signatureCheck {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (entry : Entry σ) : Bool :=
  σ.isFunctionExtensionalityWitness entry.witnessSymbol &&
    decide
      (σ.funcDomain entry.witnessSymbol =
        [.arrow entry.domain entry.codomain, .arrow entry.domain entry.codomain]) &&
    decide (σ.funcCodomain entry.witnessSymbol = entry.domain)

/-- 见证符号类型检查的逻辑解包。 -/
theorem signatureCheck_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {entry : Entry σ} (hCheck : entry.signatureCheck = true) :
    σ.isFunctionExtensionalityWitness entry.witnessSymbol = true ∧
      σ.funcDomain entry.witnessSymbol =
        [.arrow entry.domain entry.codomain, .arrow entry.domain entry.codomain] ∧
      σ.funcCodomain entry.witnessSymbol = entry.domain := by
  have hFields :
      (σ.isFunctionExtensionalityWitness entry.witnessSymbol = true ∧
        σ.funcDomain entry.witnessSymbol =
          [.arrow entry.domain entry.codomain, .arrow entry.domain entry.codomain]) ∧
        σ.funcCodomain entry.witnessSymbol = entry.domain := by
    simpa [signatureCheck] using hCheck
  exact ⟨hFields.1.1, hFields.1.2, hFields.2⟩

/-- 见证符号没有出现在原始初始字句中。 -/
def SourceFresh {σ : Signature.{u, v, w}} [DecidableEq σ.FuncSymbol]
    (problem : HODAGCertificate.Problem σ) (entry : Entry σ) : Prop :=
  ∀ clause, clause ∈ problem.initialClauses.toList →
    Syntax.clauseContainsFunction entry.witnessSymbol clause = false

/-- 初始问题中的见证新鲜性检查。 -/
def sourceFreshCheck {σ : Signature.{u, v, w}} [DecidableEq σ.FuncSymbol]
    (problem : HODAGCertificate.Problem σ) (entry : Entry σ) : Bool :=
  problem.initialClauses.toList.all fun clause =>
    !Syntax.clauseContainsFunction entry.witnessSymbol clause

/-- 初始问题新鲜性检查的逻辑解包。 -/
theorem sourceFreshCheck_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.FuncSymbol] {problem : HODAGCertificate.Problem σ}
    {entry : Entry σ} (hCheck : entry.sourceFreshCheck problem = true) :
    entry.SourceFresh problem := by
  intro clause hClause
  have hFresh :=
    List.all_eq_true.mp hCheck clause hClause
  simpa using hFresh

/-- 见证符号没有出现在其生成节点之前的任何机械结论中。 -/
def PriorFresh {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (entry : Entry σ) : Prop :=
  ∀ node, node ∈ dag.nodes.toList → node.id < entry.nodeId →
    ∃ clause, node.conclusion? dag.problem = some clause ∧
      Syntax.clauseContainsFunction entry.witnessSymbol clause = false

/-- 生成节点之前的见证新鲜性检查。 -/
def priorFreshCheck {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (entry : Entry σ) : Bool :=
  dag.nodes.toList.all fun node =>
    if node.id < entry.nodeId then
      match node.conclusion? dag.problem with
      | some clause => !Syntax.clauseContainsFunction entry.witnessSymbol clause
      | none => false
    else
      true

/-- 先前节点新鲜性检查的逻辑解包。 -/
theorem priorFreshCheck_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {entry : Entry σ}
    (hCheck : entry.priorFreshCheck dag = true) :
    entry.PriorFresh dag := by
  intro node hNode hBefore
  have hNodeCheck :=
    List.all_eq_true.mp hCheck node hNode
  rw [if_pos hBefore] at hNodeCheck
  cases hConclusion : node.conclusion? dag.problem with
  | none =>
      simp [hConclusion] at hNodeCheck
  | some clause =>
      refine ⟨clause, rfl, ?_⟩
      simpa [hConclusion] using hNodeCheck

/-- 一条 witness entry 的完整新鲜性合同。 -/
def Fresh {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (entry : Entry σ) : Prop :=
  entry.SourceFresh dag.problem ∧ entry.PriorFresh dag

/-- 一条 witness entry 的完整新鲜性检查。 -/
def freshCheck {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (entry : Entry σ) : Bool :=
  entry.sourceFreshCheck dag.problem && entry.priorFreshCheck dag

/-- 完整新鲜性检查的逻辑解包。 -/
theorem freshCheck_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {entry : Entry σ}
    (hCheck : entry.freshCheck dag = true) :
    entry.Fresh dag := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hSource, hPrior⟩
  exact ⟨sourceFreshCheck_sound hSource, priorFreshCheck_sound hPrior⟩

end Entry

/-- 全图中的显式外延见证条目。 -/
structure Registry (σ : Signature.{u, v, w}) where
  entries : List (Entry σ)

namespace Registry

/-- 从真实 HO-DAG payload 抽取全部外延见证条目。 -/
def ofDAG {σ : Signature.{u, v, w}} (dag : DAG σ) : Registry σ := {
  entries := dag.nodes.toList.filterMap Entry.ofNode?
}

end Registry

namespace SourceProblem

/-- 初始问题中不出现任何签名标记的外延见证符号。 -/
def WitnessFree {σ : Signature.{u, v, w}}
    (problem : HODAGCertificate.Problem σ) : Prop :=
  ∀ (index : Nat) (clause : Clause σ), problem.initialClauses[index]? = some clause →
    Syntax.clauseWitnessFree clause

/-- 初始问题外延见证无关性的可计算检查。 -/
def witnessFreeCheck {σ : Signature.{u, v, w}}
    (problem : HODAGCertificate.Problem σ) : Bool :=
  problem.initialClauses.toList.all Syntax.clauseWitnessFree

/-- 初始问题检查成功时，所有 source clause 都不含外延见证符号。 -/
theorem witnessFreeCheck_sound {σ : Signature.{u, v, w}}
    {problem : HODAGCertificate.Problem σ}
    (hCheck : SourceProblem.witnessFreeCheck problem = true) :
    SourceProblem.WitnessFree problem := by
  intro index clause hClause
  have hIndex := Array.getElem?_eq_some_iff.mp hClause |>.1
  have hGet := Array.getElem?_eq_some_iff.mp hClause |>.2
  have hMember : clause ∈ problem.initialClauses.toList := by
    simpa [hGet] using Array.getElem_mem hIndex
  exact List.all_eq_true.mp hCheck clause hMember

end SourceProblem

namespace Registry

/-- 相同见证符号不能由两个独立 DAG 节点重复声明。 -/
def PairwiseSymbolUnique {σ : Signature.{u, v, w}} :
    List (Entry σ) → Prop
  | [] => True
  | head :: rest =>
      (∀ other, other ∈ rest → head.witnessSymbol ≠ other.witnessSymbol) ∧
        PairwiseSymbolUnique rest

/-- 见证符号两两唯一的可计算检查。 -/
def pairwiseSymbolUniqueCheck {σ : Signature.{u, v, w}}
    [DecidableEq σ.FuncSymbol] : List (Entry σ) → Bool
  | [] => true
  | head :: rest =>
      (rest.all fun other => decide (head.witnessSymbol ≠ other.witnessSymbol)) &&
        pairwiseSymbolUniqueCheck rest

/-- 见证符号唯一性检查的逻辑解包。 -/
theorem pairwiseSymbolUniqueCheck_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.FuncSymbol] {entries : List (Entry σ)}
    (hCheck : pairwiseSymbolUniqueCheck entries = true) :
    PairwiseSymbolUnique entries := by
  induction entries with
  | nil =>
      trivial
  | cons head rest ih =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hHead, hRest⟩
      constructor
      · intro other hOther
        simpa using List.all_eq_true.mp hHead other hOther
      · exact ih hRest

/-- 注册表的全局结构合同。 -/
structure Contract {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (registry : Registry σ) : Prop where
  sourceWitnessFree : SourceProblem.WitnessFree dag.problem
  signature :
    ∀ entry, entry ∈ registry.entries →
      σ.isFunctionExtensionalityWitness entry.witnessSymbol = true ∧
        σ.funcDomain entry.witnessSymbol =
          [.arrow entry.domain entry.codomain, .arrow entry.domain entry.codomain] ∧
        σ.funcCodomain entry.witnessSymbol = entry.domain
  fresh :
    ∀ entry, entry ∈ registry.entries → entry.Fresh dag
  pairwiseUnique : PairwiseSymbolUnique registry.entries

/-- 全局注册表 checker。 -/
def check {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (registry : Registry σ) : Bool :=
  (SourceProblem.witnessFreeCheck dag.problem &&
      registry.entries.all fun entry =>
        entry.signatureCheck && entry.freshCheck dag) &&
      pairwiseSymbolUniqueCheck registry.entries

/-- 全局注册表 checker 的逻辑解包。 -/
theorem check_sound {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} {registry : Registry σ}
    (hCheck : registry.check dag = true) :
    Contract dag registry := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hEntries, hUnique⟩
  rcases Bool.and_eq_true_iff.mp hEntries with ⟨hSource, hEntries⟩
  refine {
    sourceWitnessFree :=
      SourceProblem.witnessFreeCheck_sound (σ := σ) hSource
    signature := ?_
    fresh := ?_
    pairwiseUnique := pairwiseSymbolUniqueCheck_sound hUnique
  }
  · intro entry hEntry
    have hEntryCheck := List.all_eq_true.mp hEntries entry hEntry
    exact Entry.signatureCheck_sound (Bool.and_eq_true_iff.mp hEntryCheck).1
  · intro entry hEntry
    have hEntryCheck := List.all_eq_true.mp hEntries entry hEntry
    exact Entry.freshCheck_sound (Bool.and_eq_true_iff.mp hEntryCheck).2

/-- 某个真实函数外延节点必然出现在从整图抽取的注册表中。 -/
theorem ofEvidence_mem_ofDAG {σ : Signature.{u, v, w}} {dag : DAG σ}
    {node : Node σ} {evidence : WitnessEvidence σ}
    (hNode : node ∈ dag.nodes.toList)
    (hPayload : node.payload = .functionExtensionality evidence) :
    Entry.ofEvidence node.id evidence ∈ (ofDAG dag).entries := by
  apply List.mem_filterMap.mpr
  exact ⟨node, hNode, by simp [Entry.ofNode?, hPayload, Entry.ofEvidence]⟩

/-- 抽取条目一定来自某个真实 DAG 函数外延节点。 -/
theorem exists_node_of_mem_ofDAG {σ : Signature.{u, v, w}} {dag : DAG σ}
    {entry : Entry σ} (hEntry : entry ∈ (ofDAG dag).entries) :
    ∃ node, node ∈ dag.nodes.toList ∧ Entry.ofNode? node = some entry :=
  List.mem_filterMap.mp hEntry

end Registry

/-- 已检查 DAG 的 canonical 外延见证注册表。 -/
structure CheckedRegistry {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG σ) where
  registry : Registry σ
  extracted : registry = Registry.ofDAG cert.dag
  checked : registry.check cert.dag = true

namespace CheckedRegistry

/-- 从 checked HO-DAG 构造并立即检查 canonical registry。 -/
def mk? {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG σ) : Option (CheckedRegistry cert) :=
  let registry := Registry.ofDAG cert.dag
  if hCheck : registry.check cert.dag = true then
    some {
      registry := registry
      extracted := rfl
      checked := hCheck
    }
  else
    none

/-- 已检查 registry 的全局逻辑合同。 -/
theorem contract {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {cert : CheckedDAG σ} (registry : CheckedRegistry cert) :
    Registry.Contract cert.dag registry.registry :=
  Registry.check_sound registry.checked

/-- checked DAG 中的函数外延节点可在 canonical registry 中定位。 -/
theorem ofEvidence_mem {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {cert : CheckedDAG σ} (registry : CheckedRegistry cert)
    {node : Node σ} {evidence : WitnessEvidence σ}
    (hNode : node ∈ cert.dag.nodes.toList)
    (hPayload : node.payload = .functionExtensionality evidence) :
    Entry.ofEvidence node.id evidence ∈ registry.registry.entries := by
  rw [registry.extracted]
  exact Registry.ofEvidence_mem_ofDAG hNode hPayload

/-- checked registry 中的任意条目都可回溯到真实函数外延节点。 -/
theorem exists_node_of_mem {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {cert : CheckedDAG σ} (registry : CheckedRegistry cert)
    {entry : Entry σ} (hEntry : entry ∈ registry.registry.entries) :
    ∃ node, node ∈ cert.dag.nodes.toList ∧ Entry.ofNode? node = some entry := by
  rw [registry.extracted] at hEntry
  exact Registry.exists_node_of_mem_ofDAG hEntry

end CheckedRegistry

end HOExtensionalWitnessRegistry
end Automation
end YesMetaZFC
