import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.Clause
import YesMetaZFC.Automation.DAGCertificate.CompileRenaming

/-!
# 局部规则回放的公共边界

本模块集中消去局部规则反复承担的三类义务：从节点契约抽取 checker 等式、经父快照
定位 compiled 父字句、以及把节点 payload 支持集上的 raw 替换一次编译为 typed 替换。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace IntrinsicReplay

open _root_.YesMetaZFC.Logic

variable {σ : Signature}
variable [DecidableEq σ.SortSymbol]
variable [DecidableEq σ.FuncSymbol]
variable [DecidableEq σ.RelSymbol]

/-- 实际 local payload 的具体 evidence 直接取得局部 checker 等式。 -/
theorem localRule_check_of_payload
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (evidence : LocalRuleEvidence σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = evidence) :
    evidence.check (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
  have hPayloadCheck :=
    (cert.contract.node_contract index hIndex).payload_checked
  rw [hPayload] at hPayloadCheck
  change payload.check (cert.dag.nodeAt index hIndex).parents
    (cert.dag.nodeAt index hIndex).conclusion = true at hPayloadCheck
  have hLocalCheck := (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp hPayloadCheck).1).2
  rw [hEvidence] at hLocalCheck
  exact hLocalCheck

/-- 实际父边与 payload 父快照共同确定唯一 compiled 父字句。 -/
theorem parent_compiled_raw
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (parent : ParentClause σ)
    (hParentMem :
      parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList)
    (hParentPayloadMem :
      parent ∈
        (cert.dag.nodeAt index hIndex).payload.parentClauses.toList) :
    ∃ hParentIndex : parent.id < cert.dag.nodes.size,
      (compiled.nodeAt parent.id hParentIndex).raw = parent.clause := by
  have hParentBefore : parent.id < index :=
    cert.contract.parents_before index hIndex parent.id hParentMem
  have hParentIndex : parent.id < cert.dag.nodes.size :=
    Nat.lt_trans hParentBefore hIndex
  have hNodeSnapshots :
      cert.dag.nodeParentSnapshotsChecked
        (cert.dag.nodeAt index hIndex) = true := by
    have hAll := Array.all_eq_true.mp
      cert.contract.parent_snapshots_checked
    simpa [DAG.parentSnapshotsChecked, DAG.nodeAt] using! hAll index hIndex
  have hSnapshot : cert.dag.parentSnapshotChecked parent = true := by
    change (cert.dag.nodeAt index hIndex).payload.parentClauses.all
      (fun candidate => cert.dag.parentSnapshotChecked candidate) = true at hNodeSnapshots
    exact array_check_of_mem hNodeSnapshots hParentPayloadMem
  exact ⟨hParentIndex,
    parent_compiled_raw_of_snapshot compiled parent hParentIndex hSnapshot⟩

/-- 节点 payload 覆盖替换支持时，唯一整图 registry 上的 typed 编译必成功。 -/
theorem compileSubstitution?_exists_of_nodeSupport
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (substitution : TermSubstitution σ)
    (hWellSorted : TermSubstitution.WellSorted substitution)
    (hSupport : ∀ entry, entry ∈ substitution.freeSupport →
      entry ∈ (cert.dag.nodeAt index hIndex).payload.freeSupport) :
    ∃ target,
      Compile.compileSubstitution? compiled.compilation.registry substitution =
        some target := by
  apply Compile.compileSubstitution?_exists_of_wellSorted_of_support
    compiled.compilation.registry substitution hWellSorted
  intro entry hEntry
  have hReplaySupport : entry ∈ cert.dag.replaySupport :=
    DAG.mem_replaySupport_of_node_payload cert.dag index hIndex
      (hSupport entry hEntry)
  rw [compiled.compilation.registry_eq]
  exact Compile.FreeRegistry.mem_entries_of_mem_support hReplaySupport

/-- 节点 payload 覆盖 offset 目标支持时，整图 registry 上的 typed 改名必成功。 -/
theorem compileRenaming?_exists_of_nodeSupport
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (support : List (σ.SortSymbol × Nat)) (offset : Nat)
    (hTargetSupport : ∀ entry, entry ∈ support →
      (entry.1, entry.2 + offset) ∈
        (cert.dag.nodeAt index hIndex).payload.freeSupport) :
    ∃ ρ,
      Compile.compileRenaming? compiled.compilation.registry support offset =
        some ρ := by
  apply Compile.compileRenaming?_exists_of_support
  intro entry hEntry
  have hReplaySupport :
      (entry.1, entry.2 + offset) ∈ cert.dag.replaySupport :=
    DAG.mem_replaySupport_of_node_payload cert.dag index hIndex
      (hTargetSupport entry hEntry)
  rw [compiled.compilation.registry_eq]
  exact Compile.FreeRegistry.mem_entries_of_mem_support hReplaySupport

end IntrinsicReplay
end DAGCertificate
end Automation
end YesMetaZFC
