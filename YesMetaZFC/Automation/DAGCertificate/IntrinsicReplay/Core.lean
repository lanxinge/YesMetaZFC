import YesMetaZFC.Automation.DAGCertificate

/-!
# 内在 DAG replay 核

本模块从零语义开销的节点开始：source 与 parent-copy 只依赖 checked 编译唯一性、父边
拓扑和父快照，不引入替换环境或额外良构命题。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace IntrinsicReplay

open _root_.YesMetaZFC.Logic

universe x

variable {σ : Signature}
variable [DecidableEq σ.SortSymbol]
variable [DecidableEq σ.FuncSymbol]
variable [DecidableEq σ.RelSymbol]

/-- 某个 DAG 节点的全局-registry compiled clause 在结构中有效。 -/
def NodeTrueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {dag : DAG σ} (compiled : Compile.CheckedDAGClauses dag)
    (index : Nat) (hIndex : index < dag.nodes.size) : Prop :=
  (compiled.nodeAt index hIndex).TrueIn M

/-- 已检查快照与实际索引唯一确定编译后的父子句，不要求新的父边假设。 -/
theorem parent_compiled_raw_of_snapshot
    {dag : DAG σ} (compiled : Compile.CheckedDAGClauses dag)
    (parent : ParentClause σ) (hIndex : parent.id < dag.nodes.size)
    (hSnapshot : dag.parentSnapshotChecked parent = true) :
    (compiled.nodeAt parent.id hIndex).raw = parent.clause := by
  rcases DAG.parentSnapshotChecked_sound hSnapshot with ⟨node, hNode, hClause⟩
  have hEq : node = dag.nodeAt parent.id hIndex :=
    Option.some.inj (hNode.symm.trans (dag.node?_eq_some_nodeAt hIndex))
  subst node
  exact (compiled.nodeAt_raw parent.id hIndex).trans hClause

/-- source 节点从同索引初始 compiled clause 直接取得真实性。 -/
theorem source_trueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (hInitial : ∀ target ∈ compiled.compilation.initialClauses.toList,
      target.TrueIn M)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (initialIndex : Nat)
    (hCheck : Payload.check cert.dag.problem
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion
      (.source initialIndex) = true) :
    NodeTrueIn M compiled index hIndex := by
  simp only [Payload.check, Bool.and_eq_true_iff] at hCheck
  cases hInitialRaw : cert.dag.problem.initialClauses[initialIndex]? with
  | none => simp [hInitialRaw] at hCheck
  | some raw =>
      have hConclusion :
          (cert.dag.nodeAt index hIndex).conclusion = raw :=
        Clause.eq_sound _ _ (by simpa [hInitialRaw] using hCheck.2)
      rcases Array.getElem?_eq_some_iff.mp hInitialRaw with
        ⟨hInitialIndex, hInitialGet⟩
      let initialCompiled := compiled.initialAt initialIndex hInitialIndex
      have hInitialTrue : initialCompiled.TrueIn M := by
        apply hInitial
        exact Array.getElem_mem_toList (by
          simpa [compiled.initial_size] using hInitialIndex)
      have hInitialRawEq : initialCompiled.raw = raw := by
        rw [Compile.CheckedDAGClauses.initialAt_raw]
        exact hInitialGet
      have hNodeRaw :
          (compiled.nodeAt index hIndex).raw = initialCompiled.raw :=
        (compiled.nodeAt_raw index hIndex).trans <|
          hConclusion.trans hInitialRawEq.symm
      exact (Compile.CompiledClause.trueIn_iff_of_raw_eq M hNodeRaw).mpr
        hInitialTrue

/-- parent-copy 节点只经父快照传输同一 raw 字句的真实性。 -/
theorem parentCopy_trueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (parent : ParentClause σ)
    (hCheck : LocalRuleEvidence.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion
      (.parentCopy parent) = true)
    (hSnapshot : cert.dag.parentSnapshotChecked parent = true)
    (hParent : ∀ hParentIndex : parent.id < cert.dag.nodes.size,
      NodeTrueIn M compiled parent.id hParentIndex) :
    NodeTrueIn M compiled index hIndex := by
  have hParentMem :
      parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn <|
      LocalRuleEvidence.parentIdCheck_of_check hCheck
        (by simp [LocalRuleEvidence.parentClauses])
  have hParentBefore : parent.id < index :=
    cert.contract.parents_before index hIndex parent.id hParentMem
  have hParentIndex : parent.id < cert.dag.nodes.size :=
    Nat.lt_trans hParentBefore hIndex
  have hConclusion :
      (cert.dag.nodeAt index hIndex).conclusion = parent.clause :=
    LocalRuleEvidence.parentCopy_check_sound <|
      LocalRuleEvidence.ruleCheck_of_check hCheck
  have hParentRaw := parent_compiled_raw_of_snapshot compiled parent hParentIndex hSnapshot
  have hNodeRaw :
      (compiled.nodeAt index hIndex).raw =
        (compiled.nodeAt parent.id hParentIndex).raw :=
    (compiled.nodeAt_raw index hIndex).trans <|
      hConclusion.trans hParentRaw.symm
  exact (Compile.CompiledClause.trueIn_iff_of_raw_eq M hNodeRaw).mpr
    (hParent hParentIndex)

end IntrinsicReplay
end DAGCertificate
end Automation
end YesMetaZFC
