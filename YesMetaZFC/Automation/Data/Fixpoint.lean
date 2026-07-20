import YesMetaZFC.Automation.Data.Util

/-!
# RC 友好的不动点工作区

饱和搜索中的规范化循环通常会反复替换一份携带大型 arena、索引和日志数组的状态。
若调用方在更新前后同时保留纯值快照，Lean 的引用计数会让后续数组更新退化为整段复制。

本模块把热状态放入 `ST.Ref`，并通过一次 `modifyGet` 完成“取出旧状态、计算下一状态、
写回新状态”。它不依赖具体证明语法；搜索器只需提供单步状态转换。
-/

namespace YesMetaZFC
namespace Automation
namespace Data
namespace Fixpoint

/-- 单次不动点推进的控制结果。 -/
inductive Step (α : Type) where
  /-- 当前状态已经是规范形。 -/
  | done (state : α)
  /-- 外部工作预算耗尽；保留当前合法状态并显式停止。 -/
  | exhausted (state : α)
  /-- 当前对象应被丢弃，同时保留清理后的最终状态。 -/
  | discard (state : α)
  /-- 接受一次严格推进，继续处理下一状态。 -/
  | next (state : α)

/-- 不动点循环的停止原因。 -/
inductive Outcome where
  | normal
  | exhausted
  | discarded
  deriving Repr, BEq, DecidableEq, Inhabited

/-- 不动点循环的冻结结果。 -/
structure Result (α : Type) where
  state : α
  outcome : Outcome
  iterations : Nat

/-- 单次 ST region 内的不动点工作区。 -/
structure Workspace (σ : Type) (α : Type) where
  state : ST.Ref σ α
  iterations : ST.Ref σ Nat

namespace Workspace

/-- 从初始状态建立工作区。 -/
def create {σ : Type} {α : Type} (initial : α) : ST σ (Workspace σ α) := do
  return {
    state := ← ST.mkRef initial
    iterations := ← ST.mkRef 0
  }

private inductive Control where
  | done
  | exhausted
  | discarded
  | continue

/--
执行不动点热循环。

`modifyGet` 让旧状态在同一个原子更新中被消费；调用方的 `advance` 不应把旧状态写入
外部 trace 或闭包。终止性由具体搜索器保证，通常通过良基项序或显式严格下降检查。
-/
partial def runLoop {σ : Type} {α : Type}
    (workspace : Workspace σ α) (advance : α → Step α) : ST σ Outcome := do
  let control ← workspace.state.modifyGet fun state =>
    match advance state with
    | Step.done state => (Control.done, state)
    | Step.exhausted state => (Control.exhausted, state)
    | Step.discard state => (Control.discarded, state)
    | Step.next state => (Control.continue, state)
  match control with
  | Control.done => return Outcome.normal
  | Control.exhausted => return Outcome.exhausted
  | Control.discarded => return Outcome.discarded
  | Control.continue =>
      workspace.iterations.modify (· + 1)
      runLoop workspace advance

/-- 运行一次不动点 region，并只在结束边界冻结最终状态。 -/
def run {α : Type} (initial : α) (advance : α → Step α) : Result α :=
  runST fun σ => do
    let workspace ← Workspace.create (σ := σ) initial
    let outcome ← workspace.runLoop advance
    return {
      state := ← workspace.state.get
      outcome := outcome
      iterations := ← workspace.iterations.get
    }

end Workspace

end Fixpoint
end Data
end Automation
end YesMetaZFC
