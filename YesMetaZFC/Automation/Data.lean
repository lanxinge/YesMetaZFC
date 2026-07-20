import YesMetaZFC.Automation.Data.Util
import YesMetaZFC.Automation.Data.Fixpoint
import YesMetaZFC.Automation.Data.Packed
import YesMetaZFC.Automation.Data.Arena
import YesMetaZFC.Automation.Data.OpenAddress
import YesMetaZFC.Automation.Data.Intern
import YesMetaZFC.Automation.Data.BitSet
import YesMetaZFC.Automation.Data.Signature
import YesMetaZFC.Automation.Data.Sparse
import YesMetaZFC.Automation.Data.FifoQueue
import YesMetaZFC.Automation.Data.Heap
import YesMetaZFC.Automation.Data.Watch
import YesMetaZFC.Automation.Data.ClauseArena
import YesMetaZFC.Automation.Data.ClauseMetadata
import YesMetaZFC.Automation.Data.GivenWorkspace
import YesMetaZFC.Automation.Data.ModelRoundWorkspace
import YesMetaZFC.Automation.Data.StableIdLiveness
import YesMetaZFC.Automation.Data.StableIdMap
import YesMetaZFC.Automation.Data.CanonicalSeedWorkspace
import YesMetaZFC.Automation.Data.BranchHeap
import YesMetaZFC.Automation.Data.ConflictWorkspace
import YesMetaZFC.Automation.Data.Replay
import YesMetaZFC.Automation.Data.CertificateWorkspace

/-!
# ATP 底层数据结构标准库

本聚合模块提供与对象逻辑、LCF replay 和 `prove_auto` 语法无关的纯数据结构。
下游后端应在各自实例层把 `CoreSyntax.Search`、CDCL literal 或 source provider item
映射到这些结构，而不是让底层模块 import 上层证明内核。

实现分为五层：

1. `Util`/`Packed`：原子所有权操作、紧凑字节和 unboxed handle；
2. 冻结值：只读边界、最终结果与冷路径函数式变换；
3. `*.Builder`：单次搜索 region 内的可变状态，热循环只在这一层更新；
4. `Arena`/`Slab`/`NatMap`/`InternTable`：稳定 handle、连续载荷与开放寻址索引；
5. `ClauseArena`/`WatchTable`/`BranchHeap`：CDCL 与 ATP 后端直接消费的专用结构。

builder 的 `freeze` 是 region 结束边界；冻结后不应再更新同一个 builder，也不应把热状态
数组写入 trace 或历史快照。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

end Data
end Automation
end YesMetaZFC
