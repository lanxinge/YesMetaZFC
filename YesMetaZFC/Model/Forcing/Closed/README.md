# 内部可数闭力迫

ZF＋DC 中由可数闭性证明可数分配性；另保留 ZFC 下的名称下降链与实际 proper club。
不加实数、旧值序列和可数子集，以及 ω₁ 保持的公共证明已迁至
[Distributive](../Distributive/README.md)，仅需 ZF 与可数分配性。

[总索引](../INDEX.md)

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [Basic.lean](Basic.lean) | `InternalClosed.lean` | 模型内部可数闭性；ZF＋DC 证明 `closed_distributive_l` |
| [Syntax.lean](Syntax.lean) | `InternalClosedSyntax.lean` | 内部可数闭性的原公式 |
| [Sequence.lean](Sequence.lean) | `InternalClosedSequence.lean` | 固定条件下名称下降链的逐项装配 |
| [Name.lean](Name.lean) | `InternalClosedName.lean` | 被迫可数闭偏序中的同条件下界名称 |
| [Master.lean](Master.lean) | `InternalClosedMaster.lean` | 可数闭偏序的实际内部主下降链 |
| [Proper.lean](Proper.lean) | `InternalClosedProper.lean` | 内部可数闭偏序的 properness |
| [ProperName.lean](ProperName.lean) | `InternalClosedProperName.lean` | 可数闭名称的实际 properness 力迫证书 |
| [Extension.lean](Extension.lean) | `InternalClosedExtension.lean` | 从公共分配性层装配 ZFC 闭扩张，并追加 proper 共尾性保持 |
