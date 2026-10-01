# 二步原子对应

二步等号与嵌套等号的双向匹配及保留首阶段泛型的见证。

[总索引](../../INDEX.md) · [上级目录](../README.md)

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [Syntax.lean](Syntax.lean) | `TwoStepAtomicSyntax.lean` | 二步名称等号传输的内部归纳公式 |
| [Witness.lean](Witness.lean) | `TwoStepAtomicWitness.lean` | 保留首阶段泛型的二步等号匹配 |
| [Match.lean](Match.lean) | `TwoStepAtomicMatch.lean` | 两阶段等号的子名称匹配 |
| [PullSyntax.lean](PullSyntax.lean) | `TwoStepAtomicPullSyntax.lean` | 反向二步等号传输的内部双模拟谓词 |
| [PullMatch.lean](PullMatch.lean) | `TwoStepAtomicPullMatch.lean` | 嵌套等号的第二阶段匹配提升 |
| [Push.lean](Push.lean) | `TwoStepAtomicPush.lean` | 二步等号力迫向嵌套等号力迫传输 |
| [Pull.lean](Pull.lean) | `TwoStepAtomicPull.lean` | 嵌套等号反射为原二步等号 |
