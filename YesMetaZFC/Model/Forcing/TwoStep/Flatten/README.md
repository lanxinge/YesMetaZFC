# 名称摊平

嵌套名称的内部摊平递归、存在性、求值还原和反向实现。

[总索引](../../INDEX.md) · [上级目录](../README.md)

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [Syntax.lean](Syntax.lean) | `TwoStepFlatSyntax.lean` | 二步名称摊平的内部递归规格 |
| [Recursion.lean](Recursion.lean) | `TwoStepFlatRecursion.lean` | 三层条目递归的唯一性及部分图装配 |
| [Construction.lean](Construction.lean) | `TwoStepFlatConstruction.lean` | 原 ZF 内二步名称摊平的实际构造 |
| [RoundSyntax.lean](RoundSyntax.lean) | `TwoStepFlatRoundSyntax.lean` | 名称摊平后求值还原的内部归纳公式 |
| [RoundMatch.lean](RoundMatch.lean) | `TwoStepFlatRoundMatch.lean` | 摊平后第二阶段等号的双向条目匹配 |
| [Round.lean](Round.lean) | `TwoStepFlatRound.lean` | 摊平后求值还原的全局证明 |
| [Value.lean](Value.lean) | `TwoStepFlatValue.lean` | 任意第二阶段名称由摊平名称实现 |
