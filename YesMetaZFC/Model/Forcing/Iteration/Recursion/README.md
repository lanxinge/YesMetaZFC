# 内部超限递归

完整历史与实际原公式规则、递归算子、不变式、存在性和唯一性；Rule 也保留首个 Cohen 规则实例。

[总索引](../../INDEX.md) · [上级目录](../README.md)

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [History.lean](History.lean) | `IterationHistory.lean` | 递归历史的两个实际坐标序列 |
| [Rule.lean](Rule.lean) | `IterationRule.lean` | 读取整个内部历史的后继规则 |
| [Syntax.lean](Syntax.lean) | `IterationRecursionSyntax.lean` | 支撑迭代的内部递归算子 |
| [Step.lean](Step.lean) | `IterationRecursionStep.lean` | 递归算子的全定义性与合法一步保持 |
| [InvariantSyntax.lean](InvariantSyntax.lean) | `IterationInvariantSyntax.lean` | 递归轨迹合法性的实际归纳公式 |
| [Invariant.lean](Invariant.lean) | `IterationInvariant.lean` | 任意内部长度递归轨迹的阶段系统不变式 |
| [Basic.lean](Basic.lean) | `IterationRecursion.lean` | 任意内部序数长度的支撑迭代 |
