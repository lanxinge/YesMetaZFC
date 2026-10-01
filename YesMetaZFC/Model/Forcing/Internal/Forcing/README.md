# 完整公式力迫

内部条件、可定义条件集、公式翻译、逻辑规则、真值与同余。

[总索引](../../INDEX.md) · [上级目录](../README.md)

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [Conditions.lean](Conditions.lean) | `InternalConditions.lean` | 模型内条件序与外部泛型滤子 |
| [Definability.lean](Definability.lean) | `InternalDefinability.lean` | 实际公式的可定义条件集与泛型取见证 |
| [Formula.lean](Formula.lean) | `InternalFormula.lean` | 原 Project 公式的内部力迫翻译 |
| [Logic.lean](Logic.lean) | `InternalLogic.lean` | 内部正则真值的逻辑运算 |
| [Truth.lean](Truth.lean) | `InternalTruth.lean` | 全部原公式的内部力迫真值定理 |
| [Rules.lean](Rules.lean) | `InternalForcingRules.lean` | 不依赖泛型选择的内部力迫规则 |
| [OrderCongruence.lean](OrderCongruence.lean) | `InternalOrderCongruence.lean` | 条件域上的序关系决定全部名称力迫 |
| [Congruence.lean](Congruence.lean) | `InternalForcingCongruence.lean` | 局部等号替换与有界存在见证 |
