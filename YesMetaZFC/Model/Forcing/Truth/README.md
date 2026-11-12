# 真值与语义

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [ClosedTruth](ClosedTruth.lean) | 有限地参数的 check 赋值及力迫规则；只消费有限名字参数的原力迫真值定理 |
| [Definability](Definability.lean) | 模型内条件序与外部泛型滤子；实际公式的可定义条件集与泛型取见证 |
| [OrderCongruence](OrderCongruence.lean) | 不依赖泛型选择的内部力迫规则；局部等号替换与有界存在见证；条件域上的序关系决定全部名称力迫 |
| [Truth](Truth.lean) | 原 Project 公式的内部力迫翻译；内部正则真值的逻辑运算；全部原公式的内部力迫真值定理 |
