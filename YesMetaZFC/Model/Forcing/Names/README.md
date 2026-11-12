# Names

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [CheckPools](CheckPools.lean) | 以规范检查名字为直接子名字的实际子集名字库；全部检查基点的统一子集名字库 |
| [Depth](Depth.lean) | 固定深度名称条目的内部下降 |
| [PairConstruction](PairConstruction.lean) | 内部可定义加权名称构造；不依赖泛型的规范名称配对 |
| [PairForcing](PairForcing.lean) | 规范名称配对的全局力迫证书 |
| [Realization](Realization.lean) | 地模型内部的名称谓词；内部名称的递归刻画与集合闭包；内部名称的小图呈现；小图地模型中的实际内部名称 |
| [SequenceForcing](SequenceForcing.lean) | 内部函数图的逐坐标名称装配；实际名称序列的同条件坐标读取 |
