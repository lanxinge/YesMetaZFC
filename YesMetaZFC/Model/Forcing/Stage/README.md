# 阶段完全嵌入

完全嵌入、复合、名称搬运、原子对应、泛型回拉及扩张嵌入。

[总索引](../INDEX.md)

## 子目录

| 目录 | 模块数 | 职责 |
| --- | ---: | --- |
| [Atomic](Atomic/README.md) | 4 | 完全嵌入下等号力迫的正向保持与反射。 |
| [NameMap](NameMap/README.md) | 5 | 真实内部搬运图的规格、存在、唯一性、复合和恒等。 |

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [Embedding.lean](Embedding.lean) | `StageEmbedding.lean` | 内部阶段嵌入与极大反链 |
| [Transport.lean](Transport.lean) | `OrderTransport.lean` | 内部偏序的可定义重编码 |
| [Composition.lean](Composition.lean) | `StageComposition.lean` | 阶段完全嵌入的内部复合 |
| [CCC.lean](CCC.lean) | `StageCCC.lean` | CCC 沿实际满阶段嵌入搬运 |
| [Names.lean](Names.lean) | `StageNames.lean` | 阶段完全嵌入的名称搬运 |
| [Reduction.lean](Reduction.lean) | `StageReduction.lean` | 完全嵌入的约减公式与受限加强 |
| [Generic.lean](Generic.lean) | `StageGeneric.lean` | 完全嵌入下泛型滤子的回拉 |
| [Extension.lean](Extension.lean) | `StageExtension.lean` | 阶段泛型扩张之间的实际嵌入 |
