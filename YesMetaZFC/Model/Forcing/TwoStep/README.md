# 二步迭代

实际二步偏序、名称转换、泛型分解、扩张同构及 CCC、proper、可数闭保持。

[总索引](../INDEX.md)

## 子目录

| 目录 | 模块数 | 职责 |
| --- | ---: | --- |
| [Atomic](Atomic/README.md) | 7 | 二步等号与嵌套等号的双向匹配及保留首阶段泛型的见证。 |
| [CCC](CCC/README.md) | 5 | 实际反链索引名称、可数性力迫与任意名称后继的 CCC 保持。 |
| [Flatten](Flatten/README.md) | 7 | 嵌套名称的内部摊平递归、存在性、求值还原和反向实现。 |
| [Generic](Generic/README.md) | 6 | 首阶段投影、第二阶段分解、稠密集提升与两阶段泛型组合恢复。 |
| [Names](Names/README.md) | 7 | 二步名称转换的递归和存在证明，名称性、求值及单次与双重扩张同构。 |
| [Proper](Proper/README.md) | 11 | 主条件合成、首阶段投影、N[G] 第二坐标主性、双向分解与实际主加强。 |

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [Basic.lean](Basic.lean) | `TwoStep.lean` | 任意名称偏序的二步迭代 |
| [Class.lean](Class.lean) | `TwoStepClass.lean` | 全部条件名称上的二步序 |
| [Order.lean](Order.lean) | `TwoStepOrder.lean` | 地模型内的二步条件集与序关系装配 |
| [Top.lean](Top.lean) | `TwoStepTop.lean` | 后继阶段的顶名称 |
| [Embedding.lean](Embedding.lean) | `TwoStepEmbedding.lean` | 二步迭代的实际阶段完全嵌入 |
| [Presentation.lean](Presentation.lean) | `TwoStepPresentation.lean` | 二步装配证书的原公式呈现 |
| [Witness.lean](Witness.lean) | `TwoStepWitness.lean` | 首坐标不变的二步见证 |
| [Closed.lean](Closed.lean) | `TwoStepClosed.lean` | 可数闭二步迭代及固定首坐标的下界 |
