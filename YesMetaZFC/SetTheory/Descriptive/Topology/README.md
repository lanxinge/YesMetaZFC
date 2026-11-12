# 内部描述集合论基础

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [Analytic](Analytic.lean) | 解析集与有码 Borel 集的完美集定理；内部解析层入口 |
| [BorelRank](BorelRank.lean) | Borel 秩公共入口 |
| [Completion](Completion.lean) | 内部前缀尺度的柯西列与极限；前缀距离的规范有理数码；首差坐标与规范有理数距离；内部前缀超度量及距离图 |
| [Continuous](Continuous.lean) | 实际连续函数图及逆像 |
| [ContinuousLift](ContinuousLift.lean) | 将连续映射提升到量词之下：f×id |
| [Projective](Projective.lean) | 解析与射影层入口 |
| [Space](Space.lean) | 模型内部的 Baire 与 Cantor 空间 |
| [Topology](Topology.lean) | 内部柱集及其基性质；由内部有限前缀生成的拓扑 |
