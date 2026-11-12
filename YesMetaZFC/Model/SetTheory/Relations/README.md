# 内部关系与秩层

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [Collapse](Collapse.lean) | 任意良基外延结构的完整内部坍塌同构 |
| [CollectCode](CollectCode.lean) | 原公式在任意编码关系模型中的相对化；关系模型内部函数的实际坐标图；原关系模型中幂集值函数的外部计数；原关系中的函数码与求值 |
| [Collection](Collection.lean) | 小定义域统一化进入原始关系模型 |
| [Composition](Composition.lean) | 原关系模型内部的函数复合 |
| [CompositionGraph](CompositionGraph.lean) | 只以函数图为参数的复合关系 |
| [Constant](Constant.lean) | 原关系中的实际常值与恒等函数 |
| [CrossCapture](CrossCapture.lean) | 两个原关系模型之间的有界函数回收 |
| [CrossMeasure](CrossMeasure.lean) | 完整前驱图上的同一坐标迹；两个原关系切片之间的同一可测族 |
| [CrossProjection](CrossProjection.lean) | 原关系共同切片上的实际函数投影 |
| [FunctionCapture](FunctionCapture.lean) | 共同低层回收原关系的有界函数码 |
| [FunctionFamily](FunctionFamily.lean) | 原始关系模型拥有的全部函数代表 |
| [Hierarchy](Hierarchy.lean) | 原关系共同低层的整个相对秩历史 |
| [LayerComposition](LayerComposition.lean) | 原关系模型中的全部内部有限支撑；全部有限支撑与原模型函数码的实际双射；有限支撑复制与原函数码的像；沿定义域和值域的完整解释回读实际函数 |
| [LayerMeasure](LayerMeasure.lean) | 原关系测度在共同低层上的读取 |
| [LayerSeparation](LayerSeparation.lean) | 完整低层实现上的全内部程序解释；新共同层的全内部分离 |
| [NativeRank](NativeRank.lean) | 完整前驱解释保持实际秩历史；原关系切片上的全称秩识别与内在闭包 |
| [NativeSmemSlice](NativeSmemSlice.lean) | 完整前驱图在两侧原切片上保持全部公式；native slice 到实际隶属载体的公式运输 |
| [OmegaCut](OmegaCut.lean) | 原模型切片与实际关系码的语义一致性；两个原关系模型之间的完整切片解释；同一完整前驱图生产目标切片的传递性与配对闭包；所属模型的有界可数闭性回收到原秩切片 |
| [OmegaEvaluation](OmegaEvaluation.lean) | 原关系中固定定义域上的公式统一化；由实际函数与支撑求值回收整个目标的可数列 |
| [Parity](Parity.lean) | 共同低层实现图的有界公式保持；原关系低层的内在闭包；原关系模型中共同低层的完整解释；良基原关系的完整前驱图在重叠域上唯一 |
| [PointwiseWitness](PointwiseWitness.lean) | 原始关系源中的存在行见证 |
| [RankImage](RankImage.lean) | 原关系秩证书的编码与实际表示读取；原生极限秩段沿指定嵌入的工作像 |
| [RecordImage](RecordImage.lean) | 原关系模型中的完整记录与元组；原关系对象的有序对；原关系反射层中的记录读写；原关系初等边上的完整记录恢复 |
| [Separation](Separation.lean) | 原关系模型中的全内部分离程序 |
| [SeparationSource](SeparationSource.lean) | 原关系源中固定原公式的实际分离 |
| [SliceEmbedding](SliceEmbedding.lean) | 原关系切片之间的完整公式传输 |
| [Small](Small.lean) | 原关系源中的截集与低层子集回收；原关系共同低层的相对幂集识别；共同小容器内新参数的原关系编号 |
| [Ultrafilter](Ultrafilter.lean) | 原关系源实际拥有的子集族；原关系内部测度的实际坐标超滤 |
