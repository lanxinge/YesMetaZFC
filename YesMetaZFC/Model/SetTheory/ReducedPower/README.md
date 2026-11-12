# 约化幂与 Łoś

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [Copy](Copy.lean) | 原关系超幂复制的等值集合与商核；两个原关系超幂之间的完整初等复制；两个不同源模型的完整超幂复制 |
| [CopyConstant](CopyConstant.lean) | 常值代表在源映射下的实际保持 |
| [DeltaImage](DeltaImage.lean) | 未坍塌商及其关系像中的完整公式 Łoś；完整关系 Łoś 在传递像中的有界解码 |
| [FullElementary](FullElementary.lean) | 完整测度下既有商投影的全部内部初等性 |
| [FullEmbedding](FullEmbedding.lean) | 完整函数族上任意关系的常值与投影初等性 |
| [Los](Los.lean) | 赋值族在超滤意义下的真值；赋值族的逐点单变量更新；从逐列代表函数读取商赋值；原子真值与商关系的精确对应 |
| [Overview](Overview.lean) | 实际内部约化幂 |
| [Projection](Projection.lean) | 坐标拉回精确保持代表等价；全坐标代表赋值的源内真值集；分量超幂之间的完整初等映射 |
| [ProjectionLaws](ProjectionLaws.lean) | 分量映射的恒等、复合及常值交换律 |
| [RelationApplication](RelationApplication.lean) | 同一原关系商中的函数应用 |
| [RelationCopyClass](RelationCopyClass.lean) | 实际原代表图的商类复制 |
| [RelationCopyPull](RelationCopyPull.lean) | 原关系代表族的一阶规格；原函数码赋值的唯一商像；原关系函数码沿初等图的实际复制；原坐标代表在复制下的精确像 |
| [RelationCrossBounded](RelationCrossBounded.lean) | 原关系共同切片中的全部有界代表 |
| [RelationFormulaImage](RelationFormulaImage.lean) | 原关系商及其初等像中的有限公式 |
| [RelationMeasure](RelationMeasure.lean) | 原关系坐标子集代数的实际逆像 |
| [RelationNormalize](RelationNormalize.lean) | 源内部代表赋值上的 Łoś 原公式；源代表赋值的实际商投影；源内真值逆像的超滤读取；原关系函数码、实际坐标图与商赋值 |
| [RelationPowerCount](RelationPowerCount.lean) | 原关系超幂分量中幂集像的可数性 |
| [RelationProjection](RelationProjection.lean) | 原关系函数码的商赋值与支撑拉回赋值；原关系函数代表沿实际支撑坐标拉回；原关系分量之间的完整内部初等过渡 |
| [RelationRestriction](RelationRestriction.lean) | 原关系代表的测度限制保持同一个商 |
| [RelationSuccessor](RelationSuccessor.lean) | 原关系后继的实际常值初等图；任意原关系源的后继与同一原始模型的复合初等图 |
| [RelationTrace](RelationTrace.lean) | 原关系源全部内部公式码的精确坐标真值集 |
| [Restriction](Restriction.lean) | 限制测度保持同一个源超幂 |
| [SourceComposition](SourceComposition.lean) | 源内部代表沿实际坐标函数的拉回 |
| [SourceFormula](SourceFormula.lean) | 原二元公式在源超幂中的逐点解释 |
| [SourceModel](SourceModel.lean) | 内部约化幂的几乎处处关系；模型内的函数等价类集合与投影；约化幂的实际内部结构码；实际代表图下降到商图 |
| [SourceProjection](SourceProjection.lean) | 源中的实际逆像与代表相等集 |
