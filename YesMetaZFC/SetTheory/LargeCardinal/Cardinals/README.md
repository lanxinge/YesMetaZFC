# 大基数基础与初始源

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [DerivedPredicate](DerivedPredicate.lean) | 从实际初等嵌入派生内部超滤；派生测度的有界真值集合；源内部子集与源内部函数上的实际分量；派生测度上的原嵌入求值 |
| [EmbeddingCountableBound](EmbeddingCountableBound.lean) | 模型内可数嵌入的序数限制具有实际小界 |
| [EmbeddingSetImage](EmbeddingSetImage.lean) | 全内部初等图在源内集合上的限制；原关系结构及其完整像的实际坐标双射 |
| [ExternalBookkeeping](ExternalBookkeeping.lean) | 外部代码的相容 bookkeeping |
| [ExternalFunctionSection](ExternalFunctionSection.lean) | 外部 host 函数的显式 section |
| [FiniteArithmeticSource](FiniteArithmeticSource.lean) | 有限读出层中原自然数加法与轮次奇偶的绝对性 |
| [JointFiber](JointFiber.lean) | 可数个有限支撑的统一坐标列；全部有限支撑的定向索引；有限支撑测度的共同约束；共同纤维所需的实际层族 |
| [LocalTypeTransportTuple](LocalTypeTransportTuple.lean) | Neeman 定义 3.27：实际局部不可分辨序数；局部不可分辨对象的字典序最小选取；原局部不可分辨点之间的实际高度间隔；局部不可分辨序数间有限后继秩层的完整类型搬运 |
| [RankCover](RankCover.lean) | 原强嵌入的像历史在已覆盖秩层处取真实值；秩层最小枚举的有界读取；源中的实际秩层枚举族；为指定秩层实际选择足够长的短扩展器长度 |
| [RelativeRankEnumeration](RelativeRankEnumeration.lean) | 支撑以下的子集一致性恢复同一实际秩段；共同极限秩段在新源中的实际枚举 |
| [RelativeRankSegment](RelativeRankSegment.lean) | 序数上的内部限制恢复整个小传递域上的限制；不可达秩段上的实际限制图；可沿迭代传输的相对秩层枚举 |
| [SourceProjection](SourceProjection.lean) | 临界点派生测度的非主性；临界点严格超过内部 ω；任意派生测度的短交封闭；武丁基数以下的实际可测基数 |
| [SubtypeStretch](SubtypeStretch.lean) | 子类型从前驱伸展提升到原类型伸展 |
| [TreeProjectionTransfer](TreeProjectionTransfer.lean) | 二坐标树的历史筛选；解析正规形到类型投影的第一段重编码；旧实数的投影成员关系回传 |
| [WoodinExtender](WoodinExtender.lean) | 完备测度的源分量内部良基；武丁强嵌入同时产生全部有限支撑测度与分量商结构；武丁基数产生的实际良基分量族；武丁基数产生标准短扩展器 |
| [WoodinInitial](WoodinInitial.lean) | 武丁基数与真类个武丁基数；内部递增 Woodin 序列及每轮吸收参数；真类 Woodin 假设生产原乘积和备用 Woodin；真实 Woodin 在包含它的实际 ZF 极限秩层中仍是 Woodin |
| [WoodinTypeStep](WoodinTypeStep.lean) | 可测基数的正则性；可测基数不可达及武丁基数下方的不可达选择；按指定秩自动选择短扩展器并恢复覆盖与谓词一致性；武丁强扩展器对谓词截面的作用 |
