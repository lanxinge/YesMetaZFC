# 内部关系源

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [Basic](Basic.lean) | 原 Project AST 的原子消去 |
| [BinaryRelation](BinaryRelation.lean) | 任意内部二元程序的原关系真值图 |
| [Cantor](Cantor.lean) | 源内 Cantor–Bernstein 构造 |
| [ClosureSyntax](ClosureSyntax.lean) | 原关系中的指定有限序列空间；小定义域收集的原关系保持与实际初值；原关系小集合收集的完整历史编码；有限序列空间在后继模型中的实际保持 |
| [CollectionBasis](CollectionBasis.lean) | 源内单射图的限制证书；源内函数与其图的编号；原关系中的小集合与编号；原关系中的小定义域统一化 |
| [Elementary](Elementary.lean) | 完整内部初等性的原公式调用 |
| [Field](Field.lean) | 实际初等源中的子集代数与限制超滤 |
| [FinitePartial](FinitePartial.lean) | 源模型包含全部背景内部有限函数；有限定义域上的部分图属于源 |
| [InaccessibleSyntax](InaccessibleSyntax.lean) | 任意集合载体上的原公式相对化；内部不可达判断的背景原公式 |
| [OmegaClosed](OmegaClosed.lean) | 源内传递包络；外部下降链的源内反射；枝反射的可定义良基关系；枝反射与统一标签关系的良基性 |
| [Presentation](Presentation.lean) | 塌缩存在句子的源模型闭包与初等保持；源内小关系的传递像及求值图 |
| [RankClosure](RankClosure.lean) | 严格相对秩段的集合代数与层级闭包 |
| [RankSizeInitial](RankSizeInitial.lean) | 相对秩层的实际初始实例与初等传输；模型内的不可数共尾性及其初等保持；秩模型的相对幂集闭包；所属模型中的原始不可达性 |
| [Relation](Relation.lean) | 源内函数值族的逐点求值；向源内枚举加入指定参数；有界分离族的源内函数图；源内部的实际坐标重排图 |
| [Theory](Theory.lean) | 源内基本运算与有界关系选择；原关系中的全内部分离与集合代数 |
| [Transport](Transport.lean) | 不同源之间的代表函数与真值集合搬运 |
