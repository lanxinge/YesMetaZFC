# 嵌入与解释

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [AttemptRelative](AttemptRelative.lean) | 完整初等嵌入的有限尝试；从总尝试枝解码完整初等嵌入；尝试节点的原公式；完整初等性检验与有限真值证书 |
| [Elementary](Elementary.lean) | 内部初等性的装配、复合与理论保持 |
| [ElementarySyntax](ElementarySyntax.lean) | 内部子结构与完整初等性 |
| [ElementaryTrace](ElementaryTrace.lean) | 任意内部 κ 小种子的实际初等子模型；指定内部 club 中的实际初等模型；内部初等小模型在指定子集上的实际 club |
| [PredicateTrace](PredicateTrace.lean) | 带集合谓词的内部初等嵌入；内部嵌入对原公式的实际作用；原内部初等图的实际模型映射；从谓词结构嵌入读取原集合论公式 |
| [Range](Range.lean) | 实际内部初等映射的复合；同一实际像的两个表示之间传递初等性 |
| [RankFixed](RankFixed.lean) | 初等映射固定内部自然数并搬运有限函数；初等映射在序数上不下降；初等像中可数集合的逐元素回收；逐点固定载体上的集合与图 |
| [Reflect](Reflect.lean) | 成员满嵌入保持集合模型之间的完整内部初等图；成员满包含反射完整内部初等图 |
| [Relative](Relative.lean) | 拥有集合中的原公式沿外层初等图回拉 |
| [Theory](Theory.lean) | 原关系初等图保持所属结构的实际理论 |
