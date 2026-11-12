# 偏序、泛型与尝试树

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [FilterExtension](FilterExtension.lean) | 环境中的实际滤子给出另一成员满扩张中的泛型 |
| [GenericHullCollapse](GenericHullCollapse.lean) | 对原司寇伦图及给定泛型的见证同时闭合的可数壳；实际初等壳中的全局稠密判据；同一初等壳及其泛型的传递坍塌 |
| [GenericTreeGround](GenericTreeGround.lean) | 全部旧全局稠密集的实际集合与幂集编码；内部递降条件列生成的实际滤子；内部可数稠密集族的实际滤子；递降条件和稠密命中位置的有限尝试 |
| [GlobalDense](GlobalDense.lean) | 将局部稠密要求扩充为全局稠密集 |
| [JointParameters](JointParameters.lean) | 联合树的固定参数列 |
| [NameComplete](NameComplete.lean) | 联合枝的共享枚举与全部登记读取；同一壳与原泛型交中的实际递降列及枚举登记；同一可数壳上的两条配套见证枝；任意壳内登记运行生成完整壳泛型 |
| [NameContext](NameContext.lean) | 名字树的全坐标读取及反向构枝；从原联合树一次构造固定名字树及坐标对应 |
| [NameLetters](NameLetters.lean) | 两条见证列和两张登记表的实际配对字母；共享枚举、条件登记及常量登记的实际联合树；联合字母直接读取同一枚举值与条件值；查询实数、联合字母、期限和两个名字位置的实际字母表 |
| [NameSound](NameSound.lean) | 任意名字树分支的实际传递源及同一查询实数 |
| [NameTree](NameTree.lean) | 查询实数与原联合枝的实际名字树 |
| [NameValue](NameValue.lean) | 有限名字检查在同一坍塌泛型中恢复完整实数图 |
| [ProductRight](ProductRight.lean) | 两个地模型条件序的内部积；同一实际积条件序的一阶规格；积偏序右坐标的实际正则嵌入 |
| [QueryAttempt](QueryAttempt.lean) | 有限名字检查读取原源模型自己的力迫关系；固定名字位置与逐位判值期限的有限检查；固定地实数参数及原查询名字的正负力迫；正负根检查读取原源模型的力迫关系 |
| [QueryContext](QueryContext.lean) | 正负子树的分支恰为原名字枝加同一根判定；原泛型接受的正负条件产生同一查询点的真实分支；同一大泛型扩张中原正负树的实际分支；正负根判定反射到读取原查询的同一坍塌泛型 |
| [QueryTree](QueryTree.lean) | 同一名字树中的实际正负子树 |
| [Tree](Tree.lean) | 力迫条件的预序；稠密性与保持不相容的稠密映射；相容性所确定的分离商；有限序列条件 |
| [TreeCertificateSyntax](TreeCertificateSyntax.lean) | 实际树字母、投影图和登记列的有限公式；构枝所用整套有限树证书的原公式 |
