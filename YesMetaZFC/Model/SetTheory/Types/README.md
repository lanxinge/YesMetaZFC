# 内部类型与弹性

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [CanonicalCode](CanonicalCode.lean) | 现有内部指令的规范自然数编码；全部内部公式的规范自然数码与双向编码表 |
| [CanonicalSatisfaction](CanonicalSatisfaction.lean) | 规范自然数码上的统一满足关系 |
| [CanonicalSource](CanonicalSource.lean) | 合法程序的逐行自然数编码在极限秩层中绝对；全部内部公式的规范自然数解码在极限秩层中绝对 |
| [DropEmbedding](DropEmbedding.lean) | 裸类型的原语法投影与 dcp；投影查询与原完整满足关系一致；删除末位后仍为原前缀的完整类型；实际增加末位与 dcp 互逆 |
| [Embedding](Embedding.lean) | 实现元组的完整内部类型；原变量前缀与有限参数表的统一名字列；类型投影的名字重编码；定义域查询的实际名字列 |
| [ExceedsSyntax](ExceedsSyntax.lean) | 原子类型输入元组的实际重排传输；完整实际类型对原前缀的子类型见证；定义 3.9 的超过关系；超过关系的背景原公式 |
| [FlatPredecessor](FlatPredecessor.lean) | 最大序数以下的完整满足关系 |
| [FlatSatisfaction](FlatSatisfaction.lean) | 以有限前缀为坐标的平坦真值表；平坦真值方程与原满足关系一致；平坦程序的秩界和指令绝对性；平坦真值方程在后继秩层中的绝对性 |
| [FlatTypePredecessor](FlatTypePredecessor.lean) | 在实际极限秩层内运行原规范解码器；从原自然数码恢复平坦程序的有界公式；任意较低秩层中的原自然数公式码；任意外层中读取较低秩层的原完整类型查询 |
| [KappaCode](KappaCode.lean) | 前一秩层中 κ 型的完整原公式；任意内部元数的 κ 型读取程序 |
| [LowerSource](LowerSource.lean) | 任意较低秩层中完整类型的原公式 |
| [Minus](Minus.lean) | 类型向前一秩层限制的纯语法代码；向前一秩层限制的语义；完整类型的前驱算子；查询域对公式码替换的封闭性 |
| [MoveQuote](MoveQuote.lean) | 完整类型的变量名、常量名与赋值；原名字列对平坦元组的有界求值矩阵；用原名字列移动类型的实现元组；从实际元组自动恢复共同名字列 |
| [MoveRead](MoveRead.lean) | V(ν+ω) 中指定序数的完整类型；同一完整类型的指定点与有限参数真值；在 V(ν+ω) 中统一读取 V(ν+k) 的完整类型；用指定点的完整类型读取移动后的较低类型 |
| [PointwiseWitness](PointwiseWitness.lean) | 代表函数的逐点赋值；代表函数赋值的实际逐点求值；逐点满足的赋值无关性与逻辑方程；源内部函数族的对角与全定义域延拓 |
| [PredecessorCode](PredecessorCode.lean) | 原完整前驱类型的自动公式接口；从原变量列读取完整前驱类型的内部公式 |
| [ProgramReflect](ProgramReflect.lean) | 前驱定义域的实际内部公式；前驱定义域的完整类型查询；查询程序及原名字列的有限公式；原查询名字列的向上读取 |
| [Roles](Roles.lean) | 类型坐标的固定标签角色；任意内部有限组标签角色的实际编译；标签角色成为实际完整类型中的单个查询 |
| [SubtypeInsertion](SubtypeInsertion.lean) | 在高度坐标前插入新标签的实际子类型见证 |
| [SubtypeLift](SubtypeLift.lean) | 前驱算子的自然数矩阵；前驱类型与实际初等像交换；子类型查询的有界闭包性质；子类型闭包沿实际初等映射运输 |
| [SubtypeReboundImage](SubtypeReboundImage.lean) | 子类型查询的定义域参数更换；实际初等像中的完整类型查询域；子类型定义域更换的实际初等像 |
| [SubtypeReflect](SubtypeReflect.lean) | 固定子类型查询从传递证书层向上读取；原子类型查询返回传递源 |
| [SubtypeUp](SubtypeUp.lean) | 先于具体常量固定的内部查询程序；子类型的同一固定查询与完整实现；定义 3.6 的固定查询码；子类型查询的自动构造与定义 3.7 |
| [SubtypeWitness](SubtypeWitness.lean) | 原类型元组的有限排列；子类型句子的秩内语义；子类型的完整实现见证 |
