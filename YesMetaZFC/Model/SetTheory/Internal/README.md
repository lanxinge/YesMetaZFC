# Internal

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

## 支撑层导航

| 目录 | 职责 |
| --- | --- |
| [Source](../Source/README.md) | 模型内部程序、对象与解释 |
| [Relations](../Relations/README.md) | 原关系函数、共同层与秩 |
| [Embedding](../Embedding/README.md) | 实际嵌入图、初等性与读取 |
| [Reflection](../Reflection/README.md) | 有限反射、传递坍塌及 ZFC 证书 |
| [ReducedPower](../ReducedPower/README.md) | 代表码、商成员、Łoś 和复制 |
| [DirectedSystem](../DirectedSystem/README.md) | 有向系统、因子和直接极限 |
| [Types](../Types/README.md) | 内部类型、查询、实现与排列 |
| [Game](../Game/README.md)、[Demand](../Demand/README.md) | 博弈状态及深度调度的对象编码 |
| [Images](../Images/README.md)、[Truth](../Truth/README.md) | 成员满映射、策略图像与集合真值 |

## 基本内部接口

| 模块 | 数学内容 |
| --- | --- |
| [BinaryDecode](BinaryDecode.lean) | 弱传递见证中的二值解码 |
| [ClosureLetters](ClosureLetters.lean) | 带见证位置表的有限闭包尝试；从真实可数闭集构造全部任务的见证位置表；闭包尝试的实际有限序列树；枚举值与见证位置的实际配对字母 |
| [Collapse](Collapse.lean) | Mostowski 图的完整内部初等性 |
| [CollapseCountable](CollapseCountable.lean) | 可数初等图的塌缩像保持原定义域 |
| [CollectionCode](CollectionCode.lean) | 全内部公式的收集实例代码 |
| [Countable](Countable.lean) | 全部内部公式码的规范可数性见证 |
| [Extensionality](Extensionality.lean) | 内部等号与外延性的保持 |
| [FiniteRecordRelative](FiniteRecordRelative.lean) | 固定元数记录的原一阶公式；固定坐标块的量词；固定元数记录列的实际坐标函数；同一记录的坐标回读与唯一性 |
| [FiniteSetCode](FiniteSetCode.lean) | 中间坐标的实际集合公式 |
| [FiniteSource](FiniteSource.lean) | 内部公式程序的可组合构造；原 AST 编译的参数与量词语义；原 Project 公式的内部编译；原变量中一个内部有限区间的成员枚举 |
| [FiniteSpaceBounded](FiniteSpaceBounded.lean) | 已有完整有限列空间的有界识别 |
| [FiniteTailSource](FiniteTailSource.lean) | 极限秩层中原序数加法的绝对性；极限秩层中的有限尾长绝对性 |
| [FormulaRelation](FormulaRelation.lean) | 原公式定义的实际二元关系 |
| [FunctionCode](FunctionCode.lean) | 传递集合上的有界公式程序；源内部函数域及其公式代码 |
| [Hereditary](Hereditary.lean) | 内部隶属结构的解码与外延性；集合隶属结构中的统一司寇伦见证公式；完整内部初等结构的 Σ₁ 子结构实例；内部可数初等 H(χ) 子模型的原公式 |
| [Isomorphism](Isomorphism.lean) | 内部同构保持全部公式码的真值 |
| [LargestSet](LargestSet.lean) | 最大集合的实际内部指令；最大集合指令的完整语义 |
| [LowerSatisfaction](LowerSatisfaction.lean) | 对幂集的原公式相对化；任意较低秩层的原满足公式 |
| [MembershipSlice](MembershipSlice.lean) | 给定隶属模型切片的逐项解码 |
| [NaturalBasis](NaturalBasis.lean) | 特殊实数在传递成员结构中的实际解释 |
| [OrdinalFoldSource](OrdinalFoldSource.lean) | 典范序数对次序在传递子源中的解释；典范序数配对在极限秩层中的绝对性；序数折叠的读取与递归步在极限秩层中绝对；内部有限序列编码在极限秩层中的绝对性 |
| [Quotient](Quotient.lean) | 内部语法标签的有限序数码；地模型内的集合结构编码；集合关系的规范商及下降映射 |
| [RealTrace](RealTrace.lean) | 传递隶属模型的包含映射覆盖全部成员；测试壳的实际背景实数集 |
| [Registration](Registration.lean) | 条件与固定参数列的同枚举登记 |
| [RegularRankImage](RegularRankImage.lean) | 正则秩图的完整初等像 |
| [RelativizationCorrect](RelativizationCorrect.lean) | 全部内部程序的限制翻译；限制编译的实际语法构造；完整内部程序的统一限制编译；纯语法限制证书的完整正确性 |
| [SeparationHull](SeparationHull.lean) | 任意内部公式的分离实例代码；完整初等嵌入回拉内部公式的实际分离集；可数传递模型中的全内部代码分离 |
| [SeparationTransport](SeparationTransport.lean) | 初等映射精确搬运全内部公式的分离集 |
| [SmallHull](SmallHull.lean) | κ 小种子的实际 Σ₁ 隶属子结构 |
| [SmallSkolemSyntax](SmallSkolemSyntax.lean) | 内部公式的两个实参；不同变量域上的同一内部公式；完整初等嵌入作用于有限赋值；有限求值证书的有界语法 |
| [Support](Support.lean) | 每个内部有限程序都有内部有限坐标界；内部有限支撑上的真值一致性 |
| [SyntaxSource](SyntaxSource.lean) | 原有 Kuratowski 程序在传递子源中的语法绝对性 |
| [TarskiVaught](TarskiVaught.lean) | 从有限参数司寇伦闭性到完整内部见证闭性；内部 Tarski–Vaught 定理 |
| [TarskiVaughtSyntax](TarskiVaughtSyntax.lean) | 完整内部赋值上的 Tarski–Vaught 条件 |
| [Theory](Theory.lean) | 集合编码赋值及单变量更新；模型内部的有限公式指令码；内部满足关系的递归原公式；内部真值递归的存在、唯一性与原公式 |
| [TruthImage](TruthImage.lean) | 成员满嵌入不增加内部有限程序；成员满嵌入保持全部内部有限赋值的真值；完整赋值的有限支撑回拉与实参真值运输 |
| [TupleCode](TupleCode.lean) | 内部程序更换有序对编码；更换程序编码保持全部内部公式的真值；原程序到平坦程序的转换证书在极限秩层中绝对；内部变量列的递归打包规格 |
| [Uniformization](Uniformization.lean) | 全内部公式的统一函数图代码；正则遗传小结构中的内部收集及其回拉；源模型中的实际统一见证函数 |
| [UniformizationHull](UniformizationHull.lean) | 可数传递壳的全内部码分离、收集与统一化 |
| [UniformizationSource](UniformizationSource.lean) | 源中有界关系的实际分离；原有界关系在源模型内的统一化 |
| [UniversalClosure](UniversalClosure.lean) | 全称闭包的内部赋值规格；非标准内部程序的全称闭包及理论的正向保持 |
