# 扩展器与有限支撑超幂

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [BoundedGraph](BoundedGraph.lean) | 有界共同支撑关系就是原极限关系的逆像；有界代表关系的源内图与原极限投影 |
| [BoundedIdentity](BoundedIdentity.lean) | 原有界池中恒等代表的实际值 |
| [BoundedRaw](BoundedRaw.lean) | 共同有界代表池到未坍塌商的满呈示 |
| [BoundedRealization](BoundedRealization.lean) | 所属源的有界坍塌直接识别原始商的低层 |
| [BoundedTransport](BoundedTransport.lean) | 源内有界代表及其求值图的传输 |
| [BoundedValue](BoundedValue.lean) | 所属源的求值图辨认施加超幂的实际常值像 |
| [Branch](Branch.lean) | 共同纤维保持超幂后继的枝反射 |
| [CommonImage](CommonImage.lean) | 共同极限秩段中的原超幂像 |
| [Coordinates](Coordinates.lean) | 原嵌入对实际源分量的因子图；原求值与有限坐标过渡交换；全部有限支撑求值的装配与极限因子；每个支撑序数都有真实的坐标代表 |
| [CopyApplication](CopyApplication.lean) | 代表复制与有限坐标拉回交换；双映射复制的带支撑代表方程；双映射复制整个有限支撑超幂；同时施加两侧扩展器并自动复制 |
| [CopyBounded](CopyBounded.lean) | 复制图在临界点像以下等于所属嵌入 |
| [CopySeed](CopySeed.lean) | 双映射复制保持实际坐标类 |
| [CopySubsets](CopySubsets.lean) | 实际支撑迹沿所属源嵌入传输；复制图与所属嵌入在全部有限支撑幂子集上一致 |
| [CopySuccessor](CopySuccessor.lean) | 复制的序数限制在目标内还原为完整小域限制；可数源的完整超幂在包含源中的实际呈示；从有限幂子集的一致性恢复整个小传递集合上的映射；同一复制图在传递后继上的支撑保持 |
| [Countable](Countable.lean) | 可数源与可数支撑的实际超幂可数 |
| [CriticalPoint](CriticalPoint.lean) | 原内部短扩展器的实际临界点 |
| [DerivedLimit](DerivedLimit.lean) | 武丁派生扩展器的完整极限与原目标比较 |
| [EmbeddingCountable](EmbeddingCountable.lean) | 源中实际存在的完整初等嵌入尝试树；源内可数域上的完整初等嵌入回收 |
| [FunctionMap](FunctionMap.lean) | 两张图在 κ 值代表函数上相同 |
| [FunctionValue](FunctionValue.lean) | 原始商中任意有限组对象的共同支撑代表；未坍塌商中函数求值的源内代表 |
| [Length](Length.lean) | 坍塌后因子及原嵌入的交换三角；坍塌因子固定长度，超幂恢复原临界点 |
| [LevelTransfer](LevelTransfer.lean) | 把测度像的外部共同纤维回收到所属源；节点内部的共同纤维条件及实际源内见证；同一极限秩源中的短扩展器向所属模型提升；原短扩展器在初始秩模型中的所属判断 |
| [Limit](Limit.lean) | 武丁测度族的实际良基定向极限 |
| [LocalFormula](LocalFormula.lean) | 所属短扩展器与不可达性的外层公式 |
| [LocalRead](LocalRead.lean) | 所属模型内部测度族的实际相对解释 |
| [NormalSource](NormalSource.lean) | 正规性在子集一致的源之间传递 |
| [NormalSyntax](NormalSyntax.lean) | 扩展器正规性的坐标图 |
| [OmegaClosed](OmegaClosed.lean) | 可数支撑列属于所属源的严格秩段；有界可数闭所属模型实现背景中的全部可数测度约束；有界可数闭所属模型的跨模型施加良基性；指定跨源超幂与所属模型的共同强度秩段 |
| [Overview](Overview.lean) | 扩展器理论的公共入口 |
| [Product](Product.lean) | 从测度族构造扩展器算子；扩展器算子的布尔运算和坐标变换；扩展器保持有限坐标上的乘积 |
| [RankAgreement](RankAgreement.lean) | 内部正则秩段的超幂就是原超幂的严格秩段；同源同扩展器的实际超幂唯一；共同正则秩段上的超幂一致性 |
| [RankLift](RankLift.lean) | 原所属短扩展器公式在严格极限秩段中的保持；严格极限秩段中的短扩展器向上保持 |
| [RawAgreementRead](RawAgreementRead.lean) | 实际隶属源中的原关系支撑数据；实际隶属呈示中的共同图与有限幂一致性 |
| [RawAlphabet](RawAlphabet.lean) | 原生单步的完整输出；原生一步施加的字母满像与有限前缀 |
| [RawApplication](RawApplication.lean) | 原对象码极限中的函数应用等式 |
| [RawCoherence](RawCoherence.lean) | 严格秩段中的全内部分离与小定义域收集；相对秩段及初等回拉的完整源证书；读取超幂证书所需的有限闭性；原关系后继的有限读写闭性 |
| [RawColimit](RawColimit.lean) | 原对象码后继的未坍塌极限 |
| [RawConstant](RawConstant.lean) | 对象码极限中同支撑的原子方程；任意支撑的常值代表在原关系极限中一致 |
| [RawCopy](RawCopy.lean) | 两张原关系图之间的实际测度对应；两端实际原关系分量之间的完整初等复制 |
| [RawCopyClass](RawCopyClass.lean) | 原关系共同切片上的实际下一分量与完整 Łoś；原关系中的有限幂对象；原关系有限幂的实际子集一致性；对象码分量的规范定义 |
| [RawCopyEvaluation](RawCopyEvaluation.lean) | 有界池求值沿原关系复制的保持 |
| [RawCopyMaps](RawCopyMaps.lean) | 原关系复制在有限幂子集上的交换条件 |
| [RawCopyPull](RawCopyPull.lean) | 原所属图上有限支撑的实际像；原关系支撑投影的实际复制；实际重排下原代表复制与投影交换 |
| [RawCopySyntax](RawCopySyntax.lean) | 原关系复制的统一节点公式 |
| [RawCountable](RawCountable.lean) | 原关系超幂代表的有限对象码；可数原关系模型的实际扩展器极限仍可数 |
| [RawEvaluation](RawEvaluation.lean) | 对象码极限中新成员的完整有界覆盖；原函数在对象码极限中的实际求值；原池节点在对象码极限中的求值公式 |
| [RawEvaluationRead](RawEvaluationRead.lean) | 工作模型中原池求值的实际代表 |
| [RawExactHistory](RawExactHistory.lean) | 所属模型中的最大强度证书；原关系后继中的最大子集覆盖；较高共同层保持原子集的全局实现与缺失 |
| [RawGraphSyntax](RawGraphSyntax.lean) | 对象码定义域上的原扩展器重排；原对象码投影的恒等与复合律；对象码分量间的实际统一过渡；原关系全部分量的统一过渡图与标签集合 |
| [RawMembershipSystem](RawMembershipSystem.lean) | 原关系坐标图与实际隶属源的同一投影；给定原关系系统在真实隶属源上的完整读取；实际隶属商系统的原关系实例 |
| [RawOwnedCopy](RawOwnedCopy.lean) | 有界节点在指定实际超幂中的求值；有界节点中的常值代表；有界超幂的实际像在所属源中计算；有界超幂池的精确有界编码 |
| [RawPowerStep](RawPowerStep.lean) | 实际扩展器分量的幂集计数；实际扩展器直接极限的幂集计数保持；同一次原生施加保持幂集计数不变量 |
| [RawPresent](RawPresent.lean) | 原共同支撑约束的函数复合形式；实际支撑边的原函数解释；原模型有限支撑的反向读取；原有界池约束与对象码极限关系 |
| [RawProjection](RawProjection.lean) | 共同低层内实际有限支撑的原关系过渡 |
| [RawQualityCopy](RawQualityCopy.lean) | 原所属模型中的 nice 扩展器在工作源中的实际像 |
| [RawRank](RawRank.lean) | 全部原关系支撑分量的规范结构码；同一原关系源的全部有限支撑与初等定向极限；全部原关系支撑的实际初等极限；原关系定向极限的完整有界代表覆盖 |
| [RawRankSource](RawRankSource.lean) | 短扩展器、不可达支撑与最大强度的单一有界公式；原一步证书内的共同秩段与有界池；原共同秩段构造的有限全称规则；原一步证书生成两侧共同秩段及递归闭包 |
| [RawSetCopy](RawSetCopy.lean) | 原关系商类复制保持实际系统箭头；两个原关系有限支撑极限之间的完整复制；工作模型中原关系坐标的实际支撑值；原有界池的完整实现与复制交换 |
| [RawStrength](RawStrength.lean) | 原最大强度证书与支撑以下的双向子集读取 |
| [ReflectHull](ReflectHull.lean) | 有限反射层的实际可数壳 |
| [Represent](Represent.lean) | 任意有限种子的源函数求值都进入现有极限 |
| [SeedCollapse](SeedCollapse.lean) | 源内坐标代表与坐标原子；扩展器支撑在同一商极限中的坐标像；正规性使坐标像对前驱封闭；原始关系超幂中的完整支撑初段 |
| [SetCode](SetCode.lean) | 用有限 κ 幂的子集编码 κ 值代表；两段有限坐标的实际分块投影；集合值代表的共同编码 |
| [SetCopy](SetCopy.lean) | 给定集合复制因子的支撑及全部子集交换；给定原商极限到工作集合像的复制因子；沿大模型超幂复制到 j(A) |
| [SetInclusion](SetInclusion.lean) | 有限转置矩阵的超幂值；拥有集合的超幂像中的完整内部真值；拥有集合之像中的完整分量嵌入；小源超幂到拥有集合之像的完整初等嵌入 |
| [SkolemSource](SkolemSource.lean) | 实际源中的有限程序与有限赋值空间；源内实际存在的有限真值表；有限代表列的源内转置矩阵；Skolem 见证的源内有限证书 |
| [SkolemStep](SkolemStep.lean) | 小壳闭包在严格相对秩段中的保持；小 Skolem 壳的源内塌缩及跨源隶属；指定秩层种子的小壳调整 |
| [SourceJointFiber](SourceJointFiber.lean) | 可数约束层的有界读取；相对测度的源内共同约束层；所属模型的共同纤维实现施加源中的全部可数约束 |
| [SourceLimit](SourceLimit.lean) | 源内下降代表列的实际测度约束族；共同纤维把下降代表列变成实际下降值列；超幂外部下降链的源内回收；所属模型内部短扩展器的实际施加良基性 |
| [SourceNode](SourceNode.lean) | 标签关系下降链的统一源内代表界；内部所属扩展器保持实际后继的枝反射；内部所属扩展器的完整实际后继节点 |
| [SourceSubsets](SourceSubsets.lean) | 所属模型自身超幂的有界子集回收 |
| [SourceSuccessors](SourceSuccessors.lean) | 同一内部扩展器的两侧后继及向原所属模型的编码搬运 |
| [SourceTrace](SourceTrace.lean) | 源拥有扩展器时的支撑迹 |
| [Strength](Strength.lean) | 在既有分量上扩张谓词；同一个有限支撑极限的完整谓词初等性；不可达支撑长度处的真实强度上界；指定秩层的覆盖与原谓词一致性恢复 |
| [StrengthAgreement](StrengthAgreement.lean) | 从序数子集覆盖得到支撑以下的有限幂一致性 |
| [StrengthRank](StrengthRank.lean) | 最大强度的实际有界证书及外层回拉；所属源的最大强度在严格秩截断中保持 |
| [SuccessorApplication](SuccessorApplication.lean) | 有界集合代表在固定支撑上的迹一致；同一扩展器的两次施加保持支撑以下的子集一致性；后继一致性的自动构造入口 |
| [SystemRead](SystemRead.lean) | 从传递工作源读取原超幂分量；原有限支撑超幂系统的一阶证书；有限支撑代表与过渡方程的绝对性；从传递工作源读取整个指定超幂系统 |
| [Trace](Trace.lean) | 有限支撑代表的函数空间与拉回方程；有界代表与共同支撑关系的有界原公式；背景编码与原模型自然数分离的源；有限支撑系统的实际源数据 |
| [TreeBranch](TreeBranch.lean) | 相对于源模型的有限支撑测度族；全部有限支撑源分量的统一模型图；全系统过渡映射的统一图公式；有限幂一致性搬运小关系及其传递塌缩 |
| [Truncation](Truncation.lean) | 派生有限支撑测度的正规性；扩展器的标准坐标与临界点；有限列表示中的前缀投影与末项唯一性；有界投影的实际图条件 |
| [TupleValue](TupleValue.lean) | 有限坐标列的实际坍塌值 |
| [UltraCertificate](UltraCertificate.lean) | 常值像以下的处处有界代表；任意超幂下降链的统一源内值域界；从原代数证书恢复完整超幂边 |
| [UltraSupport](UltraSupport.lean) | 支撑端点由实际临界点像界住；指定实际超幂的支撑界 |
| [Ultrapower](Ultrapower.lean) | 全分量图的代表读取及恒等、复合律；全部源分量的带标号并及其实际过渡关系；全部有限支撑分量及映射的集合装配；有限支撑测度族的完整定向系统 |
| [Value](Value.lean) | 关系实现中的实际代表与完整公式 |
| [ValueApply](ValueApply.lean) | 同一实际超幂中的求值等式 j(f)(a)=[a,f] |
| [ValueBound](ValueBound.lean) | 同一代表的有界真值在两次施加之间一致；后继中的有限幂子集具有处处有界的源内代表 |
| [WellFounded](WellFounded.lean) | 极限边的共同有限支撑约束；极限下降链及其点态约束的原公式；共同纤维证明整个有限支撑极限良基 |
