# YesMetaZFC

一个轻量 Lean 4 项目。当前已完成支撑符号消去、完整原公理模型验证及纯 Rosser 独立性：
`PureRosser.independent` 仅假定裸 ZFC 一致，推出当前纯句子与其否定均不可推导。

## 环境与构建

工具链固定为 Lean **4.33.1**（见 `lean-toolchain`），仅依赖工具链自带的 Lean / Std。
安装对应工具链后，在项目根目录运行：

```bash
lake build
bash scripts/check-all.sh
```

第二条命令需要 Bash 4 或以上，覆盖全部 Lean 源模块（包括默认入口未导入的模块）
和 `prove_auto_sweep` 可执行工具；任何 warning 都会使检查失败。
需要从头验证时，先运行 `lake clean`。

工程清理范围、性能测量及后续热点见 [ENGINEERING.md](ENGINEERING.md)。

扫描器只静态导入公共 tactic 入口，完整证明库在执行扫描时从 `.olean` 加载；
不要改回静态导入根 `YesMetaZFC`，否则大型元数学编码的原生初始化可能使工具在
处理 `--help` 之前就发生栈溢出。实际扫描使用
`lake env .lake/build/bin/prove_auto_sweep ...`，以保留项目模块搜索路径。

## 4.33.1 迁移说明

证明已适配新版透明度规则：类型别名在必要处标记 `@[implicit_reducible]`，
需要按定义相等转换的简化证明显式使用 `simpa ... using!`，自由闭合性则显式消费
有序对约定的 `code_freeClosed` 合同。

AVATAR 可靠性直接使用当前内在回放模块。已删除无声明、无调用方的
`Automation.AvatarSoundness` 与 `Automation.AvatarRegistrySoundness` 兼容入口。
旧 raw 字句 / bound-stack 接口已不受公共一阶语法支持；
调用方应使用 `DAGCertificate.IntrinsicReplay` 的节点与根节点可靠性定理，以及
`HostRules.Semantics.avatar_semanticallyEntailsAt`。相关 checker 与语义合同仍由公共
DAG 模块维护。

`Resolution.CertificateSlice.compactCore?` 因 Lean 4.33.1 的新 do elaborator 内部错误，
仅在该函数中启用工具链提供的原 do elaborator，切片算法及 checker 保持原实现。

六个签名 / 结构声明保留字段所需的独立宇宙参数，仅对相应声明局部豁免
`linter.checkUnivs`：该检查仅查看结构类型中的 `max`，不分析字段的独立宇宙用途。
其他 warning 继续由全库脚本作为构建失败处理。

## 形式化成果

[Lean 形式化奖杯表](TROPHIES.md)记录当前可核对的声明及旧架构记录。
当前已在 `intrinsic_zfc_theory`（ZFC 公理像与原有证明支撑理论的并）上
完成具体证明表示、当前 quotation 的固定点及 Rosser 不完备实例。
`ReducedRosser.independent` 仅假定该支撑理论一致，即推出具体句子及其否定均不可证。

当前公理层已闭合为**与原支撑理论推导等价的公理基表示**：原 ZFC 基础公理像，
加上从原支撑公理中抽出的 119 条闭句。`ReducedAxiomPacket.presentation` 给出这套
公理基的固定二元 Delta0 对象公式、实际自然数包检查器及正负普通推导。
`ReducedAxioms.derives_iff` 证明任意自由上下文和局部假设下，两套公理的可推导命题相同。
整棵证明树现已具备带上下文、结论标注的自然数格式，六类核规则的实际检查及
可靠性、完备性。`ReducedProofTree.derives_iff` 已将该检查器连接到原支撑理论。
`ReducedProofPresentation.nodeTest` 已具体构造固定一元 Delta0 节点公式及全自然数正负
普通推导，覆盖 27 类逻辑公理、理论公理、MP、全称概括、自由加强和同时自由代入。
`ObjectProofNode.checked_sound` 连接原局部核检查，`checked_encode` 接受全部实际证书编码；
`ObjectProofRow` 精确实现递归行的调用分派，`ObjectProofNode.ofNodeTest` 完成整树和根 quotation 传输。
最终入口 `ReducedProofPresentation.presentation` 的类型为
`Delta1ProofPresentation intrinsic_zfc_theory intrinsic_zfc_theory`，不再有待填的局部表示参数。
`ReducedRosser.presentation` 将该图接入有限 Rosser 比较；`ReducedRosser.sentence`
是当前 quotation 下的实际对角句，`fixed_point` 给出对象理论中的固定点等价，
`independent` 给出仅依赖一致性的双向不可证结论。该实例属于支撑理论；支撑消去与模型对应也已完成，
裸 ZFC 上的最终实例见 `PureRosser.independent`。

对角化的关键是 `Automation.ObjectLeastWitness.unique`：在对象公式中选择最小合法
输出，再用标准正确输出处的码域切分与有限负实例，排除全部错误对象见证。
`ObjectNumeralSyntax` 编码实际 numeral 项，`ObjectDiagonal` 连接自由代入并证明
自代入关系的存在性和唯一性。`ObjectDiagonal.fixedPoint_spec` 对任意固定一元对象
模板构造具体句子及普通 Hilbert 固定点推导，不假定原始计算图对任意对象预先具有函数性。

目前已有完整支撑理论的显式公理证书、覆盖普通 Hilbert 核全部规则的结构证书，
以及结构证书结论检查的可靠性和完备性。具体入口为
`ProofT.ZFC.intrinsic_zfc_derives_iff_certificate`。公理证书中的分离 schema
保留其参数，证书不携带理论成员证明。

自然数编解码已完成：`ProofT.ZFC.intrinsic_zfc_nat_decode` 实际解析自然数，
覆盖全部六条推导规则、27 类逻辑公理及完整支撑公理呈现；非法输入返回 `none`。
`intrinsic_zfc_nat_check_sound` 证明接受结果导出原理论的普通 `Derives`。
逆向入口 `intrinsic_zfc_nat_encode` 已实现，`intrinsic_zfc_nat_decode_encode`
证明编码后恢复整个原证书；`intrinsic_zfc_derives_iff_nat_certificate` 证明普通可证性
等价于存在一个可接受的自然数证明码。格式与验证入口见
[自然数证书编解码](NAT_DECODING.md)。

quotation 已针对当前类型安全 Hilbert 核迁移：`ProofT.IntrinsicQuotation.quote`
直接保留十一种公式构造子，并证明反解往返、单射和不同公式码在对象理论内可证明不等。
公共 `Delta1ProofPresentation` 与抽象 Rosser 接口已采用新码。旧
`QuineEncoding.quote` 先做 Hilbert 化，会合并自然数检查器需要区分的结论；
`ZFC.SchemaQuotationAudit` 已给出分离和收集公理证书上的一般反例。

`ZFC.SchemaConclusion` 已完成分离、收集、替换三类**已解析实例的结论比较**正负表示。
原始输入侧新增 `ZFC.SchemaEnvelope` 与 `ZFC.SchemaTerm`：前者统一表示两类模式的
标签、字段数量和参数叶子，后者直接表示实际正文项解码器的作用域检查。两层都有
接受时的对象证明及拒绝时的对象否定，覆盖任意原始有限树，未假定输入已解析。
`ZFC.SchemaBody` 现已证明整个正文解码的可靠性、完备性、精确往返及拒绝判准。
`ZFC.SchemaRename` 用有限自然数表重命名原始树，证明任意输入的成功/失败保持、
量词下的表提升、任意候选输出的规格，以及与类型安全 AST、新 quotation 的交换律。
`SchemaRenameInstances` 连接分离、收集、替换实际使用的六个正文位置，参数数目无固定上限。
`SchemaObjectGraph.Body.condition` 与 `Rename.condition` 现已给出固定的统一对象公式，
并在当前扩展集合论语言中证明 `Delta0` 分类。`SchemaBodyDerives` 和 `SchemaRenameDerives`
直接从实际检查器的成功、失败或错误候选输出推出普通 `Derives`，覆盖任意原始树、
任意参数和有限表，并同时提供数值码及紧凑树码出口。六个实际模式位置已接入。
`SchemaTemplate` 已将六处重命名接入分离、收集、替换的固定核心模板，并证明装配结果
逐节点等于实际 `*Core` 构造、接受集恰好等于源作用域正文识别。`SchemaTemplateDerives`
提供一个五槽位、带对象标签的固定 Delta0 公式，以及任意数值槽位或紧凑树码上的正负
普通推导；未知模板标签和任意错误候选输出均可否定。模板只负责装配已给出的槽位。
`SchemaClosure` 已完成任意参数层数的全称闭合图及正负推导，装配结果精确恢复
实际三类模式闭句。`NatPacketLink` 已完成实际版本一包到对象树码的统一 Delta0
连接和正负推导，覆盖非法包与成功包的错误候选树；`NatPacketCanonical` 证明
所有成功解码的输入均精确重编码为原自然数。正文包到三类模式闭句的宿主流程已接通。
`SchemaTable` 现已用固定八条规则生成六个实际重命名位置的任意参数表，并给出
正负推导。`SchemaJoin` 将三张表、三个重命名正文及核心共七个中间码在对象层
有界存在量化，公开接口只保留种类、参数数目、原始正文码、候选闭句码四个槽位。
其统一 Delta0 图有无额外表示合同的正负 `Derives`，并连接三类实际 Project 模式闭句；
负向覆盖任意自然数结论码及非树中间码。该分类使用既有扩展语言（包括自然数幂项）。
`KernelQuotation.project_formula_code` 现已证明原始转换逐构造子等于当前类型安全内核编码，
`SchemaKernelJoin` 将 Project 闭句中间码在最终 quotation 码的后继中量化，三类模式均有
正负表示。`SchemaPacket.template` 则是实际 ZFC 分离、收集模式包到内核 quotation 的
固定二元 Delta0 公式：原树、参数数目和正文也在对象层量化，公开输入只有包码和结论码。
`SchemaPacket.run_eq_actual` 对任意自然数证明流程精确等于原公理证书解码器的模式分支；
`actual_positive_number`、`actual_negative` 给出任意自然数输入、输出上的正负普通推导，
并有直接使用紧凑 quotation 的实际分离、收集接口。非法包、非树中间码、非法外壳和正文、
错误结论均被同一个公式排除，不要求一致性或外加表示合同。
替换未被增添到现有采用分离和收集的 ZFC 公理呈现中。

`BaseAxiomPacket.template` 已将八条固定公理和上述两个模式合并为一个固定二元
Delta0 公式。其独立规格直接使用原基础公理解码器，正负推导覆盖任意包自然数和
任意候选数码。`BaseAxiomPacket.presentation` 是具体的
`Delta1AxiomPresentation intrinsic_zfc_theory intrinsic_zfc_axiom_theory`：
检查器接受恰好对应原 ZFC 公理像中的闭句，且接受和拒绝均能在支撑理论内表示。
`AxiomCanonical` 证明所有成功基础证书重新编码后恢复原始树与包，无额外规范性前提。

参数化支撑公理现已完成证书识别层：`SyntaxParameters` 精确恢复原 indexed
上下文与项参数，成功解码后重编码恢复输入；`ObjectTermSyntax` 用固定 83 条规则
表示当前内核全部 76 个函数符号的项及参数外壳，并有统一 Delta0 公式和正负普通推导。
`SupportParameters.actual_eq_decode` 对任意原始输入核对全部 11 类实际公理分支；
`ZFC.SupportParameter` 提供原支撑理论中的数值树码与紧凑树码出口。上下文长度和
项深度无固定上限。这里的对象公式表示证书合法性。

参数代入与公理装配的计算层也已完成：`SyntaxSubstitution` 处理完整内核项、绑定处的
变量提升和任意自由上下文的全称闭合；`SupportAssembly` 为全部 11 类公理保留各自的
固定模板，`SupportTemplate.instantiate_eq` 证明实际项代入精确恢复原分离公理。
`SupportRealization.run_eq_actual` 对所有原始输入证明装配输出与原证书的实际结论相同，
并连接当前 `IntrinsicQuotation.quote` 及内层参数外壳的版本一自然数包。
`run_sound` 将任意成功结果连接到对应原族理论中的普通 Hilbert 推导。
这层保留原参数证书的计算规格。后续采用已证明等价的有限公理基，不要求继续表示
原参数证书的逐字装配过程及旧外层 union 路径。

`SupportAssembly.sentence_of_closedTemplate` 对全部 11 类任意项参数证明：打开该族固定
全称闭句、执行项代入，再关闭实际自由上下文，即可导出原公理实例。
`SupportAxiomBasis` 沿原理论全部组合结构证明有限生成性；`FiniteAxiomBasis.compact`
按精确语法去重，不改变生成的理论。没有添加公理，也没有改变原理论的普通推导能力。
`ReducedAxioms.presentation` 合并基础公理对象图与这张有限表；`ReducedAxiomPacket`
进一步将独立的实际包解码器接入同一公式。新公理包保留基础标签 0–9，标签 10 只表示
有限支撑基索引，不是新的 ZFC 模式。原完整证明包与新公理包分别命名。

此处得到的类型是 `Delta1AxiomPresentation intrinsic_zfc_theory ReducedAxioms.theory`，
明确表示等价公理基的成员关系。完整证明树的对象表示现已接入，
`ReducedAxioms.liftProofPresentation` 已在 `ReducedProofPresentation.presentation` 中将其
传回原 `intrinsic_zfc_theory`，保留同一检查器、对象公式及正负推导。
现有 `intrinsic_zfc_graph` 仍使用旧 Hilbert quotation，新的具体实例不依赖该旧图。
新实例只复用该模块中与 quotation 无关的后继链码域核心；完整证明图来自
`ReducedProofPresentation.presentation`，不依赖旧图的证明表示合同。

裸 ZFC 消去层现已完成当前内核的通用关系式翻译及其语义正确性。
`Automation.RelationalTranslation.formula_correct` 覆盖全部十一种公式构造子，
`term_correct`、`arguments_correct` 精确表示实际对象值。`expansion_realizes`
从函数图对所有参数的存在唯一性构造源模型，`models_iff` 及 `derives_sound`
连接翻译公理和普通源 Hilbert 推导的目标模型真值；这里尚未给出目标理论的句法推导传输。

`ProofT.ZFC.PureModel.theory` 明确使用原 ZFC 公理在纯签名 `ℒ` 中的像。
`PureFunctionDefinitions.graph` 已为原支撑签名的空集、无序对、单集、并集、幂集和
后继提供实际纯隶属定义；`functional` 从任意裸 ZFC 模型的公理证明这六种函数的
任意参数存在唯一性。`PureRelationFunctions.graph` 进一步给出原符号索引下的 Kuratowski
有序对、左右投影和函数求值。`PureMappingDefinitions.graph` 又加入笛卡尔积和映射收集，
`PureRelationCoordinates` 和 `PureMappingOperations` 再加入定义域、值域、恒等映射和
函数限制，上述基础模块覆盖十六个函数的纯定义；纯关系定义还包括 `isMapping`。`PureRelationDefinitions`
提供子集、有序对、关系和函数谓词；`PureKuratowski` 证明编码存在、唯一和坐标单射。
投影及求值使用 `Automation.TotalizedGraph` 规范总化：合法输入保留唯一原输出，
没有合法输出时取空集。`left_spec`、`right_spec`、`application_spec` 已证明合法输入上
匹配原数学规格；原完整公理现由 `PureSupportModels` 统一验证，不能把缺省分支当成原理论定理。

`SetTheory.Definitional.Project.FirstOrderSemantics.formula_correct` 对任意自由闭合正文
证明 Project 与当前类型化纯语言的语义对应。`PureModel.project_models` 已把任意裸
ZFC 核模型接入既有集合论模型库，不要求模型标准、传递或外部良基。
`PureKuratowskiProject.interpretation` 已具体填满该模型上的有序对编码解释，
`PureMappingDefinitions.exists_output` 因而直接复用既有替换、分离定理构造笛卡尔积和
映射收集，`functional` 证明两张图对任意模型对象参数存在唯一输出。
`mapping_spec` 在给定精确定义域、值域时对应原映射谓词；
`PureMappingSpecifications.cartesian_spec` 和 `mappingCollection_spec` 进一步证明
二重幂集及笛卡尔积幂集中的母集限制由纯定义自动满足。这些是逐值数学规格对应，
全部原支撑句子的统一验证见 `PureSupportModels.support_models`。

`PureRelationCoordinates.functional` 为任意集合收集其中合法有序对的两种坐标，并证明
存在唯一性。`PureCoordinateSpecifications.coordinate_spec` 在关系输入上保留原公理的
投影筛选及双重并集限制；`mapping_definition` 以实际纯图计算定义域和值域，消去了
映射定义中此前外加的坐标规格前提，`application_spec` 也直接消费定义域图的成员证据。
`PureMappingOperations.functional` 完成恒等映射与函数限制的任意参数存在唯一性；
`identity_spec`、`restriction_correct` 对应原成员规格，`restriction_mapping` 通过已有
Project 语义定理证明限制后的函数仍映入原目标集。坐标和限制函数在任意输入上的
这些具体取值属于所选扩张；原支撑公理仍按各自的 guard 验证。

`Automation.SemanticTransfer` 已区分并证明两条连接：目标模型可扩张给出一致性传输，
源模型可约化且指定句子真值一致则经强完备性给出目标推导向源推导的反射。
`PureRosserTransfer.Contract` 将这两侧连接到当前 `ReducedRosser.sentence`，其
`independent` 的最终一致性前提精确为 `PureModel.theory`。现在 `PureRosser.sentence` 已固定
实际纯目标句子，`PureRosserSchedule` 已提供两套公平调度；任意原模型的指定句子真值
对应仍须证明，因此条件独立性接口还不是无条件的裸 ZFC Rosser 终局。

三轮计划的第一轮已新增 9 个函数、20 个关系，共 29 个符号。函数包括二元并、对称差、
关系逆、关系复合、隶属关系、像集、归纳核、ω 与有序对反转；`PureRelationSetOperations`
和 `PureOmegaAndReverse` 给出实际纯图及任意输入的存在唯一性。`PureRoundOneSpecifications`
保留原母集、投影、反转与归纳核规格，`omega_definition_correct` 直接验证原语言的 ω 定义。
二十个关系直接沿原定义正文翻译；`PureRoundOneRelations.graph_equation`、`definition_correct`
证明同一实际扩张中的逐参数等价，`dependencies_covered` 排除未完成符号的临时分支。

第二轮首批已完成 `minimum`、`maximum` 两个函数，以及自然数、无限性、可数性、
不可数性、可数无限性和 `omegaPairLess` 六个关系。`PureOrderExtrema` 证明极值图的
任意输入存在唯一性；`PureStageTwoSemantics` 将原 guard 下的三个极值定义实例接到
同一具体扩张。`PureNaturalRelations` 保证新增关系的原正文等价和依赖覆盖。

第二轮此前再完成七个函数：有限子集收集、幂集二值编码图、指数序、有限序列空间、
非空有限序列空间、递归序列族及其并集。`Project.FromFirstOrder` 与 `PureSeparation`
把任意当前纯公式接到原 ZF 分离模式，`PureSequenceStage` 在该阶段同一扩张中保留七项
原规格及已有关系定义。递归序列族的并集已按原定义构造，其全域递归性质仍待单独证明。

当前 119 条有限支撑公理实际使用 64 个函数、46 个关系，已完成全部纯定义：**64 个函数、
46 个关系，共 110 / 110，剩余 0 个**。第三轮 **30 / 30**，第二轮 **29 / 29**。
完整清单、定义修正和证明入口见 [ELIMINATION.md](ELIMINATION.md)。

第二轮末尾补齐 `naturalOrderType`、`naturalSubsetType`、`finiteSequenceConcatenation` 和
`finiteSequenceFlatten`。序型由内部良序坍缩构造，原极值条件保证其有限性；拼接用内部
加法分段和替换收集函数图；展平由携带族参数的内部递归产生累积列，再以公式归纳和
递推唯一性确定有限末值。四项均有纯图、任意参数存在唯一性，以及原 guard 下的精确规格。

`PureRoundTwoStage` 是第二轮统一扩张，四项完整原定义实例均在该扩张中成立。
`PureRoundTwoSpecifications` 保持此前算术、收集、序列、集合构造与关系正文。
证明不假定模型内部自然数外部标准；原递归序列族并集的全域性仍是单独待办。
最终扩张现已实现全部支撑理论；Rosser 句子在任意原模型约化前后的真值对应仍是后续义务。

第三轮首批完成三个递归语法识别关系、非逻辑符号全集与结构谓词。
`PureLeastFixedPoint` 用模型内部纯分离和单调性构造最小不动点；
`PureSyntaxOperator` 与 `PureSyntaxFixedPoint` 用带标签的有界集合图同时解决三个递归关系。
首批统一扩张为 `PureStructureStage`，五项原定义均已满足，第二轮四个末尾定义继续成立；
`PureRoundThreeSpecifications` 保持此前各类规格。该构造不假定模型 ω 的外部标准性。

第三轮第二批进一步完成三个相关语法识别关系、相关项集、相关公式集与 `modusPonens`。
`PureRelatedSyntaxOperator` 和 `PureRelatedSyntaxFixedPoint` 为每个符号集构造内部不动点；
`PureRelatedSyntaxStage.condition_satisfaction` 核验原递归调用保持该参数。
`PureRelatedSyntaxSets` 从模型内部 ω 分离出两类代码集合，保留原存在深度量词。
第二批统一扩张为 `PureRelatedStage`，该批六项原定义及此前实际图均已核验，
并提供既有规格的传输接口。该批之后的逻辑公理集合、语义值、语法变换与公理识别已由下面两轮完成。

最后两轮收尾按依赖分成 **9 + 10**。第一轮已完成七个命题公理集合、量词分配公理集合和
等式自反公理集合。`PureStructuralCodeBounds` 给出实际结构码的内部 ω 界，
`PureLogicalSchemaSets` 用纯分离证明九个集合存在唯一及精确成员规格。
第一轮统一扩张为 `PureLogicalSchemaStage`，并满足七项命题公理模式的整个源闭句。

第一轮同时修正公理模式及生成步骤中误用的全称量词，改为存在见证；真正的全称闭包规则
保持不变。源句与 quotation 按修正后的定义重建。

第二轮已完成最后 **5 个函数、5 个关系**。`PureTransformStage` 实现语法变换与自由变量出现，
`PureAllSchemaStage` 补齐三种模式并验证命题、量词、等式三族完整源闭句；
`PureLogicalStage` 完成基集、逻辑公理闭包与公理码识别；`PureValueStage` 通过内部最小不动点
和四个外层参数保持，完成项与项列的原互递归求值关系。

最新统一扩张为 `PureCompletedStage`，全部 110 个符号的实际纯图已齐备，原求值定义、
全部模式与逻辑公理码闭句均在该模型中核验。全部 119 条支撑公理已由 `PureSupportModels.support_models` 统一验证，
原 ZFC 公理像及整个原理论由 `PureZFCModels.models` 验证，其实际纯翻译由 `translated_models` 验证。
模型扩张 `expands` 和任意原模型的 `reduction` 均已完成；`PureRosser.agreement` 已提供指定 Rosser 句子的真值对应证明。

统一验证修正反转函数的非法输入取值和复合函数的两个参数接线，保留原公理及 guard。
验证索引和剩余义务见 [UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md)，运行时恢复见 [RESTORE.md](RESTORE.md)。

当前纯 Rosser 配置入口为 `PureRosser`，已进入默认完整构建：

- `sentence` 与 `comparison` 固定为当前完整证明树 Rosser 句子及比较式的最终纯隶属翻译。
- `translate_derives` 由已验证的模型扩张和强完备性把任意源闭句推导传到裸 ZFC；
  `fixed_point` 因而是裸 ZFC 中 `sentence ↔ ¬ comparison` 的实际 Hilbert 推导。
- `PureRosserSchedule.source`、`target` 使用 `Automation.SyntaxNatCoding` 的单射语法编码
  及公平性证明，不再要求调用者传入调度。
- `agreement_iff_comparison` 将任意原模型上的句子真值对应严格缩减为比较式真值对应。
  `PureRosserComplete` 中的 `agreement` 填满此条件，`independent` 只要求裸 ZFC 一致。

这里的比较式使用源证明树及源 quotation，不是以纯语言自身 quotation 重新对角化的产物。
当前版本已按用户授权切换到内部自然数证明图，源固定点和对应的 quotation 随之重建；
源签名、公理和 quotation 编码规则保持不变。
配置阶段 `lake --wfail build` 通过 776 个任务，零错误、零警告。

`Agreement` 推进后，`PureSourceNumerals` 已证明任意原模型与其规范重扩张的空集、
后继、全部标准 numeral 和 quotation 取值对应，以及全部标准证明码实例的真值对应。
`RosserDomainBoundary.domain_agrees` 进一步证明后继码域本身的真值对应。

此前的码域边界已正式证明：模型内部的 ω 满足后继码域条件，
但 ω 不属于 ω，故该码域并不包含于自然数集合。原配数定义在非自然数首参数上
因 guard 为假而自动成立；未包装的完整证明图只把编码后的根节点限制在 ω，未直接限制输入证明码。
这些事实表明不能仅用标准码对应或码域条件完成 `Agreement`，尚未构成它的反模型。

`Automation.NaturalProofPresentation` 的自然数码包装已由
`ReducedNaturalProofPresentation.presentation` 接入 `ReducedRosser.presentation`，
保留原检查器、正负表示及完备性。源固定点、原理论独立性和纯固定点均已重新构建。

`PureSourceInfinity.omega_agrees` 已证明任意原模型与其规范重扩张的内部 ω 相同。
`member_natural` 与 `RosserDomainBoundary.natural_in_domain` 分别保证初始段仍在 ω 内、
内部自然数满足旧码域。`PureNaturalRosserAgreement.comparison_naturals` 因此给出精确语义：

```text
∃ p ∈ ω, Proof(p, quote(R)) ∧ ∀ q ∈ p, ¬ Proof(q, quote(¬R))
```

这里的 `Proof` 为原完整对象证明图，证明码量词遍历内部 ω，包括非标准自然数。
`PureSourceLocalTests.proof_agreement` 已对任意固定结论证明 `ProofAgreement`；
`agreement_of_natural_proofs` 消费当前句子及其否定的两个实例，得到 `PureRosser.agreement`。

`NaturalProofPresentation.comparison_delta0` 已利用现有自然数 guard 证明比较式的
**支撑语言 Δ₀** 分类。`ReducedRosser.delta0Sentence` 定义为当前比较式的否定，
`fixed_point` 给出它与原句子的普通推导等价；`delta0Sentence_delta0` 和
`delta0Sentence_independent` 分别证明其分类及仅假定原理论一致性的双侧不可证性。
当前源句子、公理和 quotation 没有再次迁移。

`PureSourceBounds` 已证明任意原模型的幂集值以及实际轨迹界 `P(ω)` 与规范重扩张一致。
`PureNaturalRosserAgreement.proof_trace` 展开当前完整图的实际轨迹语义；
`proof_agreement_of_rows` 现在只要求候选轨迹内局部行真值对应；根编码前提已由
`root_agrees` 自动提供。支撑语言 Δ₀ 使用 ω、幂集及编码函数，不代表纯隶属翻译已为 Δ₀，
也不代表一阶算术中的 Δ₀；`Agreement` 由下述实际局部检查的对应单独证明。

纯语言层级核验已纠正一个目标：当前 `ℒ` 只有 ∈，没有常元或函数。
`Automation.FunctionFreeDelta0.closed_decided` 证明这种语言的无参数闭 Δ₀ 公式均可由
纯逻辑证明或反驳。`PureRosserDelta0.sentence_not_delta0`、`comparison_not_delta0`
分别证明当前纯固定点和比较式在语法上不是 Δ₀；仅假定裸 ZFC 一致性，
`no_closed_delta0_equivalent` 还排除任何裸 ZFC 可证明等价的无参数 Δ₀ 闭句。
因此不能继续把“当前无参数纯 Rosser 闭句的正向 Δ₀ 分类”列为可补齐定理。

已完成的正向结果是纯 ∈ 的三参数矩阵：

```text
δ(w,A,B) := ¬∃ p∈w, p∈A ∧ ∀ q∈p, q∉B
```

`PureRosserDelta0.matrix_delta0` 证明其纯语言 Δ₀ 分类。`parameters_exists`、
`parameters_unique` 证明裸 ZFC 模型中可唯一取 `w=ω`，以及规范扩张内原完整证明图
对当前句子和否定的两个自然数证明码集合 `A,B`。`representation_derives` 给出实际推导
`ZFC ⊢ R ↔ ∃w,A,B (Def(w,A,B) ∧ δ(w,A,B))`。
`Def` 使用原证明图的实际纯翻译和分离；其复杂度未降为 Δ₀，完整存在闭句也已证明非 Δ₀。
这不是原证明谓词的纯 Δ₀ 定义或 `Agreement` 的证明。
内部算术与编码对应已完成，适用于任意原模型中的全部内部自然数，包括非标准自然数：

| 模块 | 已完成的对应 |
| --- | --- |
| `PureSourceMappings` | Kuratowski 有序对；关系和函数的纯语义；原合法映射的集合函数语义与定义域内求值 |
| `PureSourceArithmetic` | 原有限递推图进入纯集合函数唯一性接口；自然数加、乘、幂的实际取值保持 |
| `PureSourceCoding` | Gödel 配对、字段列表、任意标签节点及 quotation 的自然数封闭性和对应 |
| `PureNaturalRosserAgreement` | 实际根编码属于内部 ω，且在规范重扩张后保持；行归约接口已移除 `hRoot` 参数 |

证明只对实际集合函数图的值相等性质使用已有内部归纳，不假设内部 ω 外部标准。
局部检查与终局装配现已完成：

| 入口 | 结论 |
| --- | --- |
| `PureSourceHorn.condition_agrees`、`localTest` | 固定 Horn 轨迹及有限局部规则的对应；候选集合允许非标准行 |
| `PureSourceSchemas.axiomTest` | 实际固定公理表与模式连接公式对应，包括全部有界中间码 |
| `PureSourceLocalTests.currentNode`、`currentRow`、`row_agrees` | 当前节点检查、行检查及整树轨迹的实际行正文对应 |
| `PureSourceLocalTests.proof_agreement` | 任意固定结论、全部内部自然数证明码上的完整证明关系对应 |
| `PureRosser.agreement`、`independent` | 指定纯句子真值对应；只假定裸 ZFC 一致的双侧不可证性 |

完整纯 Rosser 闭句仍非 Δ₀；已接受的纯 Δ₀ 结果是三参数矩阵。`no_closed_delta0_equivalent`
已移除 `hAgrees` 参数，只要求裸 ZFC 一致性。原递归序列族之并的合法递归器全域性仍为独立数学待办，
不阻塞本次 Rosser 终局。最新默认完整构建通过 **796 个任务，0 错误，0 警告**。


## 文献系统

三卷《元数学基础》的模型友好知识库在 [knowledge/metamath-foundations](knowledge/metamath-foundations/README.md)。
优先看 [model-entry.md](knowledge/metamath-foundations/model-entry.md) 和 [query-guide.md](knowledge/metamath-foundations/query-guide.md)。
