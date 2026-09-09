# YesMetaZFC Agent Notes

## 当前恢复入口（2026-09-09）

- 可构建工作区：`/workspace/scratch/fb4803f63959/YesMetaZFC`；先执行
  `source /workspace/scratch/fb4803f63959/activate-yesmetazfc.sh`。
- 自由清理第二轮从 229,515 行独立计数，净减 **5,006 行**；当前 806 个 Lean
  源文件、224,509 行、211,291 个非空行。另有 837 行 Python/Shell，全部代码
  225,346 行，严格低于 20 万还需至少净减 25,347 行。前一轮净减 5,082 行另记。
- 最终全源严格检查 808 个任务、扫描工具 320 个任务通过，零错误、零警告。
  13,662 个既有公开声明全部保留，类型无实质变化；6,955 项数据定义中，6,953 项
  原始编译表达式相同，公理降低函数已额外证明任意输入返回的完整证书相等，
  自动化入口 try_close 按计划改进。60 项辅助声明增加对既有核心公理的部分引用，
  全仓公理并集及裸 ZFC Rosser 终点依赖集合保持；完整审计见 ENGINEERING.md。
- 本轮规范源码对应同一个 Google Drive `YesMetaZFC-source.zip`，文件 ID 为
  `1b9gV-m5sT7DEVhgNNSzsV9ZrkpzYeUID`；当前恢复使用该文件的最新版本或本工作树，
  不以早期来源包覆盖。本轮按用户授权在超过 5,000 行里程碑后更新该包。
- 此前 `/workspace/scratch/6e6aaba5102a` 的运行时已不可用，本次从 Drive 三个分片
  重新恢复并核对完整 SHA-256。当前实际工具链位于
  `/workspace/scratch/fb4803f63959/toolchains/lean-4.33.1-linux`，Lean 4.33.1。
  容器 readlink 兼容层只修复运行时定位，不进入源码包；普通 Linux 无需该层。
- 本次发布以 `b36e2434459fa71bd6d5ff91f0882058a9746399` 为父基点，将此前暂缓
  提交的累计工程精简汇总为一个发布节点，目标为 `origin/main`。用户已明确授权发布。
  后续以当前 Git 提交及其工作树为基点；下文历史记录中的“未提交”描述归档时状态。
  Lean 源码与本轮 Drive 包逐字节相同，本次发布额外更新三份工程文档的状态说明。

本仓库的 Lean 内核采用“文献对照但不照搬有限护栏”的路线。

## 元数学内核

- 文献中类似 `2020`、`2024`、`2010` 的公式级别界限，大概率服务于纸面提纲或有限检查，不映射为核心公理前提。
- 不要把 `Formula.LevelAtMost` 加回 `Formula.IsLogicalAxiom`、`Derives`、演绎方法、全域化方法或 1.4 常用逻辑定理的主接口。
- 核心证明优先使用普通 `Derives`；不要为了复刻文献的有限护栏重新引入 `BoundedDerives` 主线。
- `Formula.level` 和 `mf1_level` 可以作为文献兼容层/审计层工具保留，但它们不应阻塞核心自动化。
- 遇到文献里的“级别不超过某自然数”“具体表达式长度”等有限护栏，默认在 Lean 核心中解除映射；只有在显式建立兼容层时才单独形式化。
- 自动化里的 Skolem 化默认使用 Lean 元层 `Classical.choice` / `Classical.choose` 封装成证书构造函数；不要向对象语言核心加入新的 `ε` 算子公理。

## 当前 Rosser 公理表示路线

- `ReducedAxiomPacket.presentation` 已具体表示原 ZFC 基础公理像加有限支撑公理基。`ReducedAxioms.derives_iff` 已证明该基与原 `intrinsic_zfc_theory` 在任意上下文中推导等价；这不是两套公理集合逐字相等。
- `ReducedProofPresentation.nodeTest` 已具体构造节点 LocalTest；`ReducedProofPresentation.presentation` 已得到 `Delta1ProofPresentation intrinsic_zfc_theory intrinsic_zfc_theory`。`ObjectProofNode.ofNodeTest` 消费局部可靠性及全部实际证书编码的接受完备性，完成整树与 quotation 传输。它不要求在非规范外壳上逐值等于旧局部算法；不要声称这种额外等价已证明。
- `ObjectFormulaSyntax.checked_decode` 已证明完整内核公式的固定识别图与实际自然数 quotation / AST 解码精确一致；复用该图，不再重做公式良构识别。`ObjectSyntaxTransform` 已连接四种实际核变换，`ObjectLogicalAxiom` 已覆盖 27 类逻辑公理，`ObjectProofNode` 已覆盖全部六条核规则；复用这些图及其全自然数规格。
- 完整证明树对象表示已消费这个新公理基，并用 `ReducedAxioms.liftProofPresentation` 回到原目标理论。`ReducedRosser.sentence`、`fixed_point`、`independent` 已完成当前 quotation 下的具体固定点与仅假定一致性的不完备终局；后续任务是裸 ZFC 的支撑消去。原参数证书的逐字装配图及旧 union 路径不再是此路线的必要前置任务；不要把有限基的表示误报为原无限参数公理成员关系的精确表示。

- `Automation.ObjectDiagonal.fixedPoint_spec` 已对任意固定一元模板构造当前 quotation 的实际固定点。`ObjectLeastWitness.unique` 通过最小输出及码域切分把标准正负实例升级为任意对象输出的唯一性；不要把原 Horn 图的全对象函数性或新的反射公理加回前提。
- `ReducedRosser` 只从 `IntrinsicGraph` 复用 quotation 无关的 `intrinsic_zfc_core` 及数码码域证明。当前完整证明图使用 `ReducedNaturalProofPresentation.presentation.graph`，在 `ReducedProofPresentation.presentation.graph` 上增加内部 ω guard；不要回退到旧 `intrinsic_zfc_graph`。

- `Automation.RelationalTranslation` 的完整语法翻译、项/参数/公式/闭句语义正确性及 `expansion_realizes` 模型扩张均已完成。`derives_sound` 只给出目标模型真值，不是目标理论的句法推导变换，不能据此宣称裸 ZFC 保守性已证明。
- `PureModel.theory` 是原 ZFC 在纯 `ℒ` 签名下的像。`PureFunctionDefinitions.functional` 已从其模型公理证明原签名的空集、无序对、单集、并集、幂集、后继六种实际纯定义图的任意参数存在唯一性。`PureRelationFunctions` 已增加原符号索引下的 Kuratowski 有序对、左右投影与函数求值四种总图，并证明合法输入上的原规格；`PureRelationDefinitions` 已有子集、有序对、关系和函数谓词。最终完整公理验证见 `PureSupportModels` 与 `PureZFCModels`；未出现在有限基中的符号不计入本次消去范围。
- `SetTheory.Definitional.Project.FirstOrderSemantics` 已逐公式证明两套语法的语义桥；`PureModel.project_models` 将裸 ZFC 模型接入既有 Project 模型库。优先通过此桥复用已有分离、替换、自然数与递归定理。
- `PureKuratowskiProject.interpretation` 已具体填满纯 ZFC 模型上的 Kuratowski 编码解释；后续集合构造复用此解释和 `PureModel.project_modelsZF`。`PureMappingDefinitions` 已增加笛卡尔积、映射收集的纯图及任意参数存在唯一性，以及 `isMapping` 纯谓词。`PureMappingSpecifications` 已消去这两种构造原规格中的母集限制。
- `PureRelationCoordinates` 已完成定义域和值域的任意输入纯图及存在唯一性；`PureCoordinateSpecifications.coordinate_spec` 在关系 guard 下保留原投影筛选与双重并集限制，`mapping_definition` 已用实际坐标图填满映射定义，`application_spec` 直接消费定义域图的成员证据。`PureMappingOperations` 已完成恒等映射和函数限制的纯图、存在唯一性及原成员规格，并通过 Project 接口证明限制后仍为映射。这组基础模块覆盖十六个函数、六个关系（含隶属）的纯定义。任意输入的坐标与限制取值是所选扩张的定义，不是原支撑理论在非法输入上的额外定理。
- 第一轮新增九个函数、二十个关系；第二轮新增二十二个函数、七个关系，29 / 29 全部完成。第三轮十七个函数、十三个关系全部完成；累计六十四个函数、四十六个关系完成纯定义，有限支撑基内剩余符号为零。两个序型函数及拼接、展平均有实际纯图、任意参数存在唯一性和原规格对应。复用 `PureProjectTemplate`、`PureRelationSetOperations`、`PureOmegaAndReverse`、`PureRoundOneRelations`、`PureRoundOneSpecifications`、`PureStageSemantics`；完整三轮分组见 `ELIMINATION.md`。`graph_equation`、`definition_correct` 与 `dependencies_covered` 已确认原关系正文在具体阶段扩张中的等价和依赖覆盖。
- `PureStageBase` 对未处理函数暂取空集，最终关系阶段对未处理谓词暂取假，只服务于当前阶段；这些分支不算消去成果，不能声称已满足全部支撑公理。`PureStageSemantics.inductive_correct` 与 `PureRoundOneSpecifications.omega_definition_correct` 已将原归纳谓词、归纳核和 ω 接到同一模型。
- 最大／最小元素条件的关系方向已修正，与良序、最小元规格一致；该改动会改变相关源句和 quotation。`minimumDifference` 已改为源关系、源载体、第一函数、第二函数四个参数，quotation 按当前签名重建；其纯图及原 guard 下的存在唯一性现已完成，签名修复本身不单独计数。自然减法和递归序列的索引错位已修复，`NaturalArithmeticSemantics` 给出任意源模型、任意环境上的语义等价。
- 第二轮复用 `PureOrderExtrema`、`PureStageTwoBase`、`PureNaturalRelations`、`PureStageTwoSemantics`。极值有任意输入存在唯一性，并已从原 guard 推出合法输入规格；统一扩张逐参数满足三个原极值定义实例。六个新增关系按原正文翻译，第一轮关系正文在新阶段保持成立；不要把 `omegaPairLess` 的正文翻译误报为其标准配对良序性质。有界分离已由下述接口完成；第二轮内部自然数递归及所有函数现已完成，第三轮也已完成，转入完整公理验证。
- 第二轮七个收集类函数现已完成：`finiteSubsetCollection`、`powerSetBijection`、`indexOrder`、`finiteSequenceSpace`、`nonemptyFiniteSequenceSpace`、`recursiveSequenceSpace`、`omegaRecursiveSequence`。复用 `Project.FromFirstOrder`、`PureSeparation`、`PureBoundedDefinitions`、`PureFiniteSequenceSpace`、`PureCollectionStage`、`PureSequenceFilters`、`PureSequenceStage`。最后扩张逐参数满足七项原规格，且保留第一轮与自然数关系正文；有限序列界限使用模型内部 ω，不假定外部标准性。
- 跨阶段的模型选择项直接做定义展开会严重放大编译开销；使用纯 `openFormula` 翻译相同与语义正确性传输规格，参考 `PureCollectionStage.specification_transfer` 和 `PureSequenceStage.transfer_from_collection`。通用纯公式分离已经完成，不再逐构造重写 Project schema。
- 递归序列族及其并集的定义已完成；合法递归器下并集为 ω 上总函数的单独定理尚待证明。内部归纳与递推唯一性、加乘幂减的内部有限递推存在性及有限层级、传递闭包现均已完成。通用 `PureOmegaIteration` 直接消费 Project 递归定理，不等于原递归序列族并集的全域性定理。不要用模型 ω 的外部良基性代替内部递归。
- 最小差异点现由 `PureMinimumDifference` 完成：`difference_exists` 用同域映射外延性，`difference_set_exists` 用纯分离，`exists_of_guard` 用原良序；`unique` 只需线序。`PureDifferenceStage` 是最小差异点阶段扩张，其 `definition_instance_correct` 满足任意源项与任意环境下的原定义实例，并保持七个收集／序列函数和已有关系正文。
- 复用 `PureNaturalInduction.pure_induction`、`source_induction`、`omega_recurrence_ext`、`finite_recurrence_ext`。归纳只用于实际公式可分离的性质，不假定模型外部标准。`PureArithmeticRecurrence` 将加、乘、幂原规格归约到内部有限迭代并证明输出唯一；本次 `PureOrdinalArithmetic` 与 `PureArithmeticSpecifications` 已用替换收集实际算术值列补齐存在性及原规格对应。
- `PureOmegaIteration.functional`、`iterates_of_graph` 给出内部 ω 递归图及初值、精确定义域、后继方程；后继算子必须由自由闭合 Project 二元 schema 表示并有总唯一性。复用 `PureSetIterations` 的并集、幂集实例，不重复造递归框架。`PureTransitiveClosure` 用并集迭代的值域之并证明最小传递闭包；`PureNaturalDifference` 利用有限序数取并集等于截断前驱，限制迭代给出原减法规格。
- `PureNaturalDifferenceStage` 是此前的算术与集合构造阶段。`PureRoundTwoStage` 在其上增加两个序型、拼接和展平四个函数，统一满足四项完整原定义实例；`PureRoundTwoSpecifications` 保持此前算术、收集／序列、集合构造、最小差异点及关系正文。第二轮和第三轮已全部完成；完整支撑公理现由 `PureSupportModels.support_models` 验证，Rosser 句子对应已由 `PureRosser.agreement` 完成。
- 第三轮首批复用 `Automation.PredicateExpansion`、`PureLeastFixedPoint`、`PureSyntaxOperator`、`PureSyntaxFixedPoint`：正出现关系正文先换成候选集合成员关系，内部纯分离与单调性产生共同最小不动点，再按三种标签切片实现 `isTermCodeAt`、`isTermListCodeAt`、`isFormulaCodeAt`。不要循环展开递归正文，不要假定模型 ω 外部标准或外部良基。
- 第三轮首批扩张是 `PureStructureStage`：另实现 `relatedNonlogicalSymbolSet = ω` 和原 `isStructure` 正文，五项原定义在同一模型中成立；`PureRoundThreeSpecifications` 保持旧规格。三个关系只计实际纯图与原递归方程，不把解码定理重复计数，不声称任意递归解释唯一。
- 第三轮第二批扩张是 `PureRelatedStage`：第二批再完成 `isRelatedTermCodeAt`、`isRelatedTermListCodeAt`、`isRelatedFormulaCodeAt`、`relatedTermSet`、`relatedFormulaSet`、`modusPonens`。`PureRelatedSyntaxOperator` 与 `PureRelatedSyntaxFixedPoint` 按符号集参数使用既有最小不动点、元组查询及单射性；`condition_satisfaction` 明确核验原递归调用保持符号集，不得将候选算子忽略首参数推广到任意递归正文。
- `PureRelatedSyntaxSets.member_bounded` 用原递归方程的 ω guard；两个收集函数保留原存在深度量词，纯分离给出任意符号集上的唯一输出。`PureRelatedStage` 在原 guard 下满足完整原定义，并保留此前实际图、首批五项及第二轮最后四项定义；其他旧规格通过 `inherited_specification` / `prior_transfer` 的纯翻译相等条件传输。该批之后十四个函数均为逻辑公理集合；五个关系为 `termValue`、`termListValue`、`syntaxTransform`、`isLogicalAxiomCode`、`freeVariableOccurs`。
- 带参数语法算子只依赖第二轮已实现的基础符号，`dependencies_covered` 已验证；其核验直接使用第二轮解释。不要为方便而把整个后继阶段的选择证明展开进原子替换，曾导致内核核验内存激增。完整模型另行装配并证明 `Realizes`，实际图不丢失。
- 最后两轮收尾按依赖分成 9 + 10。第一轮完成七个命题公理集合、`quantifierDistributionAxiomSet`、`equalityReflexivityAxiomSet`。复用 `PureStructuralCodeBounds` 的内部 ω 封闭性与识别 guard，`PureLogicalSchemaSets` 用修正后的原成员正文、纯分离和外延性证明存在唯一；不另加源 guard，不把自然数界等同于良构性。
- 收尾第一轮统一扩张为 `PureLogicalSchemaStage`：九项成员规格、七项命题公理模式的整个源闭句、量词分配和等式自反的逐码定义均已完成；此前已完成实际图保持不变，旧规格使用 `transfer` / `inherited_specification` 传输。后续 `PureAllSchemaStage` 已补齐特化、空量化和等式替换，验证完整命题、量词及等式公理族。
- `LogicalRuleEncoding` 的量词问题已修正：12 种公理模式及公理码生成步骤使用 `exists_one` 等存在见证助手；真正的 `logical_axiom_code_closed_condition` 保留全称 `close_three`。源句及 quotation 已按修正后的定义重建；不能回退到旧的全称合取式成员条件，也不把修正本身单独计数。
- 收尾第二轮 10 个符号全部完成：`PureTransformStage` 实现 `syntaxTransform`、`freeVariableOccurs`；`PureDependentSchemaSets` 与 `PureAllSchemaStage` 补齐 `specializationAxiomSet`、`vacuousQuantifierAxiomSet`、`equalitySubstitutionAxiomSet`；`PureLogicalClosure`、`PureLogicalStage` 完成 `baseLogicalAxiomSet`、`logicalAxiomSet` 与 `isLogicalAxiomCode`。所选最小不动点的图唯一，不意味着原闭包公理或递归方程的任意解释唯一。
- `PureValueOperator`、`PureValueFixedPoint`、`PureValueStage` 实现互递归 `termValue`、`termListValue`。集合界使用内部 ω 与载体之并；`parameters_preserved` 实际核验原递归调用保持载体、解释、符号集、赋值四参数，不得省略此义务。没有模型 ω 的外部标准性或外部良基性假设。
- 最新统一扩张为 `PureCompletedStage`：有限基使用的 64 个函数、46 个关系均有实际纯图，两个原求值定义、全部模式与逻辑公理码闭句在此模型中成立。全部 119 条支撑公理及无限参数实例已由 `PureSupportModels.support_models` 统一验证；`PureZFCModels.models` 同时覆盖原 ZFC 公理像，`translated_models` 验证其实际纯翻译。`expands` 和任意原模型的 `reduction` 已填满；底层 `contract` 显式要求的 `hAgrees` 已由 `PureRosser.agreement` 提供。最终独立性见 `PureRosser.independent`；不要把模型保持本身误报为其证明。
- 大型图的跨阶段比较复用 `Automation.RelationalCongruence.openFormula_congr`，通过源语法覆盖及逐符号图相等传输，不对整个目标翻译使用定义展开。原正文的形状及参数保持先在抽象源模型证明，再用 `Automation.PredicateCongruence.evaluate_congr` 等接口接入实际关系，避免内核展开嵌套不动点造成内存激增。多变量算子用直接 `existsE` 块与模板接口，避免反复自由变量闭合。
- `PureNaturalInduction.source_induction` 的源模型固定为较早的 `PureDifferenceStage`，只可直接用于该模型中已实现的正文。若归纳性质使用本次或后续新增函数，应以最新解释的 `openFormula` 调用 `pure_induction`，再用语义正确性传回；不能把新函数的实际取值与旧阶段的临时空集解释混用。
- `NaturalSetTheory` 的自然序型目标关系已修正为 `ε(candidate)`，有界自然数子集序型的源关系已修正为 `ε(subset)`；完整 `ε(ω)` 不能作为有限载体上的原线序关系。修复会改变源句及 quotation；两个序型函数的存在唯一性与规格对应现已由 `PureFiniteOrderTypes`、`PureNaturalOrderType`、`PureBoundedNaturalOrder`、`PureNaturalSubsetType` 完成；修复本身不单独计数。
- `PureOrderSemantics` 精确保留原线序的关系载体限制，并桥接原双射、序同构和极值条件；自然序型必须由实际良序坍缩与原最大元条件推出内部有限性，不得直接假定序同构存在。`PureBoundedNaturalOrder.greatest_of_bounded` 通过最小严格上界构造最大元。
- `PureReplacement.mapping_exists` 将当前纯二元正文收集为集合函数图，明确总定义、唯一性与目标范围。`PureFiniteSequenceCore` 提供函数外延性和内部加法分段，`PureSequenceConcatenation` 已证明原拼接规格。
- `PureFlattenRecursion.accumulator_exists` 使用携带族参数的纯历史算子和内部递归，累积长度精确为族长度后继。`PureSequenceFlatten.accumulator_finite_values` 用最新解释的纯公式归纳保持有限性；`accumulator_unique` 只对旧基础函数值相等性质使用旧 `source_induction`，其外部递推步骤消费新拼接函数。四项均经总化保留原 guard，不要求非法输入满足原规格。
- `Automation.TotalizedGraph` 只在原图无输出时使用缺省图，并分别证明总唯一性与有输出时的精确保持。投影/求值原公理具有 guard；不能从总化构造推出原支撑理论的全语言往返等价。
- `Automation.SemanticTransfer.reflect` 由源模型约化和指定句子真值对应，经强完备性反射目标推导；`consistent_of_expands` 用目标模型扩张传输一致性。`PureRosserTransfer.Contract` 的当前实例已填满：具体解释、公理、扩张及约化由 `PureZFCModels` 给出，调度由 `PureRosserSchedule` 给出，任意原模型上的指定句子对应为 `PureRosser.agreement`。直接裸 ZFC 终局是 `PureRosser.independent`。这不宣称整个源语言的无条件往返保守性。
- 旧 `Definitional.Audit.Pure` 使用另一套 AST，不可直接替代当前核的消去证明。

## 纯 Rosser 配置

- 当前入口 `PureRosser.sentence` 是 `ReducedRosser.sentence` 经 `PureCompletedStage.interpretation` 的实际纯翻译；`comparison` 固定当前完整证明树的 Rosser 比较式。用户于 2026-09-08 明确批准切换到内部自然数证明表示，现已接入并重新生成源固定点及其 quotation；源签名、公理和 quotation 编码规则不变。当前句子不是纯语言自身 quotation 上重新对角化的结果。
- `PureRosserSchedule.source`、`target` 已有具体公平调度。通用符号及内在语法单射编码位于 `Automation.SyntaxNatCoding`；编码只用于 Henkin 完备性，不替换对象理论的 quotation。
- `PureRosser.translate_derives` 已证明源闭句推导向裸 ZFC 推导的传输；`fixed_point` 是纯句子与比较式否定之间的实际 Hilbert 推导。该正向推导传输不等于反向保守性。
- `PureRosser.agreement_iff_comparison` 把剩余 `Agreement` 严格等价归约为 `ComparisonAgreement`，无需再处理对角公式。`truth_iff` 只比较规范扩张，不能填任意原模型的 `Agreement`；`independent_of_agreement` 保留底层条件接口；`PureRosserComplete` 中的 `agreement` 实际证明该条件，`independent` 仅要求裸 ZFC 一致。
- 大公式实例先在公式参数上证明联结词保持（`translate_fixed_point`），再显式代入源句子和比较式；直接对具体 quotation 做定义等价转换会引发内存激增。实际纯公式定义保持可展开，但不生成原生代码。
- `PureSourceNumerals` 已证明任意原模型与其规范重扩张的空集、后继、标准 numeral、quotation 取值对应及全部标准证明码实例的真值对应。标准码真值证明先使用通用 `Automation.NaturalProofPresentation.models_agree`，避免对具体巨大证明图做内核展开。
- `RosserDomainBoundary.domain_agrees` 已证明后继码域真值保持；`domain_not_subset_naturals` 用 ω 自身证明该码域不包含于内部自然数集合。`pairing_instance_vacuous` 证明非自然数首参数使原配数定义实例自动成立。未包装的完整证明图只把编码后的根节点限制在 ω，不能据此直接断言输入码属于 ω；当前自然数包装已显式限制输入。这个旧码域边界不是 `Agreement` 的反例或不可证明性定理。
- `Automation.NaturalProofPresentation` 为任意完整证明表示增加 `code ∈ ω` guard，保留原检查器、全部标准码正负表示和完备性；实际实例现为 `ReducedNaturalProofPresentation.presentation`，已接入 `ReducedRosser.presentation` 的 `proof` 与 `assembly`。旧的候选实例已迁至这个无循环依赖的模块，不保留重复别名。
- `PureSourceInfinity.omega_agrees` 从原归纳集定义和归纳核方程证明任意原模型的 ω 与规范重扩张相同。`member_natural`、`natural_compare` 覆盖全部内部自然数；`RosserDomainBoundary.natural_in_domain` 证明它们满足旧后继码域。
- `Automation.NaturalRosserSemantics` 统一处理模板与比较式的值语义；`PureNaturalRosserAgreement.comparison_naturals` 已把实际新比较式精确化为内部自然数见证及其初始段上的原完整证明图。`agreement_of_natural_proofs` 是已验证的充分条件接口，仍要求当前句子及其否定的 `ProofAgreement`。这两项现由 `PureSourceLocalTests.proof_agreement` 提供，`PureRosser.agreement` 已闭合。证明覆盖非标准内部自然数；不得用外部标准性替代此证明。
- 用户建议压到 Δ₀。`NaturalProofPresentation.comparison_delta0` 已用现有正位置 ω guard 分类实际比较式；`ReducedRosser.predicate_delta0`、`delta0Sentence_delta0`、`delta0Sentence_independent` 已验证支撑语言中的比较式及等价代表。`delta0Sentence := ¬ presentation.predicate_of sentence`，复用既有 `fixed_point` 等价，不重新改变源固定点或 quotation。分类相对于含 ω、幂集和编码函数的支撑语言，不能报告纯隶属或一阶算术 Δ₀ 已完成；通用 Δ₀ 绝对性仍需逐符号解释对应，不能据此跳过逐符号解释对应义务。
- `PureSourceBounds.power_agrees`、`trace_bound_agrees` 已证明任意原模型的全部幂集值及实际 `P(ω)` 界保持；`trace_row_natural` 约束候选轨迹的全部行。`ReducedProofPresentation.rowTest`、`graph_condition` 暴露实际行模板，`ObjectTrace.condition_satisfies` 与 `PureNaturalRosserAgreement.proof_trace` 给出完整图的集合轨迹语义。`PureNaturalRosserAgreement.root_agrees` 已证明内部自然数根编码对应，`proof_agreement_of_rows` 已移除 `hRoot` 参数，其候选轨迹内局部行前提现由 `PureSourceLocalTests.row_agrees` 提供。不得重新把根编码列为待证，亦不增加模型外有限性假设。
- 纯 Δ₀ 目标已作严格修正：`ℒ` 只有二元 ∈、无常元或函数。`Automation.FunctionFreeDelta0.closed_decided` 证明无函数且无零元关系的语言中，每个无参数闭 Δ₀ 公式或其否定都有普通逻辑推导。`PureRosserDelta0.sentence_not_delta0`、`comparison_not_delta0` 无条件排除当前两个纯闭句的语法 Δ₀；`no_closed_delta0_equivalent` 已移除 `hAgrees`，仅假定裸 ZFC 一致就排除所有 ZFC 可证明等价的闭 Δ₀ 代表。不要继续把这个不可能的正向闭句分类列为待填定理；带参数矩阵是另一项结论。
- `PureRosserDelta0.matrix_delta0` 已分类实际纯 ∈ 矩阵 `¬∃p∈w (p∈A ∧ ∀q∈p q∉B)`；没有支撑符号。`proofCondition` 是原完整对象图的实际纯翻译，`parameters_exists`、`parameters_unique` 用纯 ZFC 分离给出唯一的 ω 与两侧内部证明码集合。`sentence_iff_matrix` 连接当前纯 Rosser 真值，`representation_derives` 给出 `ZFC ⊢ R ↔ ∃w,A,B (Def(w,A,B) ∧ δ(w,A,B))`。参数定义未分类为 Δ₀；`representation_not_delta0` 明确整个存在闭句非 Δ₀。集合的语义来自规范扩张，不能据此完成任意原模型的 `Agreement`，也不能声称证明谓词已获得纯 Δ₀ 定义。
- `ObjectDiagonal.fixedPoint_shape` 现公开；`ReducedRosser.sentence_exists_body`、`predicate_exists_body` 把实际正文保持为存在参数，供层级证明使用。不要为检查最外层量词而展开具体巨大 quotation；曾造成内核归约耗时和内存激增。源固定点、比较式、签名、公理与 quotation 编码没有改变。

- `PureSourceMappings.ordered_code`、`ordered_agrees`、`function_predicate` 已确定任意原模型的 Kuratowski 编码与纯函数语义。`mapping_project` 将原合法映射变为同一约化模型中的纯集合函数；`application_value`、`application_agrees` 只约束原定义域内的求值，不宣称非法输入上的总值对应或映射谓词的无条件反向等价。
- `PureSourceArithmetic.specification` 读取任意原模型的实际加乘幂有限递推图；`iteration_project` 接入既有 `PureArithmeticRecurrence.iteration_unique`，`iteration_change_step` 只使用图值落入 ω 的证据。`addition_agrees`、`multiplication_agrees`、`exponentiation_agrees` 依次完成全部内部自然数上的取值对应，无外部标准性假设。不要将原模型的任意额外谓词直接用于纯分离或内部归纳。
- `PureSourceCoding.pairing_agrees` 用原两分支配数规格、内部三歧性及已证明的算术对应；`fields_agrees`、`node_agrees` 覆盖任意有限语法字段列中的内部自然数值。`quotation_natural` 复用既有 numeral 求值，不展开巨大 quotation。`PureNaturalRosserAgreement.root_natural`、`root_agrees` 已实际接到完整图；局部行检查、两个 `ProofAgreement` 及 `Agreement` 现均已填入，见后述终局模块。源固定点、公理、签名、quotation 和已接受的纯 Δ₀ 参数矩阵均未改变。

## 统一验证与恢复记录

- 2026-09-08 最新验证门：实际局部行、内部证明图与裸 ZFC Rosser 终局后 `lake --wfail build` 796 个任务通过，零错误、零警告；内部算术、编码与根值对应阶段为 790；此前纯 Δ₀ 参数矩阵为 787，支撑 Δ₀/轨迹归约为 785，内部自然数迁移为 783，基础对应为 779，Rosser 配置为 776，支撑统一验证为 773 个任务。沿用项目既有原生计算可信基，审计范围见验证文档。
- 2026-09-08 统一验证：108 个具体闭句及 11 个参数分离模板，共 119 条有限基公理；逐项索引见 `UNIFIED_VERIFICATION.md`。原无限参数族经 `FiniteAxiomBasis.models_iff` 和普通推导覆盖。
- `Automation.ModelClosure` 处理值列、任意环境和全称闭包；`Automation.RelationalTransfer` 通过覆盖及图相等传输。`PureFinal*` 各模块验证原闭句；不要把这些证明重新改为展开大图或枚举样本。
- 统一验证修正两处实际图：`PureOmegaAndReverse.reverseGraph` 必须对任何输入等于交换两个总投影后的有序对；原反转公理没有 guard。`PureRelationSetOperations.relationCompositionGraph` 的函数槽是 `second ∘ first`，经 `relationComposition_order` 接到按执行顺序的成员规格。不要恢复先前的空集反转分支或反向复合接线。
- `PureProjectEmbedding` 比较 Project 到源签名和纯签名的实际嵌入，显式消费子集语义。`PureZFCModels.reduct_models` 适用于任意原模型，而非仅规范扩张。
- Lean 4.33.1 的完整 Linux 运行时及三个分片确实存于 Google Drive 根目录，恢复路径与校验和见 `RESTORE.md`；不要只搜索源码目录或因全文搜索无结果而断言运行时不存在。

- `Automation.ObjectHornSemantics` 给出任意模型中有界见证块与规则矩阵的值语义。`PureSourceHorn.condition_agrees` 比较同一候选集合轨迹，递归前提只读取该集合；没有按模型 ω 做外部归纳。`localTest` 用已对应的查询组合有限局部规则表。
- `PureSourceFormula` 的 `Natural` / `Stable` 以自然数环境和逐变量相等为前提；`quantify` 由原公式自然数界保证全部见证自然，`instantiate` 沿实际模板代入传输。不应去掉自然数环境条件，或把这些定理用于原公理未约束的非法函数输入。
- `PureSourceSchemas.axiomTest` 覆盖实际固定公理表及分离、收集、替换模式的中间码连接。`PureSourceLocalTests.currentNode`、`currentRow`、`row_agrees` 复用实际规则表；`proof_agreement` 对任意固定结论及全部内部自然数证明码成立。不要重新枚举巨大公理表或 quotation。
- `PureRosserComplete` 中的 `PureRosser.agreement` 和 `independent` 已消去最后的条件前提。后者仅要求裸 ZFC 一致。当前闭句是源 Rosser 的实际纯翻译，完整闭句非 Δ₀；已接受的纯 Δ₀ 三参数矩阵保持不变。20 个新增及终局接口依赖审计无 `sorryAx`，原生可信依赖集合没有增加。

## 形式化习惯

- 参数列骨架归纳复用 `Arguments.listRec`；需要同时证明项与参数列时优先相互结构递归，
  不在两个定理里各写一套完整 `Term.rec` / `Arguments.rec`。
- Hilbert 编译像使用 `Formula.hilbertize_induction` 的五种原始构造，派生联结词在底层
  统一展开；四种 quotation 变换已经迁移。码域与深度事实消费
  `FormulaStructuralCorrectness` 的 `quote_*_expression` 接口。
- 搜索语法编码的单射性通过精确编码等式复用 `SyntaxNatCoding`；不改变已有编码定义。
  大型检查器的通用接受实例先固定参数列，再与目标匹配，避免未定参数触发计算展开。
- Skolem 扩展复用 `UniformFrameExtension.refl` / `trans` 和 `UniformSoundExtension.refl`，
  复合必须显式保留新鲜变量与函数界的单调性以及环境和类型合同。


- 同一行列表生成公式列和证书列时，复用 `IntrinsicCheckedSequence.intro_of_mapped_rows`。
  它提供两个取值坐标等式，实例仅提交行条件；不要重做长度、`List.map` 成员和索引装配。
  逻辑行的实际 quotation 码域与目标上下文提升复用 `IntrinsicLogicalTranscriptSupport`
  的 `intrinsic_zfc_quote_*`，完整证书复用 `intrinsic_zfc_logical_certificate_mem_omega`。
  单行特化是特化 transcript 的单元素实例；空泛全称仍需正文的深度提升识别。
- 存在见证块复用 `Derivation.QuantifierBlock`：`Arguments.substitutionWith` 携带任意排序的
  见证列，`Formula.existsFreePrefix` 关闭自由槽前缀，`Derives.existsFreePrefix_intro`
  一次性引入见证并保持外部自由参数。列表头对应最内层见证；不要按元数复制 binder
  展开或增加新的二、三、四槽专用证明。Quine 的 22 处构造已消费这一接口。
- Quine 的常量、应用、空参数列和 cons 构造复用
  `TransformStructuralCorrectness.syntax_transform_*_shape`（声明位于 `QuineEncoding` 命名空间）。
  四种变换直接给出操作码、深度、变量位置和替换项，不再维护操作专属的 shape 证明。
  公共定理适用于任意目标理论及自由上下文为空的假设列表；常量符号可为任意闭项，
  只需给出其内部 ω 成员证明。它们仅装配 shape，scope 与总码域仍由原接口保证。
- 规范化的类型分解与环境接口复用 `CoreNormalForm.RewriteTyping`。
  FOOL 与高阶项的类型保持复用 `eval_mem_of_inferSortWith_fragment`；
  具体根规则提供 `RootRewriteSemantics`，外层上下文可靠性复用三个 `*_of_root`
  入口。保留 FOOL 片段 guard 和高阶 λ 的受类型限制同余，不重新维护两套语法归纳。
- 类型化槽位替换复用 `Derivation.Substitution.Algebra` 的 `postcompose`、`map_cons`
  与弱化尾映射定理；具体模板不再按参数个数重复语法归纳。实际 quotation 的公式归纳
  复用 `Automation.QuotationInduction.FormulaClosure`，伴随码域事实可并入其谓词。
  当前深度识别应由 `*_of_depth` 实例化，不维护第二套项或参数列递归。
- 工程维护与已测热点见 `ENGINEERING.md`。不要仅凭默认导入图不可达删除模块；
  `ProveAutoBranchProbe` 由扫描器动态导入，独立源模块由 `scripts/check-all.sh` 验证。
- 大模型上的等式替换优先固定替换参数与目标类型。`PureSyntaxFixedPoint.tag_injective`
  使用 `congrArg (membership ℳ input)` 避免猜测替换目标；不要恢复代价高昂的隐式替换
  和九分支回溯。固定公式的布尔覆盖检查可用 `decide +kernel`，不因此增加原生可信依赖。
- 无引用私有声明、退役回放实现及空兼容入口已清理；不要恢复常开的 `simp.rewrite` 追踪。

- 机械 Hilbert 证明优先改进或复用 tactic，不要手写长证明序列。
- 通用自动化层放在 `YesMetaZFC.Automation` 及其子模块；具体集合论或元数学目录只保留领域接口，不承载通用证明器实现。
- 后续 CDCL、前束规划、超消元叠加演算等证明器基础设施不要下沉到具体章节目录。
- 自动化后端共用 `YesMetaZFC.Automation.Certificate` 与 `YesMetaZFC.Automation.DAGCertificate` 的公共证书内核；新增后端时优先提供 checked payload 到公共 DAG 节点的映射。
- 一阶规范化、NNF、前束规划、局部 Skolem 化和定义性 CNF 属于 `YesMetaZFC.Automation.CoreNormalForm` / `YesMetaZFC.Automation.SourcePreprocessing` 公共前端；领域文件只消费其接口。
- 双核自动化调度放在 `YesMetaZFC.Automation.Scheduler`，负责串联预处理、Superposition 与 CDCL residual，不要写入具体定理文件。
- 面向用户的新自动化 tactic 名称是 `prove_auto`；不要在新章节证明里继续使用旧的 `mf1_fo_core` 入口。
- residual 命题后端证书放在 `YesMetaZFC.Automation.Resolution`、`YesMetaZFC.Automation.PropCdcl` 与公共 DAG 证书层，优先生成可计算、可重放的 checked payload。
- 证明接口优先长线复用性；如果一个限制只来自文献排版或提纲，不要传播到公共 API。
- 构建验证使用 `lake build`。
- `prove_auto_sweep` 只静态导入 `Automation.HostAvatar.Dispatch`，完整库由已有运行时导入加载。不要将其改回静态导入根 `YesMetaZFC`；大型闭式公理编码会在命令行处理前触发原生初始化栈溢出。工具依赖改动后需验证 `--help` 及一次有目标的实际扫描。
- 对已由通用定理覆盖的性质，信任 Lean 内核及项目既定可信基；不另行维护样本枚举、`#eval` 回归或仅重复调用这些定理的 `example` 模块。验证使用正式定理的正常构建，保留有独立数学内容的规格、正确性及正负表示证明。
- 注释使用中文。
- 证明跑通后，再做一轮人类数学可读性清理。

## 集合论接口符号约定

- `ℒ` 固定表示纯集合论语言 `SetTheory.PureSetLanguage`，不要把它复用为任意语言变量。
- `ℳ` 表示当前主要结构，`𝒩` 表示第二个或目标结构，`𝒱` 只用于具有 ambient universe
  角色的结构。
- `𝒞` 表示 `OrderedPairConvention`，`𝕀` 表示 `𝒞.Interpretation ℳ`；多结构场景使用
  `𝕀ₘ`、`𝕀ₙ`。
- `α β γ δ ξ η θ` 默认表示序数，`ω` 默认表示满足 `ℳ.IsOmega` 的最小超限序数，
  `κ λ μ` 预留给基数；这些数学性质仍必须由 `hα`、`hω`、`hκ` 等显式假设给出。
- `Ord` 只在文献和注释中表示全体序数组成的类。Lean 接口使用 `ℳ.IsOrdinal`；
  不声明裸 `Ord` 常量，以免与 Lean 核心的 `Ord` 类型类冲突。
- `Γ Δ` 表示理论或上下文，`φ ψ χ` 表示公式，`s t u` 表示项，`F G H` 表示类函数、
  schema 或递归算子。
- 单结构理论假设使用 `hZF`、`hKP`、`hZFC`；多结构场景使用 `hℳZF`、`h𝒩ZF`。
- 结构和可推断的依赖参数默认隐式；有序对解释及模型公理证明默认显式。若 `𝒞`
  不出现在返回类型中，仍应显式传入，避免留下无法推断的 metavariable。
- 不把结构、模型公理、有序对解释、`IsOmega` 或未来的 `IsCardinal` 做成 typeclass，
  也不通过 `Classical.choose` 固定全局模型相关的 `ω`。
- 接口迁移按完整模块或完整层进行，同时更新命名参数调用；不保留旧变量名兼容层。

## 稳定基点与公共区卫生

- 按当前用户授权，规范源码持续更新 Google Drive 中同一个 `YesMetaZFC-source.zip`（ID 见当前恢复入口）。后续从其当前版本或已验证工作树继续；不要创建按日期、轮次或版本号命名的平行源码包。早期 `/Projects/YesMetaZFC/YesMetaZFC-source.zip` 是历史来源，未同步当前精简，不得用其覆盖最新工作。
- 更新源码包保持同一 Drive 文件身份；报告更新也保持各自文件身份和版本历史。若无法确认原文件、遇到版本冲突或没有替换权限，先保留当前工作并说明阻碍，不要用“另存一份”绕过。
- 源码修改和形式化研究在 scratch 工作区进行。只有达到稳定基点后才回写规范源码包：至少要求 `lake build` 成功，相关额外目标或未接入默认构建图的改动模块也已单独验证，并且没有新引入未说明的 `sorry`、`admit` 或自定义公理。
- 回写前更新必要的源码、测试和状态说明；研究草稿只有在已经转化为可复核的定义、定理、证明或明确要求保留的单一研究文档后才进入稳定基点。
- 源码包只包含可复现项目所需的源码、配置和文档。不要打包 `.lake/`、编译产物、Lean/elan 缓存、临时日志、探针文件、环境兼容 shim、备份文件或旧源码压缩包。
- 公共区原则上只保留一个当前稳定源码包；用户明确要求的发布物或报告也应采用单一持续更新文件。中间检查点、失败日志和一次性分析留在 scratch，不在公共区堆积。
- 不删除或覆盖来源不明的用户文件。公共区确需整理时，先解析文件身份与用途，只更新上述规范基点；其他历史文件的删除必须取得用户明确授权。
