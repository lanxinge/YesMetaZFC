# 纯 ZFC 定义基础设施指路表

范围是 `SupportAxiomBasis.intrinsic_proof.compact.axioms` 的 119 条有限基公理实际
使用的 **64 个函数、46 个关系**。这些符号均已有纯隶属定义；函数有任意裸 ZFC
模型、任意参数上的存在唯一性及合法输入规格，关系有原正文在具体扩张中的等价。
签名里没有被该基使用的符号不计入此覆盖范围。

统一解释为 [PureCompletedStage](../YesMetaZFC/Model/ZFC/Pure/PureCompletedStage.lean)；原支撑公理验证见 [PureSupportModels](../YesMetaZFC/Model/ZFC/Pure/PureSupportModels.lean)，
裸 ZFC 模型扩张与原模型约化见 [PureZFCModels](../YesMetaZFC/Model/ZFC/Pure/PureZFCModels.lean)。指定 Rosser 的任意原模型对应和
独立性由 [PureRosserComplete](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) 给出，均不再是支撑消去待办。
纯句子的双向推导见 [PureSentenceTransfer](../YesMetaZFC/Model/ZFC/Pure/PureSentenceTransfer.lean)；
原编码表示的纯语言可证明性、Löb 与哥二已落在 `PureModel.theory`，入口见 [TROPHIES.md](TROPHIES.md)。
[PureOpenTransfer](../YesMetaZFC/Model/ZFC/Pure/PureOpenTransfer.lean)
补齐任意有限参数下的环境往返和双向推导；`PureTarskiSource` 在同一裸理论中给出
保留源公式编码的带参数真不可定义性。`PureQuotation`／`PureFixedPoint`／`PureTarski`
另已完成最终纯公式自身编码的固定点及真不可定义性：只消元实际的自编码图，
最终纯 AST 的编码由结构等式单独核验。

## 集合构造与规格传输

| 需要的基础 | 接口与源码 | 使用条件 |
| --- | --- | --- |
| 复用 Project 模型库 | [Project/FirstOrderSemantics](../YesMetaZFC/Model/SetTheory/ProjectSemantics.lean) 的 `formula_correct`、`models_iff`；[PureModel](../YesMetaZFC/Model/ZFC/Pure/PureModel.lean) 的 `project_models`、`project_modelsZF` | 显式传入模型公理和解释；两套语法通过语义桥连接 |
| 纯模型上的有序对解释 | [PureKuratowskiProject](../YesMetaZFC/Model/ZFC/Pure/PureKuratowskiProject.lean) 的 `interpretation` | 复用实际 Kuratowski 图，不重新选择不相关的解释 |
| 纯公式分离与替换收集 | [PureSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSeparation.lean)、[PureReplacement](../YesMetaZFC/Model/ZFC/Pure/PureReplacement.lean) 的 `mapping_exists`、[PureProjectTemplate](../YesMetaZFC/Model/ZFC/Pure/PureProjectTemplate.lean) 的 `bounded_functional` | 明确总定义、唯一性、目标范围和实际自由闭合公式 |
| 跨阶段保持原规格 | [RelationalCongruence](../YesMetaZFC/Model/Interpretation/RelationalCongruence.lean) 的 `openFormula_congr`、[RelationalTransfer](../YesMetaZFC/Model/Interpretation/RelationalTransfer.lean) 的 `transfer_regraph` / `transfer_covered`、[ModelClosure](../YesMetaZFC/Model/Interpretation/ModelClosure.lean) | 翻译相等直接连接源与目标；覆盖只用于建立翻译相等，不加强任意正文传输的前提 |
| 覆盖保持链与函数规格 | [RelationalInheritance](../YesMetaZFC/Model/Interpretation/RelationalInheritance.lean) 的 `CoveredExtension`、`FunctionSpecification`、`specification_regraph` | 证书只保证原覆盖内的图；任意图等式仍可直接使用规格传输。规格合同保留全部参数，guard 由调用者原假设提供 |
| 连续阶段的实例 | [PureCollectionStage](../YesMetaZFC/Model/ZFC/Pure/PureCollectionStage.lean) 的 `specification_transfer`；[PureSequenceStage](../YesMetaZFC/Model/ZFC/Pure/PureSequenceStage.lean) 的 `transfer_from_collection` | 只消费阶段已经实现的图和关系，不把临时默认值当作最终规格 |
| 内部归纳与递推唯一性 | [PureNaturalInduction](../YesMetaZFC/Model/ZFC/Pure/PureNaturalInduction.lean) 的 `pure_induction`、`source_induction`、`omega_recurrence_ext`、`finite_recurrence_ext` | 性质必须由实际可分离公式表达；`source_induction` 固定早期 Difference 阶段 |
| 通用内部 ω 迭代 | [PureOmegaIteration](../YesMetaZFC/Model/ZFC/Pure/PureOmegaIteration.lean) 的 `functional`、`iterates_of_graph` | 后继算子由自由闭合 Project 二元 schema 表示且总唯一；模型参数显式保留 |
| 递归语法与求值图 | [PredicateExpansion](../YesMetaZFC/Model/Interpretation/PredicateExpansion.lean)、[PureLeastFixedPoint](../YesMetaZFC/Model/ZFC/Pure/PureLeastFixedPoint.lean)、[PureSyntaxOperator](../YesMetaZFC/Model/ZFC/Pure/PureSyntaxOperator.lean)、[PureValueOperator](../YesMetaZFC/Model/ZFC/Pure/PureValueOperator.lean) | 正出现、集合界、单调性和递归参数保持不可省略 |

## 符号到实现的导航

下表按数学用途分组，覆盖上述 110 个符号。源码中的 `RoundOne`、`RoundTwo`
等是现有模块名；它们在此作为接口位置使用，不表示待执行轮次。

| 符号 | 实际定义与规格入口 |
| --- | --- |
| `emptySet`、`unorderedPair`、`singleton`、`union`、`powerSet`、`successor` | [PureFunctionDefinitions](../YesMetaZFC/Model/ZFC/Pure/PureFunctionDefinitions.lean) 的 `functional` |
| `orderedPair`、`leftProjection`、`rightProjection`、`application` | [PureRelationFunctions](../YesMetaZFC/Model/ZFC/Pure/PureRelationFunctions.lean) |
| `membership`、`subset`、`isOrderedPair`、`isRelation`、`isFunction` | [PureRelationDefinitions](../YesMetaZFC/Model/ZFC/Pure/PureRelationDefinitions.lean)；隶属直接使用纯签名 |
| `cartesianProduct`、`mappingCollection`、`isMapping` | [PureMappingDefinitions](../YesMetaZFC/Model/ZFC/Pure/PureMappingDefinitions.lean)、[PureMappingSpecifications](../YesMetaZFC/Model/ZFC/Pure/PureMappingSpecifications.lean) |
| `domain`、`range` | [PureRelationCoordinates](../YesMetaZFC/Model/ZFC/Pure/PureRelationCoordinates.lean)、[PureCoordinateSpecifications](../YesMetaZFC/Model/ZFC/Pure/PureCoordinateSpecifications.lean) |
| `identity`、`restriction` | [PureMappingOperations](../YesMetaZFC/Model/ZFC/Pure/PureMappingOperations.lean) |
| `binaryUnion`、`symmetricDifference`、`relationConverse`、`relationComposition`、`membershipRelation`、`image`、`inductiveCore` | [PureRelationSetOperations](../YesMetaZFC/Model/ZFC/Pure/PureRelationSetOperations.lean) 的 `functional` |
| `omega`、`orderedPairReverse` | [PureOmegaAndReverse](../YesMetaZFC/Model/ZFC/Pure/PureOmegaAndReverse.lean)、[PureRoundOneSpecifications](../YesMetaZFC/Model/ZFC/Pure/PureRoundOneSpecifications.lean)、[PureStageSemantics](../YesMetaZFC/Model/ZFC/Pure/PureStageSemantics.lean) |
| `isEquivalenceRelation`、`isInjective`、`isSurjective`、`isBijection`、`isTransitiveSet` | [PureRoundOneRelations](../YesMetaZFC/Model/ZFC/Pure/PureRoundOneRelations.lean)、[PureRoundOneSpecifications](../YesMetaZFC/Model/ZFC/Pure/PureRoundOneSpecifications.lean) |
| `isLinearOrder`、`isOrderIsomorphism`、`isOrderIsomorphic`、`isOrderEmbedding`、`isOrderEmbeddable`、`isNaturalDiscreteLinearOrder`、`isWellOrder` | [PureRoundOneRelations](../YesMetaZFC/Model/ZFC/Pure/PureRoundOneRelations.lean)、[PureOrderSemantics](../YesMetaZFC/Model/ZFC/Pure/PureOrderSemantics.lean) |
| `isFinite`、`isEquinumerous`、`cardinalityLeq`、`cardinalityStrictLess`、`isDedekindFinite`、`isInductiveSet`、`isUnboundedSubset`、`isBoundedSubset` | [PureRoundOneRelations](../YesMetaZFC/Model/ZFC/Pure/PureRoundOneRelations.lean) 的 `graph_equation`、`definition_correct`、`dependencies_covered`；[PureRoundOneSpecifications](../YesMetaZFC/Model/ZFC/Pure/PureRoundOneSpecifications.lean) |
| `minimum`、`maximum` | [PureOrderExtrema](../YesMetaZFC/Model/ZFC/Pure/PureOrderExtrema.lean)、[PureStageTwoSemantics](../YesMetaZFC/Model/ZFC/Pure/PureStageTwoSemantics.lean) |
| `minimumDifference` | [PureMinimumDifference](../YesMetaZFC/Model/ZFC/Pure/PureMinimumDifference.lean) 的 `difference_exists`、`difference_set_exists`、`exists_of_guard`、`unique`；[PureDifferenceStage](../YesMetaZFC/Model/ZFC/Pure/PureDifferenceStage.lean) |
| `finiteSubsetCollection`、`powerSetBijection`、`indexOrder` | [PureBoundedDefinitions](../YesMetaZFC/Model/ZFC/Pure/PureBoundedDefinitions.lean)、[PureCollectionStage](../YesMetaZFC/Model/ZFC/Pure/PureCollectionStage.lean) |
| `finiteSequenceSpace`、`nonemptyFiniteSequenceSpace`、`recursiveSequenceSpace`、`omegaRecursiveSequence` | [PureFiniteSequenceSpace](../YesMetaZFC/Model/ZFC/Pure/PureFiniteSequenceSpace.lean)、[PureSequenceFilters](../YesMetaZFC/Model/ZFC/Pure/PureSequenceFilters.lean)、[PureSequenceStage](../YesMetaZFC/Model/ZFC/Pure/PureSequenceStage.lean) |
| `isNaturalNumber`、`isHereditarilyFinite`、`omegaPairLess`、`isCountablyInfinite`、`isUncountable`、`isCountable`、`isInfinite` | [PureNaturalRelations](../YesMetaZFC/Model/ZFC/Pure/PureNaturalRelations.lean)、[PureStageTwoSemantics](../YesMetaZFC/Model/ZFC/Pure/PureStageTwoSemantics.lean) |
| `naturalAddition`、`naturalMultiplication`、`naturalExponentiation`、`godelPairing` | [PureArithmeticRecurrence](../YesMetaZFC/Model/ZFC/Pure/PureArithmeticRecurrence.lean)、[PureOrdinalArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureOrdinalArithmetic.lean)、[PureArithmeticSpecifications](../YesMetaZFC/Model/ZFC/Pure/PureArithmeticSpecifications.lean) |
| `finiteHierarchy`、`finiteUniverse`、`transitiveClosure`、`naturalDifference` | [PureSetIterations](../YesMetaZFC/Model/ZFC/Pure/PureSetIterations.lean)、[PureTransitiveClosure](../YesMetaZFC/Model/ZFC/Pure/PureTransitiveClosure.lean)、[PureNaturalDifference](../YesMetaZFC/Model/ZFC/Pure/PureNaturalDifference.lean) |
| `naturalOrderType`、`naturalSubsetType` | [PureFiniteOrderTypes](../YesMetaZFC/Model/ZFC/Pure/PureFiniteOrderTypes.lean)、[PureNaturalOrderType](../YesMetaZFC/Model/ZFC/Pure/PureNaturalOrderType.lean)、[PureBoundedNaturalOrder](../YesMetaZFC/Model/ZFC/Pure/PureBoundedNaturalOrder.lean)、[PureNaturalSubsetType](../YesMetaZFC/Model/ZFC/Pure/PureNaturalSubsetType.lean) |
| `finiteSequenceConcatenation`、`finiteSequenceFlatten` | [PureFiniteSequenceCore](../YesMetaZFC/Model/ZFC/Pure/PureFiniteSequenceCore.lean)、[PureSequenceConcatenation](../YesMetaZFC/Model/ZFC/Pure/PureSequenceConcatenation.lean)、[PureFlattenRecursion](../YesMetaZFC/Model/ZFC/Pure/PureFlattenRecursion.lean)、[PureSequenceFlatten](../YesMetaZFC/Model/ZFC/Pure/PureSequenceFlatten.lean)；[PureRoundTwoStage](../YesMetaZFC/Model/ZFC/Pure/PureRoundTwoStage.lean) |
| `isTermCodeAt`、`isTermListCodeAt`、`isFormulaCodeAt` | [PureSyntaxOperator](../YesMetaZFC/Model/ZFC/Pure/PureSyntaxOperator.lean)、[PureSyntaxFixedPoint](../YesMetaZFC/Model/ZFC/Pure/PureSyntaxFixedPoint.lean) |
| `relatedNonlogicalSymbolSet`、`isStructure` | [PureStructureStage](../YesMetaZFC/Model/ZFC/Pure/PureStructureStage.lean) |
| `isRelatedTermCodeAt`、`isRelatedTermListCodeAt`、`isRelatedFormulaCodeAt` | [PureRelatedSyntaxOperator](../YesMetaZFC/Model/ZFC/Pure/PureRelatedSyntaxOperator.lean)、[PureRelatedSyntaxFixedPoint](../YesMetaZFC/Model/ZFC/Pure/PureRelatedSyntaxFixedPoint.lean) |
| `relatedTermSet`、`relatedFormulaSet`、`modusPonens` | [PureRelatedSyntaxSets](../YesMetaZFC/Model/ZFC/Pure/PureRelatedSyntaxSets.lean)、[PureRelatedStage](../YesMetaZFC/Model/ZFC/Pure/PureRelatedStage.lean) |
| `implicationDistributionAxiomSet`、`selfImplicationAxiomSet`、`weakeningAxiomSet`、`contradictionAxiomSet`、`classicalAxiomSet`、`explosionAxiomSet`、`caseAnalysisAxiomSet`、`quantifierDistributionAxiomSet`、`equalityReflexivityAxiomSet` | [PureLogicalSchemaSets](../YesMetaZFC/Model/ZFC/Pure/PureLogicalSchemaSets.lean)、[PureLogicalSchemaStage](../YesMetaZFC/Model/ZFC/Pure/PureLogicalSchemaStage.lean) |
| `specializationAxiomSet`、`vacuousQuantifierAxiomSet`、`equalitySubstitutionAxiomSet` | [PureDependentSchemaSets](../YesMetaZFC/Model/ZFC/Pure/PureDependentSchemaSets.lean)、[PureAllSchemaStage](../YesMetaZFC/Model/ZFC/Pure/PureAllSchemaStage.lean) |
| `syntaxTransform`、`freeVariableOccurs` | [PureTransformStage](../YesMetaZFC/Model/ZFC/Pure/PureTransformStage.lean) |
| `baseLogicalAxiomSet`、`logicalAxiomSet`、`isLogicalAxiomCode` | [PureLogicalClosure](../YesMetaZFC/Model/ZFC/Pure/PureLogicalClosure.lean)、[PureLogicalStage](../YesMetaZFC/Model/ZFC/Pure/PureLogicalStage.lean) |
| `termValue`、`termListValue` | [PureValueOperator](../YesMetaZFC/Model/ZFC/Pure/PureValueOperator.lean)、[PureValueFixedPoint](../YesMetaZFC/Model/ZFC/Pure/PureValueFixedPoint.lean)、[PureValueStage](../YesMetaZFC/Model/ZFC/Pure/PureValueStage.lean)；最终装配 [PureCompletedStage](../YesMetaZFC/Model/ZFC/Pure/PureCompletedStage.lean) |

## 使用边界

- 总图在 guard 外的取值属于所选扩张的定义，不能当作原理论约束非法输入的额外定理。
  早期阶段的空集／假默认分支也不能当作已实现符号。
- 反转 `reverseGraph` 对任意输入均交换两个总投影后组成有序对，原公理没有 guard。
  复合函数槽为 `second ∘ first`，用 `relationComposition_order` 接到执行顺序。
- 线序保留关系的载体限制；最小／最大元的关系方向保持当前规格。
  `minimumDifference` 使用源关系、源载体、两函数四参数；存在性使用原良序 guard，
  唯一性只需线序。自然序型关系分别是 `ε(candidate)`、`ε(subset)`。
  `omegaPairLess` 的正文翻译不自动给出标准配对良序性质。
- 自然数递推和分离在模型内部进行。`PureOmegaIteration` 的迭代合同不等于原
  `omegaRecursiveSequence` 所定义递归序列族之并的全域性定理。
- 有限展平使用携带族参数的历史算子：累积长度为族长度后继；末值有限性由
  最新解释上的 `accumulator_finite_values` 保证，不能混用旧阶段的默认函数值。
- 递归语法的所选最小不动点有唯一输出，不宣称原递归方程的任意解释唯一。
  related 递归必须保持符号集参数；求值递归必须保持载体、解释、符号集、赋值四参数。
  先证明 `parameters_preserved` / `condition_satisfaction`，再接入实际图。
- 公理模式成员条件使用存在见证，真正的 `logical_axiom_code_closed_condition`
  使用全称闭合；不回退为全称合取式成员条件。纯分离保留实际成员正文和原 guard，
  内部 ω 的数值界不能替代语法良构性。

## 独立数学待办

原递归序列族的定义和并集存在性已验证；**合法递归器下，该并集为 ω 上总函数**
仍需单独证明。这不阻塞当前裸 ZFC Rosser 实例。模型对应、句法方向和 Δ₀ 分类的
精确边界见 [UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md)。
