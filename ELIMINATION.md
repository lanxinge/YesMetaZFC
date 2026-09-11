# 纯 ZFC 定义基础设施指路表

范围是 `SupportAxiomBasis.intrinsic_proof.compact.axioms` 的 119 条有限基公理实际
使用的 **64 个函数、46 个关系**。这些符号均已有纯隶属定义；函数有任意裸 ZFC
模型、任意参数上的存在唯一性及合法输入规格，关系有原正文在具体扩张中的等价。
签名里没有被该基使用的符号不计入此覆盖范围。

统一解释为 [PureCompletedStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureCompletedStage.lean)；原支撑公理验证见 [PureSupportModels](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportModels.lean)，
裸 ZFC 模型扩张与原模型约化见 [PureZFCModels](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureZFCModels.lean)。指定 Rosser 的任意原模型对应和
独立性由 [PureRosserComplete](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) 给出，均不再是支撑消去待办。
纯句子的双向推导见 [PureSentenceTransfer](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSentenceTransfer.lean)；
原编码表示的纯语言可证明性、Löb 与哥二已落在 `PureModel.theory`，入口见 [TROPHIES.md](TROPHIES.md)。
[PureOpenTransfer](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureOpenTransfer.lean)
补齐任意有限参数下的环境往返和双向推导；`PureTarskiSource` 在同一裸理论中给出
保留源公式编码的带参数真不可定义性。`PureQuotation`／`PureFixedPoint`／`PureTarski`
另已完成最终纯公式自身编码的固定点及真不可定义性：只消元实际的自编码图，
最终纯 AST 的编码由结构等式单独核验。

## 集合构造与规格传输

| 需要的基础 | 接口与源码 | 使用条件 |
| --- | --- | --- |
| 复用 Project 模型库 | [Project/FirstOrderSemantics](YesMetaZFC/SetTheory/Definitional/Project/FirstOrderSemantics.lean) 的 `formula_correct`、`models_iff`；[PureModel](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureModel.lean) 的 `project_models`、`project_modelsZF` | 显式传入模型公理和解释；两套语法通过语义桥连接 |
| 纯模型上的有序对解释 | [PureKuratowskiProject](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureKuratowskiProject.lean) 的 `interpretation` | 复用实际 Kuratowski 图，不重新选择不相关的解释 |
| 纯公式分离与替换收集 | [PureSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSeparation.lean)、[PureReplacement](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureReplacement.lean) 的 `mapping_exists`、[PureProjectTemplate](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureProjectTemplate.lean) 的 `bounded_functional` | 明确总定义、唯一性、目标范围和实际自由闭合公式 |
| 跨阶段保持原规格 | [RelationalCongruence](YesMetaZFC/Automation/RelationalCongruence.lean) 的 `openFormula_congr`、[RelationalTransfer](YesMetaZFC/Automation/RelationalTransfer.lean) 的 `transfer_regraph` / `transfer_covered`、[ModelClosure](YesMetaZFC/Automation/ModelClosure.lean) | 翻译相等直接连接源与目标；覆盖只用于建立翻译相等，不加强任意正文传输的前提 |
| 覆盖保持链与函数规格 | [RelationalInheritance](YesMetaZFC/Automation/RelationalInheritance.lean) 的 `CoveredExtension`、`FunctionSpecification`、`specification_regraph` | 证书只保证原覆盖内的图；任意图等式仍可直接使用规格传输。规格合同保留全部参数，guard 由调用者原假设提供 |
| 连续阶段的实例 | [PureCollectionStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureCollectionStage.lean) 的 `specification_transfer`；[PureSequenceStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSequenceStage.lean) 的 `transfer_from_collection` | 只消费阶段已经实现的图和关系，不把临时默认值当作最终规格 |
| 内部归纳与递推唯一性 | [PureNaturalInduction](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNaturalInduction.lean) 的 `pure_induction`、`source_induction`、`omega_recurrence_ext`、`finite_recurrence_ext` | 性质必须由实际可分离公式表达；`source_induction` 固定早期 Difference 阶段 |
| 通用内部 ω 迭代 | [PureOmegaIteration](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureOmegaIteration.lean) 的 `functional`、`iterates_of_graph` | 后继算子由自由闭合 Project 二元 schema 表示且总唯一；模型参数显式保留 |
| 递归语法与求值图 | [PredicateExpansion](YesMetaZFC/Automation/PredicateExpansion.lean)、[PureLeastFixedPoint](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLeastFixedPoint.lean)、[PureSyntaxOperator](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSyntaxOperator.lean)、[PureValueOperator](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureValueOperator.lean) | 正出现、集合界、单调性和递归参数保持不可省略 |

## 符号到实现的导航

下表按数学用途分组，覆盖上述 110 个符号。源码中的 `RoundOne`、`RoundTwo`
等是现有模块名；它们在此作为接口位置使用，不表示待执行轮次。

| 符号 | 实际定义与规格入口 |
| --- | --- |
| `emptySet`、`unorderedPair`、`singleton`、`union`、`powerSet`、`successor` | [PureFunctionDefinitions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFunctionDefinitions.lean) 的 `functional` |
| `orderedPair`、`leftProjection`、`rightProjection`、`application` | [PureRelationFunctions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRelationFunctions.lean) |
| `membership`、`subset`、`isOrderedPair`、`isRelation`、`isFunction` | [PureRelationDefinitions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRelationDefinitions.lean)；隶属直接使用纯签名 |
| `cartesianProduct`、`mappingCollection`、`isMapping` | [PureMappingDefinitions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureMappingDefinitions.lean)、[PureMappingSpecifications](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureMappingSpecifications.lean) |
| `domain`、`range` | [PureRelationCoordinates](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRelationCoordinates.lean)、[PureCoordinateSpecifications](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureCoordinateSpecifications.lean) |
| `identity`、`restriction` | [PureMappingOperations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureMappingOperations.lean) |
| `binaryUnion`、`symmetricDifference`、`relationConverse`、`relationComposition`、`membershipRelation`、`image`、`inductiveCore` | [PureRelationSetOperations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRelationSetOperations.lean) 的 `functional` |
| `omega`、`orderedPairReverse` | [PureOmegaAndReverse](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureOmegaAndReverse.lean)、[PureRoundOneSpecifications](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRoundOneSpecifications.lean)、[PureStageSemantics](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureStageSemantics.lean) |
| `isEquivalenceRelation`、`isInjective`、`isSurjective`、`isBijection`、`isTransitiveSet` | [PureRoundOneRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRoundOneRelations.lean)、[PureRoundOneSpecifications](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRoundOneSpecifications.lean) |
| `isLinearOrder`、`isOrderIsomorphism`、`isOrderIsomorphic`、`isOrderEmbedding`、`isOrderEmbeddable`、`isNaturalDiscreteLinearOrder`、`isWellOrder` | [PureRoundOneRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRoundOneRelations.lean)、[PureOrderSemantics](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureOrderSemantics.lean) |
| `isFinite`、`isEquinumerous`、`cardinalityLeq`、`cardinalityStrictLess`、`isDedekindFinite`、`isInductiveSet`、`isUnboundedSubset`、`isBoundedSubset` | [PureRoundOneRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRoundOneRelations.lean) 的 `graph_equation`、`definition_correct`、`dependencies_covered`；[PureRoundOneSpecifications](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRoundOneSpecifications.lean) |
| `minimum`、`maximum` | [PureOrderExtrema](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureOrderExtrema.lean)、[PureStageTwoSemantics](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureStageTwoSemantics.lean) |
| `minimumDifference` | [PureMinimumDifference](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureMinimumDifference.lean) 的 `difference_exists`、`difference_set_exists`、`exists_of_guard`、`unique`；[PureDifferenceStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureDifferenceStage.lean) |
| `finiteSubsetCollection`、`powerSetBijection`、`indexOrder` | [PureBoundedDefinitions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureBoundedDefinitions.lean)、[PureCollectionStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureCollectionStage.lean) |
| `finiteSequenceSpace`、`nonemptyFiniteSequenceSpace`、`recursiveSequenceSpace`、`omegaRecursiveSequence` | [PureFiniteSequenceSpace](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFiniteSequenceSpace.lean)、[PureSequenceFilters](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSequenceFilters.lean)、[PureSequenceStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSequenceStage.lean) |
| `isNaturalNumber`、`isHereditarilyFinite`、`omegaPairLess`、`isCountablyInfinite`、`isUncountable`、`isCountable`、`isInfinite` | [PureNaturalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNaturalRelations.lean)、[PureStageTwoSemantics](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureStageTwoSemantics.lean) |
| `naturalAddition`、`naturalMultiplication`、`naturalExponentiation`、`godelPairing` | [PureArithmeticRecurrence](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureArithmeticRecurrence.lean)、[PureOrdinalArithmetic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureOrdinalArithmetic.lean)、[PureArithmeticSpecifications](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureArithmeticSpecifications.lean) |
| `finiteHierarchy`、`finiteUniverse`、`transitiveClosure`、`naturalDifference` | [PureSetIterations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSetIterations.lean)、[PureTransitiveClosure](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTransitiveClosure.lean)、[PureNaturalDifference](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNaturalDifference.lean) |
| `naturalOrderType`、`naturalSubsetType` | [PureFiniteOrderTypes](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFiniteOrderTypes.lean)、[PureNaturalOrderType](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNaturalOrderType.lean)、[PureBoundedNaturalOrder](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureBoundedNaturalOrder.lean)、[PureNaturalSubsetType](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNaturalSubsetType.lean) |
| `finiteSequenceConcatenation`、`finiteSequenceFlatten` | [PureFiniteSequenceCore](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFiniteSequenceCore.lean)、[PureSequenceConcatenation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSequenceConcatenation.lean)、[PureFlattenRecursion](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFlattenRecursion.lean)、[PureSequenceFlatten](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSequenceFlatten.lean)；[PureRoundTwoStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRoundTwoStage.lean) |
| `isTermCodeAt`、`isTermListCodeAt`、`isFormulaCodeAt` | [PureSyntaxOperator](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSyntaxOperator.lean)、[PureSyntaxFixedPoint](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSyntaxFixedPoint.lean) |
| `relatedNonlogicalSymbolSet`、`isStructure` | [PureStructureStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureStructureStage.lean) |
| `isRelatedTermCodeAt`、`isRelatedTermListCodeAt`、`isRelatedFormulaCodeAt` | [PureRelatedSyntaxOperator](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRelatedSyntaxOperator.lean)、[PureRelatedSyntaxFixedPoint](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRelatedSyntaxFixedPoint.lean) |
| `relatedTermSet`、`relatedFormulaSet`、`modusPonens` | [PureRelatedSyntaxSets](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRelatedSyntaxSets.lean)、[PureRelatedStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRelatedStage.lean) |
| `implicationDistributionAxiomSet`、`selfImplicationAxiomSet`、`weakeningAxiomSet`、`contradictionAxiomSet`、`classicalAxiomSet`、`explosionAxiomSet`、`caseAnalysisAxiomSet`、`quantifierDistributionAxiomSet`、`equalityReflexivityAxiomSet` | [PureLogicalSchemaSets](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLogicalSchemaSets.lean)、[PureLogicalSchemaStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLogicalSchemaStage.lean) |
| `specializationAxiomSet`、`vacuousQuantifierAxiomSet`、`equalitySubstitutionAxiomSet` | [PureDependentSchemaSets](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureDependentSchemaSets.lean)、[PureAllSchemaStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureAllSchemaStage.lean) |
| `syntaxTransform`、`freeVariableOccurs` | [PureTransformStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTransformStage.lean) |
| `baseLogicalAxiomSet`、`logicalAxiomSet`、`isLogicalAxiomCode` | [PureLogicalClosure](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLogicalClosure.lean)、[PureLogicalStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLogicalStage.lean) |
| `termValue`、`termListValue` | [PureValueOperator](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureValueOperator.lean)、[PureValueFixedPoint](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureValueFixedPoint.lean)、[PureValueStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureValueStage.lean)；最终装配 [PureCompletedStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureCompletedStage.lean) |

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
