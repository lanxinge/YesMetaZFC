# 公理验证与不完备性接口指路表

验证对象是原 `intrinsic_proof_theory`、`intrinsic_zfc_theory` 及纯语言中的
`PureModel.theory`。裸 ZFC 的 Rosser、原编码表示的 D1–D3、Löb 与哥二实例已完成；
独立性与哥二的不可证性接口保留裸 ZFC 一致性参数；
[原生小图模型](../YesMetaZFC/Model/SmallGraph/ZFC.lean) 的 `SmallGraph.zfc_consistent`
另在 Lean 元层通过实际模型给出该一致性证明。纯定义构造见 [ELIMINATION.md](ELIMINATION.md)，
证书与检查器见 [NAT_DECODING.md](NAT_DECODING.md)。
原支撑理论的无参数及任意有限参数 Tarski 真不可定义性也已完成；语义终点覆盖
任意原模型及每一组参数赋值。`PureTarskiSource` 另已给出保留源编码的裸 ZFC 版本；
其合同按源公式索引。`PureTarski` 现已完成只量化纯公式、使用最终纯公式自身编码的版本。

## 模型、公理与推导

| 要使用的结果 | 接口与源码 | 精确范围 |
| --- | --- | --- |
| 原生小图模型与裸 ZFC 一致性 | [SmallGraph/ZFC](../YesMetaZFC/Model/SmallGraph/ZFC.lean)：`sg_model`、`sg_project_zfc`、`sg_models_zfc`、`zfc_consistent` | 小图双模拟商直接构造；原公理及全部有限参数分离、收集模式已经核验，无模型存在或一致性前提；载体固定为 `Type (u+1)` |
| 有限基覆盖原支撑理论 | [FiniteAxiomModels](../YesMetaZFC/Model/ZFC/FiniteAxiomModels.lean) 中 `FiniteAxiomBasis.models_iff`；[ReducedAxioms](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedAxioms.lean) 的 `derives_iff` | 108 个具体闭句与 11 个参数分离模板，共 119 条；与原无限参数理论推导等价，不是公理集合相等 |
| 完整支撑模型 | [PureSupportModels](../YesMetaZFC/Model/ZFC/Pure/PureSupportModels.lean) 的 `support_models` | 同一规范扩张满足整个原支撑理论 |
| 原 ZFC 像及实际纯翻译 | [PureZFCModels](../YesMetaZFC/Model/ZFC/Pure/PureZFCModels.lean) 的 `models`、`translated_models` | 不弱化原公理或 guard |
| 模型扩张与约化 | [PureZFCModels](../YesMetaZFC/Model/ZFC/Pure/PureZFCModels.lean) 的 `expands`、`reduct_models`、`reduction` | 约化适用于任意原模型，不仅规范扩张 |
| 公平调度与正向推导传输 | [PureRosserSchedule](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserSchedule.lean) 的 `source`、`target`；[PureRosser](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosser.lean) 的 `translate_derives` | 使用 Henkin 强完备性传输源闭句推导；一般反向句法保守性不在此结论中 |
| 纯句子嵌入与双向推导 | [PureSentenceTransfer](../YesMetaZFC/Model/ZFC/Pure/PureSentenceTransfer.lean) 的 `embed_m`、`translate_embed_m`、`derives_iff_m` | 对任意纯句子成立；任意源句子的反向往返 `embed_translate_m` 仍须提供其实际 `Agreement` |
| 实际纯固定点 | [PureRosser](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosser.lean) 的 `sentence`、`comparison`、`fixed_point` | 当前源 Rosser 及源 quotation 的实际纯翻译，不是纯语言 quotation 上重新对角化 |
| 任意原模型上的句子对应 | [PureRosserComplete](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) 中 `PureRosser.agreement` | `Agreement` 已有证明；[PureRosser](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosser.lean) 的 `truth_iff` 只涉及规范扩张，不能单独代替它 |
| 裸 ZFC 双侧不可证性 | [PureRosserComplete](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) 中 `PureRosser.independent` | 仅由裸 ZFC 一致性推出当前句子及其否定均不可推导 |
| 裸 ZFC 的 Löb 与第二不完备 | [PureLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLoeb.lean)、[PureSecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSecondIncompleteness.lean) | 全部句子使用纯签名，理论为 `PureModel.theory`；可证明性使用纯嵌入后的原 quotation 和检查器 |

小图层新增的 38 个关键接口已审计。`sg_model` 仅依赖 `propext`；集合存在性及
一致性证明使用已有 `propext`、`Quot.sound`、`Classical.choice`。`zfc_consistent`
还继承原八条固定公理的 `sentence!` 自由闭合性 `native_decide` 依赖：外延、空集、配对、
并集、幂集、无穷、基础及选择各一处。没有新增公理常量、`sorryAx` 或原生验证依赖。
全库严格构建与全部 979 个独立模块通过；代码范围及载体边界见
[模型论指南](../YesMetaZFC/Model/README.md)。

## 任意原模型的内部证明码对应

下列接口连接任意原模型与其纯约化的规范重扩张。自然数指模型内部 ω，
允许非标准元素；局部规则比较同一候选集合轨迹，不对内部 ω 作外部归纳。

| 需要保持的内容 | 接口与源码 | 使用条件 |
| --- | --- | --- |
| 标准数码与 quotation | [PureSourceNumerals](../YesMetaZFC/Model/ZFC/Pure/PureSourceNumerals.lean) 的 `numeral_agrees`、`quotation_agrees`、`proof_numeral_agrees` | 只凭标准码结果不能推出全部内部自然数对应 |
| 当前证明码域 | [ReducedNaturalProofPresentation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedNaturalProofPresentation.lean) 的 `presentation`、`natural_of_satisfied` | `code ∈ ω` 包装保留检查器、标准码正负表示及完备性；旧后继码域见 [RosserDomainBoundary](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/RosserDomainBoundary.lean) |
| 同一内部 ω 及顺序 | [PureSourceInfinity](../YesMetaZFC/Model/ZFC/Pure/PureSourceInfinity.lean) 的 `omega_agrees`、`member_natural`、`natural_compare` | 来自原归纳定义与最小性，不添加标准性假设 |
| 合法映射与求值 | [PureSourceMappings](../YesMetaZFC/Model/ZFC/Pure/PureSourceMappings.lean) 的 `ordered_agrees`、`mapping_project`、`application_agrees` | 求值保持限于原定义域；不宣称非法输入总值对应或映射谓词无条件反向等价 |
| 内部加、乘、幂 | [PureSourceArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureSourceArithmetic.lean) 的 `addition_agrees`、`multiplication_agrees`、`exponentiation_agrees` | 使用实际有限递推图及内部唯一性，覆盖所有内部自然数输入 |
| 配数、字段与根编码 | [PureSourceCoding](../YesMetaZFC/Model/ZFC/Pure/PureSourceCoding.lean) 的 `pairing_agrees`、`fields_agrees`、`node_agrees`；[PureNaturalRosserAgreement](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNaturalRosserAgreement.lean) 的 `root_agrees` | 实际编码保持；根值不是待填前提 |
| 幂集界与集合轨迹 | [PureSourceBounds](../YesMetaZFC/Model/ZFC/Pure/PureSourceBounds.lean) 的 `power_agrees`、`trace_bound_agrees`、`trace_row_natural`；[PureNaturalRosserAgreement](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNaturalRosserAgreement.lean) 的 `proof_trace` | 保留实际 `P(ω)` 界和轨迹行的自然数证据 |
| 有界见证与局部规则 | [ObjectHornSemantics](../YesMetaZFC/Automation/ObjectHornSemantics.lean)；[PureSourceHorn](../YesMetaZFC/Model/ZFC/Pure/PureSourceHorn.lean) 的 `condition_agrees`、`localTest` | 递归前提读取同一候选集合；不假定其外部有限 |
| 自然数参数的公式组合 | [PureSourceFormula](../YesMetaZFC/Model/ZFC/Pure/PureSourceFormula.lean) 的 `instantiate`、`quantify` | 保留自然数环境、逐变量相等和实际见证界 |
| 公理检查 | [PureSourceSchemas](../YesMetaZFC/Model/ZFC/Pure/PureSourceSchemas.lean) 的 `axiomTest` | 固定公理表及分离、收集、替换模式的实际中间码连接 |
| 节点、行与完整证明图 | [PureSourceLocalTests](../YesMetaZFC/Model/ZFC/Pure/PureSourceLocalTests.lean) 的 `currentNode`、`currentRow`、`row_agrees`、`proof_agreement` | 任意固定结论、全部内部自然数证明码；提供 Rosser 所需的两项 ProofAgreement |
| 图对应推出句子对应 | [PureNaturalRosserAgreement](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNaturalRosserAgreement.lean) 的 `proof_agreement_of_rows`、`agreement_of_natural_proofs` | 局部行与两侧图对应均已有上述实际实例，最终由 `PureRosser.agreement` 装配 |

旧后继码域包含 ω 自身，不能由根项属于 ω 推断原输入属于 ω。
这一边界既不是 `Agreement` 的反例，也不是其不可证明性结论；当前自然数包装和
上表的内部对应已经完成实际实例。

## Δ₀ 的适用范围

| 结果 | 入口 | 边界 |
| --- | --- | --- |
| 支撑语言的 Δ₀ 等价代表 | [ReducedRosser](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedRosser.lean) 的 `predicate_delta0`、`delta0Sentence_delta0`、`delta0Sentence_independent` | 语言含 ω、幂集及编码函数；不自动成为纯隶属或一阶算术 Δ₀ |
| 无参数纯闭 Δ₀ 可决定 | [FunctionFreeDelta0](../YesMetaZFC/Automation/FunctionFreeDelta0.lean) 的 `closed_decided` | 纯 ℒ 只有二元 ∈，没有常元、函数或零元关系 |
| 当前纯闭句非 Δ₀ | [PureRosserDelta0](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `sentence_not_delta0`、`comparison_not_delta0` | 无条件的语法分类；不能再列为正向分类待办 |
| 排除闭 Δ₀ 等价代表 | [PureRosserDelta0](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `no_closed_delta0_equivalent` | 假定裸 ZFC 一致，排除可证明等价的无参数纯 Δ₀ 闭句 |
| 三参数纯 Δ₀ 矩阵 | [PureRosserDelta0](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `matrix_delta0`、`parameters_exists`、`parameters_unique`、`sentence_iff_matrix`、`representation_derives` | 参数为内部 ω 与两侧内部证明码集合；参数定义本身未分类为 Δ₀ |

矩阵为 $\delta(w,A,B)=\neg\exists p\in w\,(p\in A\land\forall q\in p\,q\notin B)$。
实际推导为 `ZFC ⊢ R ↔ ∃w,A,B (Def(w,A,B) ∧ δ(w,A,B))`；
`representation_not_delta0` 明确包含参数定义的整个存在闭句非 Δ₀。
这些参数通过纯分离得到，不意味着原证明谓词已获得纯 Δ₀ 定义；
`∃p∈ω` 也不能直接当作一阶算术的有界量词。

## 公理与证明索引

下表保持有限基原顺序。覆盖由 `FiniteAxiomBasis.models_iff` 和正式推导保证，
不由表格计数推断；项与项列求值的合取按原基计一条。

| 编号 | 原基公理或模板 | 验证定理 |
| --- | --- | --- |
| 1 | `(empty_predicate (free := [])).separation_axiom` | `PureSupportSeparation.separation_axiom (empty_predicate (free := []))`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 2 | `membership_relation_predicate.separation_axiom` | `PureSupportSeparation.separation_axiom membership_relation_predicate`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 3 | `Nonlogical.BasicSetTheory.infinity_axiom` | `PureFinalInfinity.infinity`；[PureFinalInfinity](../YesMetaZFC/Model/ZFC/Pure/PureFinalInfinity.lean) |
| 4 | `term_value_definition_axiom ∧ₘ term_list_value_definition_axiom` | `And.intro (PureFinalSyntax.term_value) (PureFinalSyntax.term_list_value)`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 5 | `binary_union_definition_axiom` | `PureFinalBasic.binary_union`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 6 | `bounded_subset_definition_axiom` | `PureFinalRelations.bounded_subset`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 7 | `cardinality_leq_definition_axiom` | `PureFinalRelations.cardinality_leq`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 8 | `cardinality_strict_less_definition_axiom` | `PureFinalRelations.cardinality_strict_less`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 9 | `cartesian_product_definition_axiom` | `PureFinalCollections.cartesian_product`；[PureFinalCollections](../YesMetaZFC/Model/ZFC/Pure/PureFinalCollections.lean) |
| 10 | `domain_definition_axiom` | `PureFinalMappings.domain`；[PureFinalMappings](../YesMetaZFC/Model/ZFC/Pure/PureFinalMappings.lean) |
| 11 | `empty_set_definition_axiom` | `PureFinalBasic.empty_set`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 12 | `equality_axiom_schema_definition_axiom` | `(PureFinalSyntax.schema_axioms).2.2`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 13 | `extensionality_axiom` | `PureFinalBasic.extensionality_axiom`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 14 | `finite_hierarchy_definition_axiom` | `PureFinalConstructions.finite_hierarchy`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 15 | `finite_sequence_concatenation_definition_axiom` | `PureFinalConstructions.finite_sequence_concatenation`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 16 | `finite_sequence_flatten_definition_axiom` | `PureFinalConstructions.finite_sequence_flatten`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 17 | `finite_sequence_space_definition_axiom` | `PureFinalConstructions.finite_sequence_space`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 18 | `finite_subset_collection_definition_axiom` | `PureFinalConstructions.finite_subset_collection`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 19 | `finite_subset_collection_separation_axiom` | `PureFinalSeparation.finite_subset_collection`；[PureFinalSeparation](../YesMetaZFC/Model/ZFC/Pure/PureFinalSeparation.lean) |
| 20 | `finite_universe_definition_axiom` | `PureFinalConstructions.finite_universe`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 21 | `free_variable_occurs_definition_axiom` | `PureFinalSyntax.free_variable_occurs`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 22 | `function_application_definition_axiom` | `PureFinalMappings.application`；[PureFinalMappings](../YesMetaZFC/Model/ZFC/Pure/PureFinalMappings.lean) |
| 23 | `godel_pairing_definition_axiom` | `PureFinalConstructions.godel_pairing`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 24 | `hereditarily_finite_definition_axiom` | `PureFinalRelations.hereditarily_finite`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 25 | `identity_definition_axiom` | `PureFinalCollections.identity`；[PureFinalCollections](../YesMetaZFC/Model/ZFC/Pure/PureFinalCollections.lean) |
| 26 | `image_definition_axiom` | `PureFinalOperations.image`；[PureFinalOperations](../YesMetaZFC/Model/ZFC/Pure/PureFinalOperations.lean) |
| 27 | `index_order_definition_axiom` | `PureFinalConstructions.index_order`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 28 | `inductive_core_definition_axiom` | `PureFinalInfinity.inductive_core`；[PureFinalInfinity](../YesMetaZFC/Model/ZFC/Pure/PureFinalInfinity.lean) |
| 29 | `is_bijection_definition_axiom` | `PureFinalRelations.is_bijection`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 30 | `is_countable_definition_axiom` | `PureFinalRelations.is_countable`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 31 | `is_countably_infinite_definition_axiom` | `PureFinalRelations.is_countably_infinite`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 32 | `is_dedekind_finite_definition_axiom` | `PureFinalRelations.is_dedekind_finite`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 33 | `is_equinumerous_definition_axiom` | `PureFinalRelations.is_equinumerous`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 34 | `is_equivalence_relation_definition_axiom` | `PureFinalRelations.is_equivalence_relation`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 35 | `is_finite_definition_axiom` | `PureFinalRelations.is_finite`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 36 | `is_function_definition_axiom` | `PureFinalMappings.is_function`；[PureFinalMappings](../YesMetaZFC/Model/ZFC/Pure/PureFinalMappings.lean) |
| 37 | `is_inductive_set_definition_axiom` | `PureFinalRelations.is_inductive_set`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 38 | `is_infinite_definition_axiom` | `PureFinalRelations.is_infinite`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 39 | `is_injective_definition_axiom` | `PureFinalRelations.is_injective`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 40 | `is_linear_order_definition_axiom` | `PureFinalRelations.is_linear_order`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 41 | `is_mapping_definition_axiom` | `PureFinalMappings.is_mapping`；[PureFinalMappings](../YesMetaZFC/Model/ZFC/Pure/PureFinalMappings.lean) |
| 42 | `is_natural_discrete_linear_order_definition_axiom` | `PureFinalRelations.is_natural_discrete_linear_order`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 43 | `is_order_embeddable_definition_axiom` | `PureFinalRelations.is_order_embeddable`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 44 | `is_order_embedding_definition_axiom` | `PureFinalRelations.is_order_embedding`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 45 | `is_order_isomorphic_definition_axiom` | `PureFinalRelations.is_order_isomorphic`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 46 | `is_order_isomorphism_definition_axiom` | `PureFinalRelations.is_order_isomorphism`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 47 | `is_ordered_pair_definition_axiom` | `PureFinalPairs.is_ordered_pair`；[PureFinalPairs](../YesMetaZFC/Model/ZFC/Pure/PureFinalPairs.lean) |
| 48 | `is_relation_definition_axiom` | `PureFinalPairs.is_relation`；[PureFinalPairs](../YesMetaZFC/Model/ZFC/Pure/PureFinalPairs.lean) |
| 49 | `is_surjective_definition_axiom` | `PureFinalRelations.is_surjective`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 50 | `is_transitive_set_definition_axiom` | `PureFinalRelations.is_transitive_set`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 51 | `is_uncountable_definition_axiom` | `PureFinalRelations.is_uncountable`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 52 | `left_projection_definition_axiom` | `PureFinalPairs.left_projection`；[PureFinalPairs](../YesMetaZFC/Model/ZFC/Pure/PureFinalPairs.lean) |
| 53 | `logical_axiom_code_definition_axiom` | `PureFinalSyntax.logical_axioms`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 54 | `mapping_collection_definition_axiom` | `PureFinalCollections.mapping_collection`；[PureFinalCollections](../YesMetaZFC/Model/ZFC/Pure/PureFinalCollections.lean) |
| 55 | `maximum_natural_order_definition_axiom` | `PureFinalExtrema.maximum_natural_order`；[PureFinalExtrema](../YesMetaZFC/Model/ZFC/Pure/PureFinalExtrema.lean) |
| 56 | `membership_irreflexive_axiom` | `PureFinalBasic.irreflexivity`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 57 | `membership_relation_definition_axiom` | `PureFinalOperations.membership_relation`；[PureFinalOperations](../YesMetaZFC/Model/ZFC/Pure/PureFinalOperations.lean) |
| 58 | `minimum_difference_definition_axiom` | `PureFinalConstructions.minimum_difference`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 59 | `minimum_linear_order_definition_axiom` | `PureFinalExtrema.minimum_linear_order`；[PureFinalExtrema](../YesMetaZFC/Model/ZFC/Pure/PureFinalExtrema.lean) |
| 60 | `minimum_natural_order_definition_axiom` | `PureFinalExtrema.minimum_natural_order`；[PureFinalExtrema](../YesMetaZFC/Model/ZFC/Pure/PureFinalExtrema.lean) |
| 61 | `modus_ponens_definition_axiom` | `PureFinalSyntax.modus_ponens`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 62 | `natural_addition_definition_axiom` | `PureFinalConstructions.natural_addition`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 63 | `natural_addition_upper_bound_axiom` | `PureFinalArithmetic.addition_upper_axiom`；[PureFinalArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureFinalArithmetic.lean) |
| 64 | `natural_difference_definition_axiom` | `PureFinalConstructions.natural_difference`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 65 | `natural_exponent_product_index_bound_axiom` | `PureFinalArithmetic.exponent_product_axiom`；[PureFinalArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureFinalArithmetic.lean) |
| 66 | `natural_exponentiation_definition_axiom` | `PureFinalConstructions.natural_exponentiation`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 67 | `natural_exponentiation_index_bound_axiom` | `PureFinalArithmetic.exponent_axiom`；[PureFinalArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureFinalArithmetic.lean) |
| 68 | `natural_godel_pairing_coordinate_bound_axiom` | `PureFinalArithmetic.pairing_axiom`；[PureFinalArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureFinalArithmetic.lean) |
| 69 | `natural_le_lt_transitivity_axiom` | `PureFinalArithmetic.transitivity_axiom`；[PureFinalArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureFinalArithmetic.lean) |
| 70 | `natural_multiplication_definition_axiom` | `PureFinalConstructions.natural_multiplication`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 71 | `natural_order_type_definition_axiom` | `PureFinalConstructions.natural_order_type`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 72 | `natural_positive_left_addition_strict_bound_axiom` | `PureFinalArithmetic.positive_addition_axiom`；[PureFinalArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureFinalArithmetic.lean) |
| 73 | `natural_subset_type_definition_axiom` | `PureFinalConstructions.natural_subset_type`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 74 | `nonempty_finite_sequence_space_definition_axiom` | `PureFinalConstructions.nonempty_finite_sequence_space`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 75 | `nonempty_finite_sequence_space_separation_axiom` | `PureFinalSeparation.nonempty_sequence_space`；[PureFinalSeparation](../YesMetaZFC/Model/ZFC/Pure/PureFinalSeparation.lean) |
| 76 | `omega_definition_axiom` | `PureFinalInfinity.omega`；[PureFinalInfinity](../YesMetaZFC/Model/ZFC/Pure/PureFinalInfinity.lean) |
| 77 | `omega_pair_less_definition_axiom` | `PureFinalRelations.omega_pair_less`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 78 | `omega_recursive_sequence_definition_axiom` | `PureFinalConstructions.omega_recursive_sequence`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 79 | `ordered_pair_definition_axiom` | `PureFinalPairs.ordered_pair`；[PureFinalPairs](../YesMetaZFC/Model/ZFC/Pure/PureFinalPairs.lean) |
| 80 | `ordered_pair_reverse_definition_axiom` | `PureFinalPairs.reverse`；[PureFinalPairs](../YesMetaZFC/Model/ZFC/Pure/PureFinalPairs.lean) |
| 81 | `pair_definition_axiom` | `PureFinalBasic.pairing`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 82 | `pairing_axiom` | `PureFinalBasic.pairing_exists`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 83 | `power_set_axiom` | `PureFinalBasic.power_exists_axiom`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 84 | `power_set_bijection_definition_axiom` | `PureFinalConstructions.power_set_bijection`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 85 | `power_set_definition_axiom` | `PureFinalBasic.power_definition`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 86 | `propositional_axiom_schema_definition_axiom` | `(PureFinalSyntax.schema_axioms).1`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 87 | `quantifier_axiom_schema_definition_axiom` | `(PureFinalSyntax.schema_axioms).2.1`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 88 | `range_definition_axiom` | `PureFinalMappings.range`；[PureFinalMappings](../YesMetaZFC/Model/ZFC/Pure/PureFinalMappings.lean) |
| 89 | `recursive_sequence_space_definition_axiom` | `PureFinalConstructions.recursive_sequence_space`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 90 | `related_nonlogical_symbol_set_definition_axiom` | `PureFinalSyntax.nonlogical_symbols`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 91 | `related_syntax_definition_axiom` | `PureFinalSyntax.related_syntax`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 92 | `relation_composition_definition_axiom` | `PureFinalOperations.composition`；[PureFinalOperations](../YesMetaZFC/Model/ZFC/Pure/PureFinalOperations.lean) |
| 93 | `relation_converse_definition_axiom` | `PureFinalOperations.converse`；[PureFinalOperations](../YesMetaZFC/Model/ZFC/Pure/PureFinalOperations.lean) |
| 94 | `relation_image_separation_axiom` | `PureFinalSeparation.relation_image`；[PureFinalSeparation](../YesMetaZFC/Model/ZFC/Pure/PureFinalSeparation.lean) |
| 95 | `restriction_definition_axiom` | `PureFinalCollections.restriction`；[PureFinalCollections](../YesMetaZFC/Model/ZFC/Pure/PureFinalCollections.lean) |
| 96 | `right_projection_definition_axiom` | `PureFinalPairs.right_projection`；[PureFinalPairs](../YesMetaZFC/Model/ZFC/Pure/PureFinalPairs.lean) |
| 97 | `singleton_definition_axiom` | `PureFinalBasic.singleton`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 98 | `structural_syntax_definition_axiom` | `PureFinalSyntax.structural_syntax`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 99 | `structure_definition_axiom` | `PureFinalSyntax.structure_axiom`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 100 | `subset_definition_axiom` | `PureFinalBasic.subset`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 101 | `successor_definition_axiom` | `PureFinalBasic.successor`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 102 | `symmetric_difference_definition_axiom` | `PureFinalOperations.symmetric_difference`；[PureFinalOperations](../YesMetaZFC/Model/ZFC/Pure/PureFinalOperations.lean) |
| 103 | `syntax_transform_definition_axiom` | `PureFinalSyntax.syntax_transform`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 104 | `transitive_closure_definition_axiom` | `PureFinalConstructions.transitive_closure`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 105 | `unbounded_subset_definition_axiom` | `PureFinalRelations.unbounded_subset`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 106 | `union_axiom` | `PureFinalBasic.union_exists_axiom`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 107 | `union_definition_axiom` | `PureFinalBasic.union_definition`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 108 | `well_order_definition_axiom` | `PureFinalRelations.well_order`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 109 | `SupportAssembly.closedTemplate .cartesianProduct` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 110 | `SupportAssembly.closedTemplate .composition` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 111 | `SupportAssembly.closedTemplate .converse` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 112 | `SupportAssembly.closedTemplate .domain` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 113 | `SupportAssembly.closedTemplate .identity` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 114 | `SupportAssembly.closedTemplate .indexOrder` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 115 | `SupportAssembly.closedTemplate .inductiveCore` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 116 | `SupportAssembly.closedTemplate .mappingCollection` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 117 | `SupportAssembly.closedTemplate .powerSetBijection` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 118 | `SupportAssembly.closedTemplate .range` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 119 | `SupportAssembly.closedTemplate .symmetricDifference` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |

## 可导性、内部反射与不完备性核验

在既有 D1、D2 接口之上，已完成
内部数码总性与唯一性、固定 AST 的非标准自由代入、模式 2 点实例化连接、
任意内部上下文下的数码语法，以及内部结论码上的节点装配、MP 和数码存在引入。
现已补上任意有限参数定理的非标准数码特化、自然数 guard 反射、零测试
正负反射、任意两个内部自然数的数码相等／不等与严格／非严格序反射，
以及加、乘、幂、Gödel 配对与复合编码项的数码求值。
编码项入口覆盖字段列、节点、Horn 表达式、参数化 AST 码项和既定 quotation。
原子判断及命题联结词的正负反射已完成；自然数有界全称／存在也有正负反射，
界可为已求值的复合项。固定有限轨迹骨架的逐行内部证明可经 `finite_verification`
接回原验证矩阵。数码递归图已完成任意内部轨迹的正负反射，并接入复合项；
投影图也完成了全部七条规则的内部正反射；一般语法图的项、参数列和全部公式
构造子已完成内部正反射。原四种语法变换、schema 各递归图、传输包解码以及
完整 schema／公理行查询现已完成正反射。原 27 类逻辑公理、6 类证明节点、
实际局部行查询也已完成正反射，并接入原检查步骤。完整 checked 轨迹的任意内部
根行反射现已完成，原验证矩阵与完整证明矩阵均已反射。
公共入口为 [InternalNumeralProof](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralProof.lean)
和 [ReducedProofReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofReflection.lean)。
`InternalNumeralReflection.natural`、`natural_derives`、`zero`、`nonzero` 均已证明，
`equal`、`unequal`、`unequal_derives`、`order`、`weak_order`、`order_derives`
及 `arithmetic_evaluation_derives` 也已证明，没有相应反射前提。
`ReducedProvability.matrix_of_verification` 用自然数反射补齐
原矩阵的 guard；`verification_reflection` 填入原检查器正文反射，
`ReducedProvability.introspection` 已给出无附加反射假设的 D3 普通推导。
归纳消费最终解释的纯公式，未假定内部自然数或轨迹在外部标准、有限或良基。

当前源码包含原理论及裸 ZFC 的 Löb、第二不完备定理，原支撑理论的 Tarski 实例，
以及保留源编码和最终纯公式自身编码的裸 ZFC 带参数 Tarski 实例。
`lake --wfail build` 完成 947 个任务。
`bash scripts/check-all.sh` 检查全部 950 个 Lean 模块，完成 952 个全源构建任务及
320 个扫描工具任务，零错误、零警告。
这些核验在恢复环境中实际运行；没有运行远端 CI。

最新 `#print axioms` 检查覆盖 530 个入口，包括 D1–D3、Löb、哥二、Rosser、原理论及纯语言表示的 Tarski 终点。
上一状态的 440 个入口依赖集合逐项不变；90 个新增核验入口覆盖通用语义外壳、表达式迭代、
最小输出、纯 AST 编解码、数码求值、自身编码图、固定点及纯 Tarski。
全部新增依赖均未超出保存的 Rosser 32 项可信基，没有新可信依赖或 `sorryAx`：

| 核验入口 | 依赖数量及比较 |
| --- | --- |
| `DerivabilityConditions_m.imp_m`、`iff_m` | 各 0 项 |
| `DerivabilityConditions_m.loeb_axiom_m`、`loeb_m` | 各 1 项，仅 `propext` |
| `ObjectLoeb.reflection_apply_m`、`fixed_point_m` | 分别为 2 项、3 项，仅既有 Lean 基础依赖 |
| `ReducedProvability.loeb_fixed_point_m` | 11 项，包含于既有 Rosser 可信基 |
| `ReducedProvability.derivability_m`、`loeb_axiom_m`、`loeb_m` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `DerivabilityConditions_m.second_incompleteness_internal_m`、`second_incompleteness_m` | 各 1 项，仅 `propext` |
| `ReducedProvability.second_incompleteness_internal_m`、`second_incompleteness_m` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `PureSentenceTransfer.translate_embed_m`、`derives_iff_m` | 各 31 项，均包含于既有 Rosser 可信基 |
| `PureProvability.checked_iff_m`、`source_canonical_m`、`source_roundtrip_m` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `PureProvability.necessitation_m`、`distribution_m`、`introspection_m`、`derivability_m` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `PureProvability.loeb_fixed_point_m`、`loeb_axiom_m`、`loeb_m` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `PureProvability.consistency_translation_m` | 11 项，包含于既有 Rosser 可信基 |
| `PureProvability.second_incompleteness_internal_m`、`second_incompleteness_m` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `Tarski.liar_refutes_m`、`biconditional_unprovable_m`、`not_truth_schema_m` | 各 1 项，仅 `propext` |
| `Tarski.not_defines_truth_m`、`ObjectTarski.liar_fixed_point_m` | 各 3 项，仅既有 Lean 基础依赖 |
| `ReducedTarski.liar_fixed_point_m`、`liar_refutes_m`、`biconditional_unprovable_m` | 各 10 项，均包含于既有 Rosser 可信基 |
| `ReducedTarski.undefinable_syntax_m`、`undefinable_semantics_m` | 各 10 项，均包含于既有 Rosser 可信基 |
| `ObjectNumeralSyntax.value_encode_m` | 0 项 |
| `ObjectParameterDiagonal.fixed_point_m`、`ObjectTarski.Parameters.liar_fixed_point_m` | 各 3 项，仅既有 Lean 基础依赖 |
| `Tarski.not_defines_satisfaction_m` | 3 项，仅既有 Lean 基础依赖 |
| `ReducedTarski.Parameters.liar_fixed_point_m`、`liar_refutes_closed_m`、`liar_fails_at_m` | 各 10 项，均包含于既有 Rosser 可信基 |
| `ReducedTarski.Parameters.undefinable_syntax_m`、`undefinable_at_m`、`undefinable_parameters_m` | 各 10 项，均包含于既有 Rosser 可信基 |
| `SemanticTransfer.derives_open_m`、`consistent_open_m` | 各 3 项，仅既有 Lean 基础依赖 |
| `PureOpenTransfer.embed_canonical_m`、`translate_embed_m`、`derives_iff_m` | 各 31 项，均包含于既有 Rosser 可信基 |
| `PureTarskiSource.predicate_satisfies_m`、`liar_fixed_point_m`、`liar_refutes_closed_m` | 各 31 项，均包含于既有 Rosser 可信基 |
| `PureTarskiSource.undefinable_syntax_m`、`undefinable_at_m`、`undefinable_parameters_m`、`undefinable_source_at_m` | 各 31 项，均包含于既有 Rosser 可信基 |
| `PureQuotation.self_code_m`、`code_injective_m`、`decode_tree_m` | 各 3 项，仅既有 Lean 基础依赖 |
| `PureDiagonalGraph.source_satisfies_m` | 10 项，均包含于既有 Rosser 可信基 |
| `PureQuotation.numeral_satisfies_m`、`PureDiagonalGraph.satisfies_m`、`PureFixedPoint.fixed_point_m` | 各 31 项，均包含于既有 Rosser 可信基 |
| `PureTarski.liar_fixed_point_m`、`liar_refutes_closed_m`、`undefinable_syntax_m`、`undefinable_parameters_m` | 各 31 项，均包含于既有 Rosser 可信基 |
| `ObjectCodeInstantiation.formula_values_congr` | 1 项，为既有 Rosser 32 项依赖的子集 |
| `PureSourceTraceComposition.witness_agrees`；`PureSourceNumeralSyntax.graph_transform` | 各 31 项，均包含于同一既有可信基 |
| `PureSourceInstantiation.formula_mapped_transform`、`numeral_point`、`numeral_wellFormed` | 各 31 项，均包含于同一既有可信基 |
| `InternalNumeralProof.forall_elimination`、`specialize_values`、`specialize_finite`、`specialize`、`values_modus_ponens` | 各 32 项，与此前 Rosser 依赖集合相同 |
| `InternalNumeralReflection.equal`、`successor_inequality`、`unequalAll_agrees`、`unequal`、`unequal_derives` | 各 32 项，与此前 Rosser 依赖集合相同 |
| `InternalNumeralReflection.natural`；`ReducedProvability.matrix_of_verification` | 重新核验后仍为同一组 32 项依赖；后者仍须提供检查器正文证明 |
| `ReducedProvability.distribution`、`PureRosser.independent` | 重新核验后仍为同一组 32 项依赖 |
| `PureSourceArithmetic.at_zero`、`at_successor`；`InternalNumeralReflection.source_complete` | 前两项各 31 项，开放完备性入口 10 项，均为既有可信基的子集 |
| `InternalNumeralReflection.orderAll_agrees`、`order`、`weak_order`、`order_derives` | 各 32 项，与此前 Rosser 依赖集合相同 |
| `InternalNumeralReflection.evaluationAll_agrees`、`evaluation_induction`、`evaluation_zero`、`evaluation_successor` | 各 32 项，与此前 Rosser 依赖集合相同 |
| `InternalNumeralReflection.addition_evaluation`、`multiplication_evaluation`、`exponentiation_evaluation`、`arithmetic_evaluation_derives` | 各 32 项，与此前 Rosser 依赖集合相同 |
| `ObjectCodeInstantiation.term_mapped`、`term_weakenFree`；`InternalNumeralReflection.composition_derives` | 分别为 0、1、10 项，均包含于既有可信基 |
| `InternalNumeralReflection.binary_term_evaluation`、`arithmetic_term_evaluation`；配对多项式求值、`pairing_evaluation`、`pairing_evaluation_derives` | 各 32 项，与此前 Rosser 依赖集合相同 |
| 字段列、节点、Horn 表达式、参数化项／参数列／公式、quotation 树与 `quotation_evaluation` | 八个入口各 32 项，与此前 Rosser 依赖集合相同 |
| `ObjectCodeInstantiation.term_weakenBound`、`formula_renamed`、`formula_weakenFree` | 分别为 1、2、2 项，均包含于既有可信基 |
| 原子同余、全称零点／后继／反例的源推导 | 四个入口各 10 项；内部原子反射、逻辑组合、量词见证及实际有界反射均为原 32 项依赖 |
| `bounded_bundle_parameters`、`bounded_bundle`、`bundleAt_agrees` | 各 32 项；`parameterValues_agrees` 为 31 项，均包含于既有可信基 |
| `finite_trace_derives`、`verificationMatrix_trace` | 分别为 9、11 项，均包含于既有可信基 |
| `allOf_values`、`natural_term_proof`、`finite_trace_values`、`checked_trace_values`、`finite_verification` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `term_embedBoundClosed`；`formula_mapped_of_depth`、`formula_substituteFree`、`binary_template` | 前者 1 项，其余各 2 项；自由重命名改为复用该遍历后，旧入口依赖集合不变 |
| 数码图 `template_apply`；`predicate_terms_code`、`predicate_names_code` | 各 2 项，均包含于既有可信基 |
| `predicate_transport_derives`；`predicate_transport`、`nextTerm_evaluation` | 分别为 10、32、32 项，均包含于既有可信基 |
| `numeral_trace_zero_derives`、`numeral_trace_step_derives`、`numeral_trace_reject_derives` | 各 31 项，均包含于既有可信基 |
| `numeral_trace_zero`、`numeral_trace_step`、`numeralTraceAt_agrees`、`numeral_trace_positive`、`numeral_trace_positive_derives`、`numeral_trace_negative`、`numeral_trace_reflection` | 七个入口各 32 项，与既有 Rosser 依赖集合相同 |
| Horn `template_apply`、`horn_satisfies`；`hornAt_satisfies`、`projectionGet_satisfies` | 前两项各 2 项，后两项各 11 项，均包含于既有可信基 |
| `rule_cases`、`node_head_injective`、`horn_rule_derives` | 各 31 项，均包含于既有可信基 |
| `horn_term_transfer`、`horn_rule_terms`、`horn_rule_values`、`hornProv_agrees` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `projectionGet_agrees`、`projection_get_step`、`projection_get_positive`、`projection_positive`、`projection_term_positive`、`projection_positive_derives` | 六个入口各 32 项，与既有 Rosser 依赖集合相同 |
| `ObjectSyntaxReflection.Row.map_tag`、`map_fields`、`map_input`；`PureSourceSyntaxRank.value_map` | 四个入口均为 0 项依赖 |
| `ObjectSyntaxReflection.Row.input_mem`、`PureSourceSyntaxRank.input_natural` | 各 1 项，均包含于既有可信基 |
| `ObjectSyntaxReflection.ranked`、`head_variables` | 各 2 项，纯规则形状及变量出现证明 |
| `PureSourceSyntaxRank.value_natural`、`map_natural` | 各 10 项，均包含于既有可信基 |
| `PureSourceInduction.strong_induction`；`PureSourceSyntaxRank.rank_unique`、`below_value`、`rule_ranked` | 四个入口各 31 项，均包含于既有可信基 |
| `syntaxAt_satisfies` | 11 项，实际同时归纳公式的语义接口 |
| `syntaxAt_agrees`、`syntax_step`、`syntax_at_positive`、`syntax_positive`、`syntax_term_positive`、`syntax_positive_derives` | 六个入口各 32 项，与既有 Rosser 依赖集合相同 |
| 分层规则 `transform_valid`、`iteration_valid`、`project_valid`；schema 三项 `*_valid` 和 packet `shapes` | 各 2 项，由内核核验原固定规则表 |
| `rule_intro_bounds`、`rule_cases_bounds`；`affine_bounds` | 分别为 10、31、31 项，均包含于既有可信基 |
| `rankedAt_satisfies`；`rankedAt_agrees`、`horn_ranked_positive`、`horn_valid_positive` | 语义接口为 11 项，其余各 32 项，均包含于既有可信基 |
| `transform_positive_derives`；`InternalPositiveFormula.boundedExists`、`positive_derives` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `axiom_query_positive`、`axiom_query_named`、`axiom_query_positive_derives` | 各 32 项，实际一元公理行查询的内部与普通推导终点 |
| `InternalPositiveFormula.localMatrix`、`localRule`、`localTest` | 三个公共局部规则组合入口，各 32 项 |
| `InternalProofQueryReflection.logical`、`query`、`node`、`row`、`currentNode`、`currentRow` | 六个原局部查询反射入口，各 32 项 |
| `logical_term_positive`、`node_term_positive`、`row_term_positive`、`row_named_positive` 及三项 `*_positive_derives` | 七个复合项、数码及普通推导终点，各 32 项 |
| `checked_step_values`、`proof_step_values`、`finite_verification_of_links` | 三个实际步骤／矩阵装配入口，各 32 项；仍显式保留连边证明输入 |

| checked `template_apply`、`proof_valid`、`step_satisfies`、`checked_satisfies` | 四个入口各 2 项，由原公式语义及内核规则核验给出 |
| checked `rule_cases_bounds`、`checked_step_agrees` | 各 31 项，均包含于既有可信基 |
| checked `rule_intro_bounds`、`checked_rule_bounded_derives` | 各 10 项，内部集合构造及源规则推导 |
| `checkedAt_satisfies`、`checkedRankedAt_satisfies` | 各 11 项，原反射公式的语义接口 |
| `checked_term_transfer`、`checked_rule_bounded_terms`、`checked_rule_bounded_values`、`checkedProv_agrees`、`checkedRankedAt_agrees`、`checked_valid_positive` | 六个入口各 32 项，与既有 Rosser 依赖集合相同 |
| `proof_trace_positive`、`proof_trace_values`、`proofTrace`、`proof_trace_positive_derives` | 四个任意内部原证明树轨迹终点，各 32 项 |
| `verificationRoot_evaluation`、`verification_reflection`、`proof_matrix_reflection`、`ReducedProvability.introspection` | 四个原矩阵／D3 终点，各 32 项；无新增可信依赖 |


此前数码、节点装配、模式 2 变换与逻辑公理入口的审计也未超出上述可信基。
新增源码无 `sorry`、`admit`、自定义公理或原生验证调用；这里保留原有原生
支撑依赖，不声称整个仓库没有原生依赖。

数码的 `graph_term` 使用带 bound/free 参数的实际对象公式归纳，旧闭项接口
作为零上下文特例保留。自由代入和点实例化共用 `formula_mapped_transform` 的
AST 遍历；公式语法构造统一于 `PureSourceFormulaConstruction`，逻辑层复用它。
`InternalNumeralProof.exists_introduction` 只消费数码图和实例内部证明，自动填入
正文、项、实例语法及实际模式 2 变换。`codeProof_agreement` 还将最终阶段对应
推广到非标准结论码。新增 `ObjectNumeralReflection.atNumber` 由实际数码图、
参数化 AST 码项和原可证明性图组成，归纳前已证明其与最终规范扩张逐值一致。
自然数反射的后继步骤使用源无穷公理定理的内部特化及 MP，零测试的负分支
只反演数码图的根行。AST 的自然性、求值与模型传输复用关系保持遍历。
变换遍历现在允许两端都含内部数码，自由槽位相等只须覆盖实际上下文。
`graph_transform` 对任意内部深度证明数码不变，`specialize_values` 以同一全称
消去构造递归消费有限自由上下文；`specialize_finite` 不约束上下文外的槽位。
二元不等反射的归纳性质是 `ObjectNumeralComparison.unequalAll`，全称覆盖
第二个内部自然数和两个数码，零与后继分支均构造实际证明码。
序关系的归纳性质为 `ObjectNumeralOrder.atRight`，后继使用隶属后继的析取刻画。
算术的 `ObjectNumeralEvaluation.atRight` 同时量化两个操作数及运算结果的数码，
`evaluationAll_agrees` 先验证自然数封闭性与最终阶段对应，再用 `evaluation_induction`。
加法、乘法、幂依次提供实际后继证明；源递推由既有纯序数算术规格传回。
受限数码量词和联结词语义共用 `ObjectNumeralQuantifiers`／`InternalNumeralQuantifiers`，
避免展开整个验证器；所有数码实例仍交给原 `ProvableCode`。
复合项的 `binary_term_evaluation` 通过源同余推导组合子项等式与运算等式，
`term_mapped` 统一证明槽位代入与项码构造交换。配对的两分支消费序关系
正负反射和复合算术求值；节点、字段列及 Horn 表达式沿原编码构造组合，
参数化 AST 码项复用 `ObjectCodeInstantiation` 的既有关系保持遍历。
`quotation_evaluation` 直接覆盖原结构树。此处项骨架固定于元层，输入值、
数码与内部证明不要求外部标准；并未声称任意内部 AST 的统一解释器已完成。
D1、D2 与 Rosser 的公开结论保持；当前证明图、quotation、
公理和 Rosser 终点源码未改动。

`bounded_bundle` 的归纳性质是 `ObjectBoundedReflection.bundleAt`：内部区间上
所有数码实例的可证明性，蕴含有界全称实例的可证明性。性质只含实际数码图、
原证明图及固定 AST 码项；`bundleAt_agrees`、`parameterValues_agrees` 完成最终阶段对应，
没有把任意外部谓词当作可分离公式。反例方向及存在双重否定对偶保留原量词 AST。

`numeral_trace_positive` 的归纳性质是 `ObjectNumeralTraceReflection.atInput`，
包含原数码图、数码实例编码与原证明谓词。`numeralTraceAt_agrees` 完成最终阶段对应，
后继步从任意原内部轨迹反演前驱，并用 `numeral_trace_step` 构造下一图实例的证明。
`numeral_trace_negative` 使用已证明的总性与唯一性及不等式反射，不枚举拒绝轨迹。
`predicate_transport` 通过含量词模板同余和项求值，把两种反射传到复合项。
这些结论没有标准性、外部有限性或额外反射假设。

`projection_get_positive` 按内部索引归纳，性质为 `ObjectHornReflection.getAt`；
`projectionGet_agrees` 证明最终阶段对应。`rule_cases` 只读取原内部轨迹根行，
`horn_rule_values` 统一生成参数命名、守卫证明及前提／结论的数码传输。
`projection_positive` 据此覆盖原 `ObjectProjection.rules` 的全部七条规则，
`projection_term_positive` 接入复合行项，`projection_positive_derives` 给出源理论统一闭句。
不要求规范树／列表外壳，未假定内部索引或轨迹外部标准、有限或良基。
本入口只证明投影图正反射，不登记一般负反射。

`syntax_positive` 覆盖原 `ObjectFormulaSyntax.rules` 的任意内部根行。
[PureSourceSyntaxRank](../YesMetaZFC/Model/ZFC/Pure/PureSourceSyntaxRank.lean) 的 `rule_ranked` 从实际规则表证明子输入严格小于头输入；
`rank_unique` 用编码单射性恢复输入秩，量词下增长的 bound 长度不影响下降。
归纳正文为 `ObjectSyntaxReflection.atInput`，同时量化内部上下文和参数个数；
`syntaxAt_agrees` 证明最终阶段对应，`PureSourceInduction.strong_induction` 通过
较小输入的有界全称公式实现内部强归纳。规则装配复用 `horn_rule_values`。
`syntax_term_positive` 支持复合行项，`syntax_positive_derives` 给出统一闭句推导。
本入口证明一般语法图正反射，不登记一般负反射。

[InternalTransformReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalTransformReflection.lean) 用 `horn_valid_positive` 覆盖原 28 条变换规则。
查表先按表尾下降，再对语法输入下降；元层有限阶段与内部输入强归纳分开。
[InternalSchemaGraphs](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaGraphs.lean) 覆盖正文、重命名、表生成、闭合和 quotation 转换。
[InternalPacketReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPacketReflection.lean) 覆盖原传输包十条规则；token 的递归输入下降
由原 radix 128 仿射图的正尾增长界推出，不依赖外部数值解码。
原规则量化的隐含中间参数通过 `rule_cases_bounds`／`horn_rule_bounded_values`
保留实际边界，未加入“所有变量必须出现在头部”的额外条件。

[InternalSchemaReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaReflection.lean) 将上述图和固定表组合为原 schema 的完整有界查询。
[InternalPositiveQuantifiers](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPositiveQuantifiers.lean) 只用正向见证引入，复用规范 binder 打开与替换，
不假设各图具有负反射。[InternalSchemaQueries](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaQueries.lean) 的 `axiom_query_positive`
支持已求值复合项，`axiom_query_positive_derives` 是实际 `ReducedAxiomNumber.localTest`
成立时数码实例可证明性的普通闭句推导。输入、见证、数码及原集合轨迹都允许非标准。

[InternalLocalDecisionReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalLocalDecisionReflection.lean) 对任意原局部规则表统一处理头等式、全部子查询
与有界存在块；没有逐条复制 27 类逻辑公理的证明。
[InternalProofQueries](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofQueries.lean) 消费已完成的一般语法、变换、投影及实际公理查询，
得到六类节点及原零码／零标签／其他标签行封装的正反射。
[InternalProofRowReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofRowReflection.lean) 将其导出为复合项、任意内部数码及统一普通推导入口。
[InternalCheckedStepReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedStepReflection.lean) 的 `proof_step_values` 消去实际检查步骤中的
局部证明输入，只保留原 Horn 连边证明和局部真值；轨迹项不要求是自然数。
`finite_verification_of_links` 把同一装配接回原 `verificationMatrix`，仍显式要求有限骨架及连边证明。

[PureSourceCheckedConstruction](../YesMetaZFC/Model/ZFC/Pure/PureSourceCheckedConstruction.lean) 在根行反演时同时取得原 Horn 规则、参数界、守卫、局部真值及前提见证。
各前提保留同一原内部集合轨迹；构造时用公共集合 `collect` / `insert` 合并并插入头行。
[InternalCheckedReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedReflection.lean) 将实际局部查询正反射与前提数码证明组合，得到原规则结论的数码证明。

[InternalCheckedRanking](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedRanking.lean) 的 `checked_valid_positive` 对实际
`ObjectCheckedReflection.atPhase` 公式作内部强归纳，`checkedRankedAt_agrees` 核验最终阶段对应。
[ObjectCheckedReflection](../YesMetaZFC/Automation/ObjectCheckedReflection.lean) 的 `proof_valid` 以 Lean 内核核验原十二条规则：
节点阶段沿子证明编码下降，根阶段进入节点阶段。[InternalProofTraceReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofTraceReflection.lean)
的 `proof_trace_positive` 已填入原行查询正反射和对应合同，覆盖任意内部根行与轨迹。

[InternalVerificationReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalVerificationReflection.lean) 的 `verification_reflection` 通过
`verificationMatrix_trace` 精确接回原检查器正文，`proof_matrix_reflection` 补齐自然数 guard。
`proofMatrix_exists` 保持原普通可证明性句子；[ReducedIntrospection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedIntrospection.lean) 的
`ReducedProvability.introspection` 因而给出 $T\vdash\Box\varphi\to\Box\Box\varphi$。
这些入口不要求外部有限骨架、逐条连边证明、额外反射、一致性或标准模型假设。

[Loeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Loeb.lean) 将 D1–D3
封装为 `DerivabilityConditions_m`。给定固定点 $\psi\leftrightarrow(\Box\psi\to\varphi)$，
先由 D2、D3 得到 $\Box\psi\to\Box\varphi$，再推出
$(\Box\varphi\to\varphi)\to\psi$；D1、D2 提升后一推导，给出内部 Löb 公式。
[ReducedLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedLoeb.lean)
实际构造 `loebSentence_m` 并证明 `loeb_fixed_point_m`，因此 `loeb_axiom_m` 无额外固定点或
反射前提；`loeb_m` 将 $T\vdash\Box\varphi\to\varphi$ 转为 $T\vdash\varphi$。
这里 $T$ 与 $\Box$ 仍是原 `intrinsic_zfc_theory` 与 `ReducedProvability.provable`。

[ReducedSecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedSecondIncompleteness.lean)
复用 $\varphi=\bot$ 的固定点，保持已有 $\mathrm{Con}(T)=\neg\Box\bot$。
`second_incompleteness_internal_m` 证明 $T\vdash\mathrm{Con}(T)\to\neg\Box\mathrm{Con}(T)$；
`second_incompleteness_m` 只假定 `Derives.Consistent T []`，便排除 $T\vdash\mathrm{Con}(T)$。
通用证明见 [SecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SecondIncompleteness.lean)：
若有一致性句子的推导，否定消去将它转成 $\Box\bot\to\bot$，Löb 规则随即推出矛盾。

## 裸 ZFC 的语言、可证明性与固定点传输

令 $Z=\texttt{PureModel.theory}$，$e=\texttt{PureSentenceTransfer.embed_m}$，
$\tau=\texttt{PureRosser.translate}$。[PureSentenceTransfer](../YesMetaZFC/Model/ZFC/Pure/PureSentenceTransfer.lean)
使用模型扩张后的约化等于原纯模型，证明 $Z\vdash\tau(e(\varphi))\leftrightarrow\varphi$；
结合原模型约化和强完备性，得到 $T\vdash e(\varphi)\iff Z\vdash\varphi$。
对于任意源句子 $\psi$，$T\vdash\psi\leftrightarrow e(\tau(\psi))$ 仍需其任意模型对应。

[PureProvability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureProvability.lean)
定义 $\Box_Z\varphi=\tau(\Box_T e(\varphi))$。`checked_iff_m` 证明原检查器接受某个
$e(\varphi)$ 的证书当且仅当 $Z\vdash\varphi$，因此这个纯算子确实表示裸 ZFC 的推导。
`source_canonical_m` 使用已完成的全部内部证明码对应和 quotation 对应，
使 $\Box_T\psi$ 在任意原模型及其规范重扩张中同真。
D1、D2 直接经嵌入和翻译传输；D3 还用
$T\vdash\Box_T e(\varphi)\leftrightarrow e(\Box_Z\varphi)$ 的正向推导提升可证明性，
接上原 D3，得到 $Z\vdash\Box_Z\varphi\to\Box_Z\Box_Z\varphi$。

[PureLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLoeb.lean)
从原固定点 $\psi\leftrightarrow(\Box_T\psi\to e(\varphi))$ 出发，
通过右侧的实际对应证明 $\psi$ 的任意模型对应；再把
$\psi\leftrightarrow e(\tau(\psi))$ 提升到可证明性层，得到
$Z\vdash\tau(\psi)\leftrightarrow(\Box_Z\tau(\psi)\to\varphi)$。
`loeb_axiom_m` 和 `loeb_m` 因而使用纯算子的实际固定点，未留下固定点或反射假设。

[PureSecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSecondIncompleteness.lean)
令 $\mathrm{Con}_Z=\neg\Box_Z\bot$，证明内部公式
$Z\vdash\mathrm{Con}_Z\to\neg\Box_Z\mathrm{Con}_Z$；只由裸 ZFC 一致便推出
$Z\nvdash\mathrm{Con}_Z$。`consistency_translation_m` 还确认 $\mathrm{Con}_Z=\tau(\mathrm{Con}_T)$。
这些是纯隶属语言、原始 ZFC 公理下的普通 `Derives` 结论。
编码仍是嵌入句子的原 quotation 与检查器；另选直接编码纯 ZFC 证明树的谓词，
及其与当前算子的内部等价，不属于此处已证内容。

## 原支撑理论的真不可定义性

[Tarski](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Tarski.lean)
将候选闭句算子 $F$ 的两种合同分开：`TruthSchema_m T F` 要求所有
$T\vdash F(\varphi)\leftrightarrow\varphi$；`DefinesTruth_m ℳ F` 要求所有
$\mathcal M\models F(\varphi)\leftrightarrow\varphi$。
`liar_refutes_m` 仅从 $T\vdash L\leftrightarrow\neg F(L)$ 推出
$T\vdash\neg(F(L)\leftrightarrow L)$，其逻辑核心还允许开放公式和任意局部上下文。
一致性排除相应等价式的推导，可靠性排除模型中的全部真值对应。

[ObjectTarskiFixedPoint](../YesMetaZFC/Automation/ObjectTarskiFixedPoint.lean)
对任意 `FormulaTemplate.Unary` 的正文取否定，调用原 `ObjectDiagonal.fixedPoint_spec`。
[ReducedTarski](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedTarski.lean)
以 `ReducedRosser.diagonalSupport` 实例化，令
$F(\varphi)=P(\texttt{IntrinsicQuotation.quote}\ \varphi)$，并实际生成 `liarSentence_m P`。
`liar_fixed_point_m` 与 `liar_refutes_m` 没有额外固定点、一致性或反射前提。
`undefinable_syntax_m` 只假定 `Derives.Consistent intrinsic_zfc_theory []`，排除所有候选一元公式；
`undefinable_semantics_m` 对任意载体宇宙的 $\mathcal M\models\texttt{intrinsic_zfc_theory}$ 成立。

候选只有编码变量这一自由槽位，不携带任意模型参数；真值合同量化宿主 `SetSentence`，
不把非标准内部语法当作宿主有限语法，也不要求模型的内部自然数标准。
既有 `TarskiTruth` 是集合结构满足关系的对象定义规格，不是此全局真谓词。
最终纯公式自身编码的对角化由下述 `PureFixedPoint` 独立完成；
原 `PureLoeb` 的特定算子固定点仍保留其既有编码合同。

### 参数上下文与逐赋值反例

[ObjectParameterDiagonal](../YesMetaZFC/Automation/ObjectParameterDiagonal.lean)
对任意有限 `parameters : SetContext` 和 $P(x,\bar z)$ 实际生成固定点，
将原同时自由代入图的表尾推广为参数变量的恒等替换。对象输出唯一性复用既有最小见证论证。
[ReducedTarskiParameters](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedTarskiParameters.lean)
在同一支撑理论上证明
$T\vdash L_P(\bar z)\leftrightarrow\neg P(\ulcorner L_P\urcorner,\bar z)$，并全称闭合其反驳式。
`undefinable_syntax_m` 只假定原理论在闭上下文中的一致性；开放上下文一致性由闭项代入推出。
`liar_fails_at_m` 与 `undefinable_at_m` 对每个任意模型赋值 `env` 成立；
`undefinable_parameters_m` 同时排除参数上下文、赋值及候选公式的存在。

这里 `DefinesSatisfaction_m env` 要求相同自由上下文中的全部宿主开放公式同真。
任意参数取值不需要能被闭项命名，也不要求模型标准；quotation 只编码实际公式语法。
只定义无参数闭句真值的带参数谓词不满足这个合同的全部要求，不能据此宣称已排除它。
原闭固定点的空参数构造与修改前 AST 已通过通用定义等式核验；原 quotation 随之保持。

### 保留源编码的裸 ZFC 终点

[PureOpenTransfer](../YesMetaZFC/Model/ZFC/Pure/PureOpenTransfer.lean)
将纯候选按同一参数槽嵌入原语言，证明规范扩张中的逐环境真值往返及开放公式双向推导。
纯签名没有闭项，故开放上下文的一致性通过既有模型存在性与模型非空性取得。
[PureTarskiSource](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTarskiSource.lean)
对任意纯候选 $P(x,\bar z)$ 构造源反例 $S_P$ 和纯反例 $L_P=\tau(S_P)$。
`liar_fixed_point_m`、`liar_refutes_closed_m` 的实际推导理论是裸 `PureModel.theory`；
`undefinable_syntax_m` 只假定该裸理论在闭上下文中的一致性。

`predicate_satisfies_m` 证明消元后的候选实例在任意裸模型和任意参数环境中，恰好是原纯
$P$ 在源 quotation 值处的应用。`undefinable_source_at_m` 直接排除
$P(\ulcorner\varphi\urcorner,\bar a)\leftrightarrow\varphi^{\mathcal M^+}(\bar a)$
对全部源开放公式成立；$\mathcal M^+$ 是现有规范扩张。参数个数和取值任意，模型无需标准。
`undefinable_parameters_m` 对所有这些参数上下文和赋值统一排除纯翻译的真值合同。

这里保留原自代入图及原 quotation，没有加入消元编码图或纯语法专用 quotation。
固定点使用的是 $\ulcorner S_P\urcorner$，不是 $\ulcorner\tau(S_P)\urcorner$；
不能把这个已证合同直接换成仅量化纯公式并使用纯公式自身编码的合同。
也没有由规范扩张的正确性推断任意原模型对全部源公式的约化往返。

### 最终纯公式自身编码的裸 ZFC 终点

[PureQuotationFaithful](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureQuotationFaithful.lean) 给出纯 AST 数值编码的单射性，
并证明结构嵌入与现有完整 AST 编解码器的逐节点对应。纯数码公式 $N_n(x)$
在任意裸模型中唯一定义规范扩张内相应的有限数码值；不对内部自然数作标准性假设。

[PureDiagonalGraph](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureDiagonalGraph.lean) 的实际纯图在标准输入 $n$ 处，
对任意对象输出 $a$ 恰好等价于 $a=d(n)$。递推只用两条固定 Horn 规则；
最小见证论证消费标准正负实例，从而排除任意内部伪轨迹产生的错误输出。
`self_code_m` 是最终 $\exists x(N_n(x)\land B)$ 的 AST 编码等式，
[PureFixedPoint](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFixedPoint.lean) 的 `fixed_point_m` 据此在普通裸 ZFC 推导中成立。

[PureTarski](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTarski.lean) 中候选、反例及合同量化的公式全是纯公式，
`quotation_m hℳ φ` 命名 $\varphi$ 自身的完整 AST 码。
`liar_fixed_point_m` 与全称闭合反驳式没有一致性前提；句法不可定义性只假定裸 ZFC 一致。
`undefinable_parameters_m` 对任意裸模型和每组任意有限参数成立，参数无需闭项名称。
合同包含使用这些参数的所有宿主开放公式；不将它改称只判定无参数闭句的带参数合同，
也不声称已构造非标准内部语法的满足关系。

## D1、D2 增量核验

在 `9045935` 基础上新增普通可证明性与内部 MP 构造，入口为
[ReducedDerivability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedDerivability.lean)。
`lake --wfail build` 完成 820 个任务；`bash scripts/check-all.sh` 检查全部
823 个 Lean 模块，完成 825 个全源构建任务及 320 个扫描工具任务，零错误、零警告。
这是恢复环境中的增量内核构建，不声称冷构建或远端 CI 已运行。

新增源码没有 `sorry`、`admit`、自定义公理或原生计算验证调用。
实际 `#print axioms` 核验显示：通用 D1 依赖 `propext`、`Quot.sound`；
源理论 D1 的 11 项依赖是既有 Rosser 终点依赖的子集；D2 和内部 MP 构造的
32 项依赖集合均与 `PureRosser.independent` 相同。这里保留仓库已有的原生
支撑依赖，不把“无新增依赖”表述为“没有原生依赖”。
原有证明图、quotation、公理和 Rosser 终点的源码均未修改。

## Rosser 与既有声明的核验基点

源码基点为 [4ae86c1](https://github.com/lanxinge/YesMetaZFC/commit/4ae86c1b38c756e95d3dee7e8de50a9c60db292b)。
该源码的全源检查完成 808 个构建任务、扫描工具检查完成 320 个任务，零错误、零警告。

公开声明审计保留全部 13,662 项基线声明；13,658 项原始编译类型相同，4 项仅有
相互递归生成的 binder 显示名差别。6,955 项数据定义中，6,953 项原始表达式相同；
`HilbertBaseAxiom.lower` 另经 Lean 证明任意输入的完整返回证书与旧实现相等，
`FirstOrderDerives.try_close` 是已实施的自动化改进。

60 项辅助声明因公共接口复用增加对既有 `propext`、`Quot.sound`、`Classical.choice`
的部分引用；审计范围内全仓公理并集未增加，Rosser 两个终点的类型和完整依赖集合
保持，没有新增对象公理、Lean 公理常量、原生验证依赖或 `sorryAx`。
最终审计覆盖 13,893 项，包括新增及补充纳入项；不把新增覆盖项冒充旧基线。

日常入口：`lake --wfail build`、`bash scripts/check-all.sh`。
本次文档整理沿用该源码核验结果，不声称重新构建或远端 CI 通过。
独立数学待办仍是原递归序列族之并在合法递归器下的 ω 全域性，见
[ELIMINATION.md](ELIMINATION.md)。
