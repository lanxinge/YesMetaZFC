# 公理验证与 Rosser 接口指路表

验证对象是原 `intrinsic_proof_theory`、`intrinsic_zfc_theory` 及纯语言中的
`PureModel.theory`。裸 ZFC Rosser 实例已完成；独立性定理假定裸 ZFC 一致，
不证明 ZFC 自身的一致性。纯定义构造见 [ELIMINATION.md](ELIMINATION.md)，
证书与检查器见 [NAT_DECODING.md](NAT_DECODING.md)。

## 模型、公理与推导

| 要使用的结果 | 接口与源码 | 精确范围 |
| --- | --- | --- |
| 有限基覆盖原支撑理论 | [FiniteAxiomModels](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/FiniteAxiomModels.lean) 中 `FiniteAxiomBasis.models_iff`；[ReducedAxioms](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedAxioms.lean) 的 `derives_iff` | 108 个具体闭句与 11 个参数分离模板，共 119 条；与原无限参数理论推导等价，不是公理集合相等 |
| 完整支撑模型 | [PureSupportModels](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportModels.lean) 的 `support_models` | 同一规范扩张满足整个原支撑理论 |
| 原 ZFC 像及实际纯翻译 | [PureZFCModels](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureZFCModels.lean) 的 `models`、`translated_models` | 不弱化原公理或 guard |
| 模型扩张与约化 | [PureZFCModels](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureZFCModels.lean) 的 `expands`、`reduct_models`、`reduction` | 约化适用于任意原模型，不仅规范扩张 |
| 公平调度与正向推导传输 | [PureRosserSchedule](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserSchedule.lean) 的 `source`、`target`；[PureRosser](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosser.lean) 的 `translate_derives` | 使用 Henkin 强完备性传输源闭句推导；一般反向句法保守性不在此结论中 |
| 实际纯固定点 | [PureRosser](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosser.lean) 的 `sentence`、`comparison`、`fixed_point` | 当前源 Rosser 及源 quotation 的实际纯翻译，不是纯语言 quotation 上重新对角化 |
| 任意原模型上的句子对应 | [PureRosserComplete](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) 中 `PureRosser.agreement` | `Agreement` 已有证明；[PureRosser](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosser.lean) 的 `truth_iff` 只涉及规范扩张，不能单独代替它 |
| 裸 ZFC 双侧不可证性 | [PureRosserComplete](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) 中 `PureRosser.independent` | 仅由裸 ZFC 一致性推出当前句子及其否定均不可推导 |

## 任意原模型的内部证明码对应

下列接口连接任意原模型与其纯约化的规范重扩张。自然数指模型内部 ω，
允许非标准元素；局部规则比较同一候选集合轨迹，不对内部 ω 作外部归纳。

| 需要保持的内容 | 接口与源码 | 使用条件 |
| --- | --- | --- |
| 标准数码与 quotation | [PureSourceNumerals](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceNumerals.lean) 的 `numeral_agrees`、`quotation_agrees`、`proof_numeral_agrees` | 只凭标准码结果不能推出全部内部自然数对应 |
| 当前证明码域 | [ReducedNaturalProofPresentation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedNaturalProofPresentation.lean) 的 `presentation`、`natural_of_satisfied` | `code ∈ ω` 包装保留检查器、标准码正负表示及完备性；旧后继码域见 [RosserDomainBoundary](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/RosserDomainBoundary.lean) |
| 同一内部 ω 及顺序 | [PureSourceInfinity](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceInfinity.lean) 的 `omega_agrees`、`member_natural`、`natural_compare` | 来自原归纳定义与最小性，不添加标准性假设 |
| 合法映射与求值 | [PureSourceMappings](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceMappings.lean) 的 `ordered_agrees`、`mapping_project`、`application_agrees` | 求值保持限于原定义域；不宣称非法输入总值对应或映射谓词无条件反向等价 |
| 内部加、乘、幂 | [PureSourceArithmetic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceArithmetic.lean) 的 `addition_agrees`、`multiplication_agrees`、`exponentiation_agrees` | 使用实际有限递推图及内部唯一性，覆盖所有内部自然数输入 |
| 配数、字段与根编码 | [PureSourceCoding](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceCoding.lean) 的 `pairing_agrees`、`fields_agrees`、`node_agrees`；[PureNaturalRosserAgreement](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNaturalRosserAgreement.lean) 的 `root_agrees` | 实际编码保持；根值不是待填前提 |
| 幂集界与集合轨迹 | [PureSourceBounds](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceBounds.lean) 的 `power_agrees`、`trace_bound_agrees`、`trace_row_natural`；[PureNaturalRosserAgreement](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNaturalRosserAgreement.lean) 的 `proof_trace` | 保留实际 `P(ω)` 界和轨迹行的自然数证据 |
| 有界见证与局部规则 | [ObjectHornSemantics](YesMetaZFC/Automation/ObjectHornSemantics.lean)；[PureSourceHorn](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceHorn.lean) 的 `condition_agrees`、`localTest` | 递归前提读取同一候选集合；不假定其外部有限 |
| 自然数参数的公式组合 | [PureSourceFormula](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceFormula.lean) 的 `instantiate`、`quantify` | 保留自然数环境、逐变量相等和实际见证界 |
| 公理检查 | [PureSourceSchemas](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceSchemas.lean) 的 `axiomTest` | 固定公理表及分离、收集、替换模式的实际中间码连接 |
| 节点、行与完整证明图 | [PureSourceLocalTests](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceLocalTests.lean) 的 `currentNode`、`currentRow`、`row_agrees`、`proof_agreement` | 任意固定结论、全部内部自然数证明码；提供 Rosser 所需的两项 ProofAgreement |
| 图对应推出句子对应 | [PureNaturalRosserAgreement](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNaturalRosserAgreement.lean) 的 `proof_agreement_of_rows`、`agreement_of_natural_proofs` | 局部行与两侧图对应均已有上述实际实例，最终由 `PureRosser.agreement` 装配 |

旧后继码域包含 ω 自身，不能由根项属于 ω 推断原输入属于 ω。
这一边界既不是 `Agreement` 的反例，也不是其不可证明性结论；当前自然数包装和
上表的内部对应已经完成实际实例。

## Δ₀ 的适用范围

| 结果 | 入口 | 边界 |
| --- | --- | --- |
| 支撑语言的 Δ₀ 等价代表 | [ReducedRosser](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedRosser.lean) 的 `predicate_delta0`、`delta0Sentence_delta0`、`delta0Sentence_independent` | 语言含 ω、幂集及编码函数；不自动成为纯隶属或一阶算术 Δ₀ |
| 无参数纯闭 Δ₀ 可决定 | [FunctionFreeDelta0](YesMetaZFC/Automation/FunctionFreeDelta0.lean) 的 `closed_decided` | 纯 ℒ 只有二元 ∈，没有常元、函数或零元关系 |
| 当前纯闭句非 Δ₀ | [PureRosserDelta0](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `sentence_not_delta0`、`comparison_not_delta0` | 无条件的语法分类；不能再列为正向分类待办 |
| 排除闭 Δ₀ 等价代表 | [PureRosserDelta0](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `no_closed_delta0_equivalent` | 假定裸 ZFC 一致，排除可证明等价的无参数纯 Δ₀ 闭句 |
| 三参数纯 Δ₀ 矩阵 | [PureRosserDelta0](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `matrix_delta0`、`parameters_exists`、`parameters_unique`、`sentence_iff_matrix`、`representation_derives` | 参数为内部 ω 与两侧内部证明码集合；参数定义本身未分类为 Δ₀ |

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
| 1 | `(empty_predicate (free := [])).separation_axiom` | `PureSupportSeparation.separation_axiom (empty_predicate (free := []))`；[PureSupportSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportSeparation.lean) |
| 2 | `membership_relation_predicate.separation_axiom` | `PureSupportSeparation.separation_axiom membership_relation_predicate`；[PureSupportSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportSeparation.lean) |
| 3 | `Nonlogical.BasicSetTheory.infinity_axiom` | `PureFinalInfinity.infinity`；[PureFinalInfinity](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalInfinity.lean) |
| 4 | `term_value_definition_axiom ∧ₘ term_list_value_definition_axiom` | `And.intro (PureFinalSyntax.term_value) (PureFinalSyntax.term_list_value)`；[PureFinalSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSyntax.lean) |
| 5 | `binary_union_definition_axiom` | `PureFinalBasic.binary_union`；[PureFinalBasic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalBasic.lean) |
| 6 | `bounded_subset_definition_axiom` | `PureFinalRelations.bounded_subset`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 7 | `cardinality_leq_definition_axiom` | `PureFinalRelations.cardinality_leq`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 8 | `cardinality_strict_less_definition_axiom` | `PureFinalRelations.cardinality_strict_less`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 9 | `cartesian_product_definition_axiom` | `PureFinalCollections.cartesian_product`；[PureFinalCollections](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalCollections.lean) |
| 10 | `domain_definition_axiom` | `PureFinalMappings.domain`；[PureFinalMappings](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalMappings.lean) |
| 11 | `empty_set_definition_axiom` | `PureFinalBasic.empty_set`；[PureFinalBasic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalBasic.lean) |
| 12 | `equality_axiom_schema_definition_axiom` | `(PureFinalSyntax.schema_axioms).2.2`；[PureFinalSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSyntax.lean) |
| 13 | `extensionality_axiom` | `PureFinalBasic.extensionality_axiom`；[PureFinalBasic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalBasic.lean) |
| 14 | `finite_hierarchy_definition_axiom` | `PureFinalConstructions.finite_hierarchy`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 15 | `finite_sequence_concatenation_definition_axiom` | `PureFinalConstructions.finite_sequence_concatenation`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 16 | `finite_sequence_flatten_definition_axiom` | `PureFinalConstructions.finite_sequence_flatten`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 17 | `finite_sequence_space_definition_axiom` | `PureFinalConstructions.finite_sequence_space`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 18 | `finite_subset_collection_definition_axiom` | `PureFinalConstructions.finite_subset_collection`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 19 | `finite_subset_collection_separation_axiom` | `PureFinalSeparation.finite_subset_collection`；[PureFinalSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSeparation.lean) |
| 20 | `finite_universe_definition_axiom` | `PureFinalConstructions.finite_universe`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 21 | `free_variable_occurs_definition_axiom` | `PureFinalSyntax.free_variable_occurs`；[PureFinalSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSyntax.lean) |
| 22 | `function_application_definition_axiom` | `PureFinalMappings.application`；[PureFinalMappings](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalMappings.lean) |
| 23 | `godel_pairing_definition_axiom` | `PureFinalConstructions.godel_pairing`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 24 | `hereditarily_finite_definition_axiom` | `PureFinalRelations.hereditarily_finite`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 25 | `identity_definition_axiom` | `PureFinalCollections.identity`；[PureFinalCollections](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalCollections.lean) |
| 26 | `image_definition_axiom` | `PureFinalOperations.image`；[PureFinalOperations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalOperations.lean) |
| 27 | `index_order_definition_axiom` | `PureFinalConstructions.index_order`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 28 | `inductive_core_definition_axiom` | `PureFinalInfinity.inductive_core`；[PureFinalInfinity](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalInfinity.lean) |
| 29 | `is_bijection_definition_axiom` | `PureFinalRelations.is_bijection`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 30 | `is_countable_definition_axiom` | `PureFinalRelations.is_countable`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 31 | `is_countably_infinite_definition_axiom` | `PureFinalRelations.is_countably_infinite`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 32 | `is_dedekind_finite_definition_axiom` | `PureFinalRelations.is_dedekind_finite`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 33 | `is_equinumerous_definition_axiom` | `PureFinalRelations.is_equinumerous`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 34 | `is_equivalence_relation_definition_axiom` | `PureFinalRelations.is_equivalence_relation`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 35 | `is_finite_definition_axiom` | `PureFinalRelations.is_finite`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 36 | `is_function_definition_axiom` | `PureFinalMappings.is_function`；[PureFinalMappings](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalMappings.lean) |
| 37 | `is_inductive_set_definition_axiom` | `PureFinalRelations.is_inductive_set`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 38 | `is_infinite_definition_axiom` | `PureFinalRelations.is_infinite`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 39 | `is_injective_definition_axiom` | `PureFinalRelations.is_injective`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 40 | `is_linear_order_definition_axiom` | `PureFinalRelations.is_linear_order`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 41 | `is_mapping_definition_axiom` | `PureFinalMappings.is_mapping`；[PureFinalMappings](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalMappings.lean) |
| 42 | `is_natural_discrete_linear_order_definition_axiom` | `PureFinalRelations.is_natural_discrete_linear_order`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 43 | `is_order_embeddable_definition_axiom` | `PureFinalRelations.is_order_embeddable`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 44 | `is_order_embedding_definition_axiom` | `PureFinalRelations.is_order_embedding`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 45 | `is_order_isomorphic_definition_axiom` | `PureFinalRelations.is_order_isomorphic`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 46 | `is_order_isomorphism_definition_axiom` | `PureFinalRelations.is_order_isomorphism`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 47 | `is_ordered_pair_definition_axiom` | `PureFinalPairs.is_ordered_pair`；[PureFinalPairs](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalPairs.lean) |
| 48 | `is_relation_definition_axiom` | `PureFinalPairs.is_relation`；[PureFinalPairs](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalPairs.lean) |
| 49 | `is_surjective_definition_axiom` | `PureFinalRelations.is_surjective`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 50 | `is_transitive_set_definition_axiom` | `PureFinalRelations.is_transitive_set`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 51 | `is_uncountable_definition_axiom` | `PureFinalRelations.is_uncountable`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 52 | `left_projection_definition_axiom` | `PureFinalPairs.left_projection`；[PureFinalPairs](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalPairs.lean) |
| 53 | `logical_axiom_code_definition_axiom` | `PureFinalSyntax.logical_axioms`；[PureFinalSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSyntax.lean) |
| 54 | `mapping_collection_definition_axiom` | `PureFinalCollections.mapping_collection`；[PureFinalCollections](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalCollections.lean) |
| 55 | `maximum_natural_order_definition_axiom` | `PureFinalExtrema.maximum_natural_order`；[PureFinalExtrema](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalExtrema.lean) |
| 56 | `membership_irreflexive_axiom` | `PureFinalBasic.irreflexivity`；[PureFinalBasic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalBasic.lean) |
| 57 | `membership_relation_definition_axiom` | `PureFinalOperations.membership_relation`；[PureFinalOperations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalOperations.lean) |
| 58 | `minimum_difference_definition_axiom` | `PureFinalConstructions.minimum_difference`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 59 | `minimum_linear_order_definition_axiom` | `PureFinalExtrema.minimum_linear_order`；[PureFinalExtrema](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalExtrema.lean) |
| 60 | `minimum_natural_order_definition_axiom` | `PureFinalExtrema.minimum_natural_order`；[PureFinalExtrema](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalExtrema.lean) |
| 61 | `modus_ponens_definition_axiom` | `PureFinalSyntax.modus_ponens`；[PureFinalSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSyntax.lean) |
| 62 | `natural_addition_definition_axiom` | `PureFinalConstructions.natural_addition`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 63 | `natural_addition_upper_bound_axiom` | `PureFinalArithmetic.addition_upper_axiom`；[PureFinalArithmetic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalArithmetic.lean) |
| 64 | `natural_difference_definition_axiom` | `PureFinalConstructions.natural_difference`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 65 | `natural_exponent_product_index_bound_axiom` | `PureFinalArithmetic.exponent_product_axiom`；[PureFinalArithmetic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalArithmetic.lean) |
| 66 | `natural_exponentiation_definition_axiom` | `PureFinalConstructions.natural_exponentiation`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 67 | `natural_exponentiation_index_bound_axiom` | `PureFinalArithmetic.exponent_axiom`；[PureFinalArithmetic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalArithmetic.lean) |
| 68 | `natural_godel_pairing_coordinate_bound_axiom` | `PureFinalArithmetic.pairing_axiom`；[PureFinalArithmetic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalArithmetic.lean) |
| 69 | `natural_le_lt_transitivity_axiom` | `PureFinalArithmetic.transitivity_axiom`；[PureFinalArithmetic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalArithmetic.lean) |
| 70 | `natural_multiplication_definition_axiom` | `PureFinalConstructions.natural_multiplication`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 71 | `natural_order_type_definition_axiom` | `PureFinalConstructions.natural_order_type`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 72 | `natural_positive_left_addition_strict_bound_axiom` | `PureFinalArithmetic.positive_addition_axiom`；[PureFinalArithmetic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalArithmetic.lean) |
| 73 | `natural_subset_type_definition_axiom` | `PureFinalConstructions.natural_subset_type`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 74 | `nonempty_finite_sequence_space_definition_axiom` | `PureFinalConstructions.nonempty_finite_sequence_space`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 75 | `nonempty_finite_sequence_space_separation_axiom` | `PureFinalSeparation.nonempty_sequence_space`；[PureFinalSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSeparation.lean) |
| 76 | `omega_definition_axiom` | `PureFinalInfinity.omega`；[PureFinalInfinity](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalInfinity.lean) |
| 77 | `omega_pair_less_definition_axiom` | `PureFinalRelations.omega_pair_less`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 78 | `omega_recursive_sequence_definition_axiom` | `PureFinalConstructions.omega_recursive_sequence`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 79 | `ordered_pair_definition_axiom` | `PureFinalPairs.ordered_pair`；[PureFinalPairs](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalPairs.lean) |
| 80 | `ordered_pair_reverse_definition_axiom` | `PureFinalPairs.reverse`；[PureFinalPairs](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalPairs.lean) |
| 81 | `pair_definition_axiom` | `PureFinalBasic.pairing`；[PureFinalBasic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalBasic.lean) |
| 82 | `pairing_axiom` | `PureFinalBasic.pairing_exists`；[PureFinalBasic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalBasic.lean) |
| 83 | `power_set_axiom` | `PureFinalBasic.power_exists_axiom`；[PureFinalBasic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalBasic.lean) |
| 84 | `power_set_bijection_definition_axiom` | `PureFinalConstructions.power_set_bijection`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 85 | `power_set_definition_axiom` | `PureFinalBasic.power_definition`；[PureFinalBasic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalBasic.lean) |
| 86 | `propositional_axiom_schema_definition_axiom` | `(PureFinalSyntax.schema_axioms).1`；[PureFinalSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSyntax.lean) |
| 87 | `quantifier_axiom_schema_definition_axiom` | `(PureFinalSyntax.schema_axioms).2.1`；[PureFinalSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSyntax.lean) |
| 88 | `range_definition_axiom` | `PureFinalMappings.range`；[PureFinalMappings](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalMappings.lean) |
| 89 | `recursive_sequence_space_definition_axiom` | `PureFinalConstructions.recursive_sequence_space`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 90 | `related_nonlogical_symbol_set_definition_axiom` | `PureFinalSyntax.nonlogical_symbols`；[PureFinalSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSyntax.lean) |
| 91 | `related_syntax_definition_axiom` | `PureFinalSyntax.related_syntax`；[PureFinalSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSyntax.lean) |
| 92 | `relation_composition_definition_axiom` | `PureFinalOperations.composition`；[PureFinalOperations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalOperations.lean) |
| 93 | `relation_converse_definition_axiom` | `PureFinalOperations.converse`；[PureFinalOperations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalOperations.lean) |
| 94 | `relation_image_separation_axiom` | `PureFinalSeparation.relation_image`；[PureFinalSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSeparation.lean) |
| 95 | `restriction_definition_axiom` | `PureFinalCollections.restriction`；[PureFinalCollections](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalCollections.lean) |
| 96 | `right_projection_definition_axiom` | `PureFinalPairs.right_projection`；[PureFinalPairs](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalPairs.lean) |
| 97 | `singleton_definition_axiom` | `PureFinalBasic.singleton`；[PureFinalBasic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalBasic.lean) |
| 98 | `structural_syntax_definition_axiom` | `PureFinalSyntax.structural_syntax`；[PureFinalSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSyntax.lean) |
| 99 | `structure_definition_axiom` | `PureFinalSyntax.structure_axiom`；[PureFinalSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSyntax.lean) |
| 100 | `subset_definition_axiom` | `PureFinalBasic.subset`；[PureFinalBasic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalBasic.lean) |
| 101 | `successor_definition_axiom` | `PureFinalBasic.successor`；[PureFinalBasic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalBasic.lean) |
| 102 | `symmetric_difference_definition_axiom` | `PureFinalOperations.symmetric_difference`；[PureFinalOperations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalOperations.lean) |
| 103 | `syntax_transform_definition_axiom` | `PureFinalSyntax.syntax_transform`；[PureFinalSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSyntax.lean) |
| 104 | `transitive_closure_definition_axiom` | `PureFinalConstructions.transitive_closure`；[PureFinalConstructions](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalConstructions.lean) |
| 105 | `unbounded_subset_definition_axiom` | `PureFinalRelations.unbounded_subset`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 106 | `union_axiom` | `PureFinalBasic.union_exists_axiom`；[PureFinalBasic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalBasic.lean) |
| 107 | `union_definition_axiom` | `PureFinalBasic.union_definition`；[PureFinalBasic](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalBasic.lean) |
| 108 | `well_order_definition_axiom` | `PureFinalRelations.well_order`；[PureFinalRelations](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalRelations.lean) |
| 109 | `SupportAssembly.closedTemplate .cartesianProduct` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportSeparation.lean) |
| 110 | `SupportAssembly.closedTemplate .composition` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportSeparation.lean) |
| 111 | `SupportAssembly.closedTemplate .converse` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportSeparation.lean) |
| 112 | `SupportAssembly.closedTemplate .domain` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportSeparation.lean) |
| 113 | `SupportAssembly.closedTemplate .identity` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportSeparation.lean) |
| 114 | `SupportAssembly.closedTemplate .indexOrder` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportSeparation.lean) |
| 115 | `SupportAssembly.closedTemplate .inductiveCore` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportSeparation.lean) |
| 116 | `SupportAssembly.closedTemplate .mappingCollection` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportSeparation.lean) |
| 117 | `SupportAssembly.closedTemplate .powerSetBijection` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportSeparation.lean) |
| 118 | `SupportAssembly.closedTemplate .range` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportSeparation.lean) |
| 119 | `SupportAssembly.closedTemplate .symmetricDifference` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportSeparation.lean) |

## 当前核验基点

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
