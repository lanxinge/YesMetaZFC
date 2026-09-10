# 形式化成果入口

本表登记当前源码中的结论；构造和证明细节通过基础设施指南定位。

## 裸 ZFC Rosser 实例

纯理论为 `PureModel.theory`，具体闭句为 `PureRosser.sentence`。记它为 $R$：

$$
\operatorname{Con}(\mathrm{ZFC})\Longrightarrow
(\mathrm{ZFC}\nvdash R)\land(\mathrm{ZFC}\nvdash\neg R).
$$

$R$ 只含隶属关系、等号与逻辑符号，是当前源 Rosser 句子的实际纯翻译。
最终定理仅假定裸 ZFC 一致；任意原模型对应 `Agreement` 已有证明。

| 成果 | 声明与源码 |
| --- | --- |
| 具体纯句子与普通 Hilbert 固定点推导 | [PureRosser](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosser.lean) 的 `sentence`、`fixed_point` |
| 任意原模型上的句子对应 | [PureRosserComplete](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) 中 `PureRosser.agreement` |
| 裸 ZFC 双侧不可证性 | [PureRosserComplete](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) 中 `PureRosser.independent` |
| 三参数纯 Δ₀ 矩阵及实际推导等价 | [PureRosserDelta0](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `matrix_delta0`、`parameters_exists`、`parameters_unique`、`representation_derives` |
| 当前纯句子非 Δ₀，以及一致性下排除无参数闭 Δ₀ 等价代表 | [PureRosserDelta0](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `sentence_not_delta0`、`no_closed_delta0_equivalent` |

纯 Δ₀ 矩阵为 $\neg\exists p\in w\,(p\in A\land\forall q\in p\,q\notin B)$。
参数定义未分类为 Δ₀，保留定义的完整存在闭句非 Δ₀。

## 普通可证明性的 D1、D2、D3

令 $T=\texttt{intrinsic_zfc_theory}$，$\Box\varphi$ 为
`ReducedProvability.provable φ`，使用原有
`ReducedNaturalProofPresentation.presentation.graph` 和完整 AST quotation。

| 成果 | 声明与源码 |
| --- | --- |
| D1：$T\vdash\varphi$ 推出 $T\vdash\Box\varphi$ | [ReducedProvability](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProvability.lean) 的 `necessitation`；通用表示版见 [Provability](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Provability.lean) |
| D2：$T\vdash\Box(\varphi\to\psi)\to(\Box\varphi\to\Box\psi)$ | [ReducedDerivability](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedDerivability.lean) 中 `ReducedProvability.distribution` |
| D3：$T\vdash\Box\varphi\to\Box\Box\varphi$ | [ReducedIntrospection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedIntrospection.lean) 的 `ReducedProvability.introspection`；原验证矩阵反射已完整填入 |
| 对象一致性句子 $\neg\Box\bot$ 及相对支撑语言的 Π₁ 分类 | [ReducedProvability](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProvability.lean) 的 `consistency`、`consistency_pi1` |
| 任意内部自然数证明码上的实际 MP 构造 | [ReducedProofComposition](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofComposition.lean) 的 `modus_ponens` |

这些结论不假定 $T$ 一致、可靠或其模型的自然数域外部标准。D2 合并内部轨迹，
验证新增 MP 节点和根行，最后由既有强完备性导出普通 Hilbert 推导。
D3 通过实际公式的内部强归纳反射原已检查轨迹。Löb 定理和哥德尔第二不完备定理
仍是后续目标；裸 ZFC 原生证明谓词的可导性条件另需语言及推导传输。

## 内部数码与轨迹反射

继续使用现有 `ObjectNumeralSyntax.condition` 与完整 AST 编码。
其输入和输出是任意内部自然数，不要求能解码为宿主 `Nat`。

| 成果 | 声明与源码 |
| --- | --- |
| 数码图总性与唯一性的实际对象闭句推导 | [PureSourceNumeralTotality](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceNumeralTotality.lean) 中 `PureSourceNumeralSyntax.totalUnique_derives` |
| 数码输出通过当前完整语法图的闭项检查 | [InternalNumeralQuotation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralQuotation.lean) 中 `PureSourceNumeralSyntax.wellFormed_derives`、`quotation_exists_unique`；`graph_term` 还覆盖任意内部上下文长度 |
| 标准输入与既有 AST 编码算法一致 | [PureSourceNumeralTotality](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceNumeralTotality.lean) 中 `PureSourceNumeralSyntax.standard_iff` |
| 固定完整 AST 的非标准自由代入 | [PureSourceSubstitution](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceSubstitution.lean) 中 `PureSourceInstantiation.formula_substitution`、`unary_substitution`；接入当前模式 3 变换图 |
| 数码命名与代入在整个内部 ω 上的实际总性推导 | [InternalNumeralSubstitution](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralSubstitution.lean) 的 `total_derives`；同一个合法闭项数码作为代入表条目 |
| 非标准结论码上的六类节点装配和 MP | [ReducedProofComposition](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofComposition.lean) 的 `codeProof_of_node`、`modus_ponens_code`；保留原证明图与实际语法条件 |
| 内部逻辑公理及存在引入 | [ReducedProofLogicalConstruction](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofLogicalConstruction.lean) 的 `logical_rule`、`exists_introduction`；须提供实际模式 2 实例化证书及正文、项和实例的语法证书 |
| 自由代入与点实例化的同一输出 | [PureSourcePointInstantiation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourcePointInstantiation.lean) 中 `PureSourceInstantiation.unary_point`；抽象后的模式 2 输出等于原公式的模式 3 输出 |
| 无额外语法义务的数码存在引入 | [InternalNumeralProof](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralProof.lean) 的 `instance_wellFormed`、`exists_introduction`；只消费数码图及实例的内部证明 |
| 已证定理的全部内部数码实例 | [InternalNumeralSpecialization](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralSpecialization.lean) 中 `InternalNumeralProof.specialize_values`、`specialize_finite`；任意有限参数数目，旧单参数入口与 MP 复用统一构造 |
| 连续特化保持已代入数码 | [InternalNumeralTransform](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralTransform.lean) 中 `PureSourceNumeralSyntax.graph_transform`；[InternalNumeralParameters](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralParameters.lean) 的 `PureSourceInstantiation.numeral_point`，保持任意内部深度下的合法数码 |
| 任意内部数码可证明属于 ω | [InternalNumeralArithmeticReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralArithmeticReflection.lean) 中 `InternalNumeralReflection.natural`、`natural_derives`；实际可分离公式归纳，零／后继步骤无反射假设 |
| 内部数码零测试的正负反射 | [InternalNumeralZeroReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralZeroReflection.lean) 中 `InternalNumeralReflection.zero`、`nonzero`；两种真值均生成当前证明图接受的内部证明 |
| 任意两个内部数码的相等与不等反射 | [InternalNumeralEqualityRules](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralEqualityRules.lean) 中 `InternalNumeralReflection.equal`；[InternalNumeralEqualityReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralEqualityReflection.lean) 中 `unequal`、`unequal_derives`，对非标准自然数也成立 |
| 内部自然数严格／非严格序的正负反射 | [InternalNumeralOrderReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralOrderReflection.lean) 的 `order`、`weak_order`、`order_derives`；序关系及其否定都生成原证明图接受的内部证明 |
| 任意内部自然数的加乘幂数码求值 | [InternalArithmeticEvaluation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalArithmeticEvaluation.lean) 的 `addition_evaluation`、`multiplication_evaluation`、`exponentiation_evaluation`、`arithmetic_evaluation_derives`；三个运算复用实际公式的内部归纳，没有求值反射假设 |
| Gödel 配对及复合编码项求值 | [InternalPairingEvaluation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPairingEvaluation.lean) 的 `pairing_evaluation`、`pairing_evaluation_derives`；[InternalCodingEvaluation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCodingEvaluation.lean) 覆盖字段列、节点、Horn 表达式和参数化 AST 码项，共用 `binary_term_evaluation` |
| 既定 quotation 的求值证明 | [InternalQuotationEvaluation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalQuotationEvaluation.lean) 的 `quotation_evaluation`；保持原树编码，输出原证明谓词接受的数码等式证明 |
| 复合项原子及逻辑联结词的正负反射 | [InternalAtomicReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalAtomicReflection.lean) 的 `atomic_reflection`；[InternalBooleanReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalBooleanReflection.lean) 的 `boolean_reflection`，数值与内部证明可非标准 |
| 任意内部自然数界的量词反射 | [InternalBoundedTerms](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalBoundedTerms.lean) 的 `bounded_term_reflection`；全称／存在、正／负方向共用界项求值与 `bounded_bundle`，不假定内部区间外部有限 |
| 原验证矩阵的有限轨迹证明装配 | [InternalVerificationTrace](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalVerificationTrace.lean) 的 `finite_verification`；原检查器及局部条件不变，有限骨架及各行内部证明仍是输入 |
| 任意内部数码递归轨迹的正负反射 | [InternalNumeralTraceReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralTraceReflection.lean) 的 `numeral_trace_positive`、`numeral_trace_positive_derives`；[InternalNumeralTraceDecision](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralTraceDecision.lean) 的 `numeral_trace_negative`、`numeral_trace_reflection`；使用原 `ObjectNumeralSyntax.condition` 和原证明图；实际对象公式归纳，无外部有限轨迹或反射假设，支持已求值复合项 |
| 原投影图全部七条规则的内部正反射 | [InternalProjectionReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProjectionReflection.lean) 的 `projection_positive`、`projection_term_positive`、`projection_positive_derives`；索引、输入和原轨迹均可非标准，取尾递归使用实际对象公式归纳 |
| 原一般语法图的内部正反射 | [InternalSyntaxReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSyntaxReflection.lean) 的 `syntax_positive`、`syntax_term_positive`、`syntax_positive_derives`；项、参数列和公式共用实际公式的内部强归纳，覆盖非标准输入与上下文，并保留原检查器规则 |
| 原四种语法变换的内部正反射 | [InternalTransformReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalTransformReflection.lean) 的 `transform_positive`、`transform_term_positive`、`transform_positive_derives`；原 28 条规则共用分层内部强归纳 |
| 原 schema 与传输包图的内部正反射 | [InternalSchemaGraphs](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaGraphs.lean)、[InternalPacketReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPacketReflection.lean)；正文、重命名、表生成、闭句、quotation 转换及传输包的原规则均已反射 |
| verifier 实际 schema／公理查询的内部正反射 | [InternalSchemaQueries](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaQueries.lean) 的 `packet_term_positive`、`axiom_term_positive`、`axiom_query_positive`、`axiom_query_positive_derives`；保留原有界查询和数码，覆盖非标准参数，无查询反射前提 |
| 原逻辑／证明行查询的内部正反射 | [InternalProofRowReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofRowReflection.lean) 的 `logical_term_positive`、`node_term_positive`、`row_term_positive`、`row_named_positive` 及三项 `*_positive_derives`；全部原逻辑公理、六类节点及实际行封装，无局部查询反射假设 |
| 实际检查步骤的局部证明装配 | [InternalCheckedStepReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedStepReflection.lean) 的 `proof_step_values`、`finite_verification_of_links`；局部查询只需真值，原 Horn 连边证明仍须提供 |
| 原证明树任意内部已检查轨迹反射 | [InternalProofTraceReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofTraceReflection.lean) 的 `proof_trace_positive`、`proof_trace_values`、`proof_trace_positive_derives`；覆盖全部原规则与非标准根行，不要求外部骨架或连边证明 |
| 原验证矩阵与完整证明矩阵的数码反射 | [InternalVerificationReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalVerificationReflection.lean) 的 `verification_reflection`、`proof_matrix_reflection`；保留原图、quotation 和自然数 guard |

内部归纳使用最终解释的实际纯公式，并先证明原模型与规范扩张的真值对应。
`checkedRankedAt_agrees` 同时覆盖原 checked 轨迹及其数码实例的可证明性；
两阶段秩证书只依赖原证明树的固定规则表，输入证明码覆盖整个内部 ω。
`proof_trace_positive` 结合已完成的局部行查询正反射，消去了外部有限骨架和连边证明输入。
`verification_reflection` 经 `verificationMatrix_trace` 接回原检查器正文，
`proof_matrix_reflection` 补齐自然数 guard；`ReducedProvability.introspection`
因此给出 $T\vdash\Box\varphi\to\Box\Box\varphi$，无附加反射假设。

有限骨架、单行装配及条件性矩阵装配接口仍可单独调用；它们不是完整轨迹反射的假设。
本次结论是原验证图及其数码实例的正反射，不登记一般负反射或完整真理反射。

## 可复用的基础成果

| 成果 | 实际入口 | 指路表 |
| --- | --- | --- |
| 完整自然数证书往返与可推导性表示 | [ZFC/NatEncode](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/NatEncode.lean)、[ZFC/NatDecode](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/NatDecode.lean) | [证书和对象图](NAT_DECODING.md) |
| 当前 quotation 的具体证明表示与源 Rosser 实例 | [ReducedProofPresentation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofPresentation.lean)、[ReducedNaturalProofPresentation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedNaturalProofPresentation.lean)、[ReducedRosser](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedRosser.lean) | [证书和对象图](NAT_DECODING.md) |
| 有限基使用的 64 个函数、46 个关系的纯定义 | [PureCompletedStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureCompletedStage.lean) | [定义与规格](ELIMINATION.md) |
| 119 条有限基及原无限参数支撑理论的模型验证 | [PureSupportModels](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSupportModels.lean) 的 `support_models` | [逐项公理索引](UNIFIED_VERIFICATION.md) |
| 原 ZFC 像、纯翻译、模型扩张与约化 | [PureZFCModels](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureZFCModels.lean) 的 `models`、`translated_models`、`expands`、`reduction` | [模型与推导](UNIFIED_VERIFICATION.md) |
| 全部内部自然数证明码的实际图对应 | [PureSourceLocalTests](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceLocalTests.lean) 的 `proof_agreement` | [内部模型对应](UNIFIED_VERIFICATION.md) |

一般反向句法保守性未包含在上表结论中。原递归序列族之并在合法递归器下的
ω 全域性仍是独立数学待办。源码核验与可信依赖以
[UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md) 的当前基点为准。
