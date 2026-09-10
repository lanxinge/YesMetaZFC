# 自然数证书与对象表示指路表

## 可计算入口

[ZFC/NatEncode](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/NatEncode.lean)、[ZFC/NatDecode](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/NatDecode.lean) 提供原 `intrinsic_zfc_theory` 上的实际入口：

```lean
intrinsic_zfc_nat_encode : IntrinsicClosedProofCertificate → Nat
intrinsic_zfc_nat_decode : Nat → Option IntrinsicClosedProofCertificate
intrinsic_zfc_nat_check : Nat → SetSentence → Bool
```

| 需要的保证 | 公共声明 |
| --- | --- |
| 接受的闭句有普通推导 | `intrinsic_zfc_nat_check_sound` |
| 恢复整个实际证书 | `intrinsic_zfc_nat_decode_encode` |
| 编码单射 | `intrinsic_zfc_nat_encode_injective` |
| 可推导当且仅当存在被接受的自然数证书 | `intrinsic_zfc_derives_iff_nat_certificate` |

解码保存实际结论和类型正确的证书，覆盖六条核规则。编码沿证书递归，不通过
经典选择从可证性命题抽取证书；检查器不从输入接收理论成员证明。
`none` 只表示该输入不是此格式的合法闭证明，不能推出目标闭句不可证。

## quotation 与公理基

| 需要的接口 | 源码 | 边界 |
| --- | --- | --- |
| 保留完整 AST 的 quotation | [IntrinsicQuotation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/IntrinsicQuotation.lean) 的 `quote`、`unquote_quote`、`quote_injective`、`quote_ne`；[IntrinsicQuotationEvaluation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/IntrinsicQuotationEvaluation.lean) 的 `quote_evaluate` | 十一种公式构造子均保留；使用紧凑树项 |
| 完整公式的实际识别与解码 | [ObjectFormulaSound](YesMetaZFC/Automation/ObjectFormulaSound.lean) 中 `ObjectFormulaSyntax.checked_decode` | 覆盖所有自然数输入，包括失败分支 |
| 当前四种类型化变换、逻辑公理和证明规则 | [ObjectSyntaxTransform](YesMetaZFC/Automation/ObjectSyntaxTransform.lean)、[ObjectLogicalAxiom](YesMetaZFC/Automation/ObjectLogicalAxiom.lean)、[ObjectProofNode](YesMetaZFC/Automation/ObjectProofNode.lean) | 分别连接实际核变换、27 类逻辑公理和六条核规则 |
| 八个固定 ZFC 公理与两个模式 | [BaseAxiomPacketSpec](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/BaseAxiomPacketSpec.lean) 的 `BaseAxiomPacket.presentation` | 精确表示原基础公理像；替换作为派生模式接口存在，不额外加入原证书分支 |
| 与原理论推导等价的完整公理基 | [ReducedAxiomPacket](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedAxiomPacket.lean) 的 `presentation`；[ReducedAxioms](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedAxioms.lean) 的 `derives_iff` | 原 ZFC 像加 119 条有限基；不宣称原无限参数公理成员关系逐值相同 |
| 带上下文与实际结论标注的证明树 | [ProofTreeCode](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ProofTreeCode.lean)、[ReducedProofTree](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofTree.lean) 的 `derives_iff` | 全部六条规则的真实检查器、可靠性与完备性 |
| 固定局部测试到整树对象表示 | [ReducedProofPresentation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofPresentation.lean) 的 `nodeTest`、`presentation`；[ObjectProofNode](YesMetaZFC/Automation/ObjectProofNode.lean) 的 `ofNodeTest` | 要求局部可靠性和全部实际编码的接受完备性，不要求非规范外壳与旧算法逐值相等 |
| 内部自然数码域与 Rosser 装配 | [ReducedNaturalProofPresentation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedNaturalProofPresentation.lean)、[ReducedRosser](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedRosser.lean)、[PureRosserComplete](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) | 当前实例已完成裸 ZFC 支撑消去及任意原模型对应；精确终点见 [UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md) |

旧 `QuineEncoding.quote` 先 Hilbert 化，会合并不同实际 AST；
[SchemaQuotationAudit](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaQuotationAudit.lean) 给出分离、收集模式的实际冲突。旧 `IntrinsicVerifier`、
`IntrinsicSchemaCertificate`、`IntrinsicGraph` 的 Hilbert 格式不能直接充当当前表示。
`ReducedRosser` 只从旧层复用 quotation 无关的 core 与数码成员事实。

## 普通可证明性与内部证明合成

`ReducedProvability.provable` 是现有自然数证明图的存在投影；
`consistency` 定义为不存在矛盾的证明。普通谓词与 Rosser 比较谓词分别保留。
`necessitation`、`distribution` 分别实现 D1、D2，具体入口见 [TROPHIES.md](TROPHIES.md)。

| 调用方需要 | 公共接口与源码 | 保留的边界 |
| --- | --- | --- |
| 内部自然数 Gödel 配对、节点和字段列表单射性 | [PureGodelPairingInversion](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureGodelPairingInversion.lean) 的 `coordinates_unique`；[PureSourceCodingInversion](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceCodingInversion.lean) | 所有坐标显式属于模型内部 ω，不转换为宿主 Nat |
| 内部轨迹合并与插入 | [ObjectTraceComposition](YesMetaZFC/Automation/ObjectTraceComposition.lean)；[PureSourceTraceComposition](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceTraceComposition.lean) 的 `merge`、`insert`、`collect` | 幂集界、前提行成员和全部局部检查保持；轨迹可以外部非有限 |
| 任意自然数参数的 Horn 规则实例 | [PureSourceHornConstruction](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceHornConstruction.lean) 的 `rule_intro` | 自动验证头表达式中的变量界，逐一保留 guards 和前提 |
| 固定字段位置的实际投影轨迹 | [PureSourceProjection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceProjection.lean) 的 `field_node` | 位置及字段列表为语法参数，字段值可以非标准 |
| 原证明根行的结论与节点连边 | [ReducedProofHeaders](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofHeaders.lean) 的 `root_header_code`、`root_header` | 内部结论码不要求是标准 quotation；同时恢复自由变量数、结论字段、结论上界和原节点行 |
| 实际 MP 证明码、局部检查和完整闭包 | [ReducedProofLocalConstruction](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofLocalConstruction.lean) 的 `mpCodeOf`、`mp_local_code`；[ReducedProofComposition](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofComposition.lean) 的 `modus_ponens_code`、`modus_ponens` | 证明和结论均可非标准；保留两侧公式的实际语法检查，原 D2 入口仍可用 |
| 经最终纯翻译传回的内部归纳 | [PureSourceInduction](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceInduction.lean) 的 `induction` | 性质必须是实际公式，且在内部自然数上证明原模型与规范扩张的真值一致；不授权任意外部谓词归纳 |
| 当前数码图的零／后继反演 | [PureSourceNumeralSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceNumeralSyntax.lean) 的 `zero_iff`、`successor_iff` | 只读取内部轨迹根行，前驱证书保留同一内部集合轨迹 |
| 任意内部自然数的唯一数码 | [PureSourceNumeralTotality](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceNumeralTotality.lean) 中 `PureSourceNumeralSyntax.total`、`functional`、`totalUnique_derives` | 对整个内部 ω 成立，使用既有 `ObjectNumeralSyntax.condition`；`standard_iff` 连接现有 AST 算法 |
| 内部项码的参数列与函数应用 | [PureSourceTermConstruction](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceTermConstruction.lean) 的 `arguments_cons`、`arguments_list`、`application` | 上下文长度和项码可非标准；规则表须包含完整项与参数列规则，函数元数保留 |
| 同一个唯一数码的实际闭项证书 | [InternalNumeralQuotation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralQuotation.lean) 中 `PureSourceNumeralSyntax.quotation_exists_unique`、`wellFormed_derives`、`graph_term` | 使用当前逻辑公理检查器共享的 `ObjectFormulaSyntax.rules`；`graph_term` 以带上下文参数的实际公式归纳，覆盖任意内部 bound/free 长度 |
| 固定 AST 的参数化码构造 | [ObjectCodeInstantiation](YesMetaZFC/Automation/ObjectCodeInstantiation.lean) 的 `term`、`arguments`、`formula`；[PureSourceInstantiation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceInstantiation.lean) 的 `original_quote`、`formula_natural` | 只遍历标准语法骨架，槽位码值可非标准；原变量赋值精确恢复当前 quotation |
| 真实变换图上的内部规则实例 | [PureSourceTransformConstruction](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceTransformConstruction.lean) 的 `lookup_list`、`bound_point`、`application`、`binary`、`unary` | guards、前提和编码上界均保留；模式 2 点代入与模式 3 自由代入不混用 |
| 非标准数码代入总性 | [PureSourceSubstitution](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceSubstitution.lean) 中 `PureSourceInstantiation.formula_substitution`；[InternalNumeralSubstitution](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralSubstitution.lean) 的 `total_derives` | 模式 3 的固定公式代入；自然数输出和实际轨迹由本层提供，数码实例的语法证书见下行；未证明变换图一般唯一性 |
| 同一证明图的内部结论参数 | [ReducedProofCodeSemantics](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofCodeSemantics.lean) 的 `CodeProof`、`codeProof_trace`、`codeProof_quotation` | 直接解释原二元模板；不是替代的证明谓词 |
| 六类证明节点共用的内部装配 | [ReducedProofComposition](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofComposition.lean) 的 `codeProof_of_node` | 当前闭证明根要求自由变量数为零，子节点轨迹和完整局部测试必须成立 |
| 实际逻辑模式与存在引入 | [ReducedProofLogicalConstruction](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofLogicalConstruction.lean) 的 `logical_rule`、`of_logical_code`、`exists_introduction` | 原二十七类公理表；存在引入显式保留正文、项、实例语法及模式 2 变换条件 |
| 模式 2/3 共用的固定 AST 变换 | [PureSourceMappedTransform](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceMappedTransform.lean) 中 `PureSourceInstantiation.formula_mapped_transform`；[PureSourcePointInstantiation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourcePointInstantiation.lean) 的 `unary_point` | 变量像的合同覆盖全部 binder 深度；单槽抽象后的点实例化与自由代入共用同一个输出码 |
| 固定 AST 实例的全部语法证书 | [PureSourceInstantiationSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceInstantiationSyntax.lean) 的 `formula_wellFormed`、`original_wellFormed` | 自由槽位的项码须在所需深度合法；数码的此项义务已由 `graph_term` 证明 |
| 数码实例证明到存在句证明 | [InternalNumeralProof](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralProof.lean) 的 `exists_introduction` | 给出同一数码图及实例内部证明即可；正文、项、实例语法和模式 2 条件均自动消去 |
| 已证定理的非标准数码特化 | [InternalNumeralSpecialization](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralSpecialization.lean) 中 `InternalNumeralProof.specialize_values`、`specialize_finite`、`values_modus_ponens` | 覆盖任意有限参数数目；`specialize_finite` 只要求实际自由槽位的数码证书。旧单参数 `specialize` 与 MP 入口复用统一构造 |
| 已代入数码在后续变换下不变 | [InternalNumeralTransform](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralTransform.lean) 中 `PureSourceNumeralSyntax.graph_transform` | 使用实际可分离公式归纳，覆盖任意内部模式、深度与参数，要求模式小于四 |
| 多参数环境的连续点实例化 | [InternalNumeralParameters](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralParameters.lean) 中 `PureSourceInstantiation.numeral_point`、`numeral_wellFormed` | 尾部槽位可为不同的非标准数码；源端与目标端共用推广后的 `formula_mapped_transform` |
| 可分离的数码反射归纳 | [InternalNumeralReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralReflection.lean) 的 `numeral_induction`、`atNumber_agrees` | 实际对象公式包含原数码图和原可证明性图；最终阶段对应覆盖非标准结论码 |
| 自然数 guard 的实际反射 | [InternalNumeralArithmeticReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralArithmeticReflection.lean) 的 `natural`、`natural_derives`、`of_natural_derives` | 零和后继证明码均已构造；还可消去已证源定理的自然数前提 |
| 零测试的正负反射 | [InternalNumeralZeroReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralZeroReflection.lean) 的 `zero`、`nonzero` | 真值决定生成等于零或不等于零的内部证明，非零分支反演实际数码图 |
| 二元相等／不等反射 | [InternalNumeralEqualityRules](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralEqualityRules.lean) 的 `equal`、`successor_inequality`；[InternalNumeralEqualityReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralEqualityReflection.lean) 的 `unequal`、`unequal_derives` | 任意两个内部自然数；不等式反射的归纳性质全称覆盖第二个数及两个数码，已证明最终阶段对应 |
| 严格序与非严格序的正负反射 | [InternalNumeralOrderReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralOrderReflection.lean) 的 `order`、`weak_order`、`order_derives` | 非严格序按 x∈S(y) 表示；右参数内部归纳，后继步消费等式与不等式反射 |
| 内部加、乘、幂数码求值 | [InternalArithmeticEvaluation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalArithmeticEvaluation.lean) 的 `addition_evaluation`、`multiplication_evaluation`、`exponentiation_evaluation`、`arithmetic_evaluation_derives` | 生成运算项等于结果数码的实际证明；二元项共用 `evaluation_induction`，依次用加法构造乘法、乘法构造幂 |
| 复合项求值的统一组合 | [InternalTermComposition](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalTermComposition.lean) 的 `binary_term_evaluation`；[ObjectCodeSubstitution](YesMetaZFC/Automation/ObjectCodeSubstitution.lean) 的 `term_mapped` | 子项证明与原始运算证明经有限参数特化和 MP 合成；任意有限自由上下文，无需重建编码 AST |
| Gödel 配对及编码项求值 | [InternalPairingEvaluation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPairingEvaluation.lean) 的 `pairing_evaluation`、`pairing_evaluation_derives`；[InternalCodingEvaluation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCodingEvaluation.lean) | 配对两分支消费序反射和复合算术求值；覆盖字段列、节点、Horn 表达式及参数化项／参数列／公式码项 |
| 原结构 quotation 的求值 | [InternalQuotationEvaluation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalQuotationEvaluation.lean) 的 `quotation_evaluation`、`tree_term_evaluation` | 保留原节点与字段顺序；生成 quotation 项等于其结果数码的实际证明，未改写为另一种 quotation |
| 复合项原子判断与逻辑组合 | [InternalAtomicReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalAtomicReflection.lean) 的 `atomic_reflection`；[InternalBooleanReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalBooleanReflection.lean) 的 `boolean_reflection`、`negation_reflection`、`reflection_of_iff` | 等式、成员及全部命题联结词的正负反射，复用子项数码求值 |
| 任意有限参数的量词见证 | [InternalQuantifierReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalQuantifierReflection.lean) 的 `exists_values`、`forall_counterexample` | 实际数码点实例化及原存在公理，覆盖内部自然数见证 |
| 自然数界的全称／存在正负反射 | [InternalBoundedReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalBoundedReflection.lean) 的 `bounded_forall_reflection`；[InternalBoundedExistence](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalBoundedExistence.lean) 的 `bounded_exists_reflection`；[InternalBoundedTerms](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalBoundedTerms.lean) 的 `bounded_term_reflection` | 界可为已求值的算术／编码复合项；`bounded_bundle` 使用实际公式归纳，有限参数表示及最终阶段对应均已消去 |
| 固定有限轨迹骨架的内部证明 | [InternalTraceReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalTraceReflection.lean) 的 `finite_trace_values`、`checked_trace_values`；[InternalVerificationTrace](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalVerificationTrace.lean) 的 `finite_verification`、`verificationMatrix_trace` | 由逐行内部证明装配原幂集量词正文，并逐字接回原验证矩阵；此有限骨架接口的输入条件保留 |
| 含量词图谓词的复合项／数码传输 | [InternalPredicateTransport](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPredicateTransport.lean) 的 `predicate_transport`；[ObjectCodeSubstitution](YesMetaZFC/Automation/ObjectCodeSubstitution.lean) 的 `formula_mapped_of_depth`、`formula_substituteFree` | 覆盖全部 binder 深度，正负公式及两个传输方向共用原模板同余 |
| 任意内部数码递归轨迹的正负反射 | [InternalNumeralTraceReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralTraceReflection.lean) 的 `numeral_trace_positive`、`numeral_trace_positive_derives`；[InternalNumeralTraceDecision](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralTraceDecision.lean) 的 `numeral_trace_negative`、`numeral_trace_reflection` | 使用原 `ObjectNumeralSyntax.condition` 和原证明图；实际对象公式归纳，无外部有限轨迹或反射假设，支持已求值复合项 |
| Horn 根行反演与统一内部规则证明 | [PureSourceHornElimination](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceHornElimination.lean) 的 `rule_cases`；[InternalHornReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalHornReflection.lean) 的 `horn_rule_values`、`horn_term_transfer` | 参数自动命名，守卫由原子反射证明；有限规则前提复用任意内部集合轨迹，不需要全图反射假设 |
| 原投影图的内部正反射 | [InternalProjectionReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProjectionReflection.lean) 的 `projection_get_positive`、`projection_positive`、`projection_term_positive`、`projection_positive_derives` | 全部七条规则、任意非标准索引与非规范外壳；按实际 `getAt` 公式作内部归纳，保留原局部投影图 |
| 原一般语法图的内部正反射 | [InternalSyntaxReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSyntaxReflection.lean) 的 `syntax_at_positive`、`syntax_positive`、`syntax_term_positive`、`syntax_positive_derives` | 项、参数列和全部公式构造子按输入码同时强归纳；支持非标准上下文、元数与原集合轨迹，最终阶段对应已证明 |
| 任意内部结论码的最终阶段对应 | [PureSourceLocalTests](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceLocalTests.lean) 的 `codeProof_agreement` | 输入证明码和结论码均属内部 ω；不要求结论是外部标准 quotation |
| 原四种语法变换的内部正反射 | [InternalTransformReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalTransformReflection.lean) 的 `transform_positive`、`transform_term_positive`、`transform_positive_derives` | 原 28 条规则；查表与语法遍历分层，覆盖非标准模式、上下文与输入，不增加反射前提 |
| schema 图及传输包的内部正反射 | [InternalSchemaGraphs](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaGraphs.lean) 的正文、重命名、表生成、闭合及 quotation 转换入口；[InternalPacketReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPacketReflection.lean) 的 `packet_positive` | 原规则、原集合轨迹；token 正尾的下降来自 `affine_bounds`，中间参数保留原界 |
| 完整 schema 与公理行查询的内部正反射 | [InternalSchemaReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaReflection.lean) 的 `packet`、`axiomCondition`；[InternalSchemaQueries](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaQueries.lean) 的 `packet_term_positive`、`axiom_query_positive`、`axiom_query_positive_derives` | 覆盖分离、收集、替换的原有界查询和有限公理表，接入实际 `ReducedAxiomNumber.localTest`；只登记正反射 |
| 原逻辑公理、证明节点与行查询的内部正反射 | [InternalProofQueries](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofQueries.lean) 的 `logical`、`currentNode`、`currentRow`；[InternalProofRowReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofRowReflection.lean) 的 `logical_positive_derives`、`node_positive_derives`、`row_positive_derives` | 覆盖 27 类逻辑公理、6 类节点及零码／零标签／其他标签行封装；实际参数和外壳可非标准，不要求额外查询反射假设 |
| 原递归连边与局部行证明装配 | [InternalCheckedStepReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedStepReflection.lean) 的 `proof_step_values`、`finite_verification_of_links` | 局部真值自动产生原查询的内部证明；仍须原 Horn 连边证明，有限验证入口仍须外部固定的骨架 |
| 任意内部 checked 轨迹的反演与构造 | [PureSourceCheckedConstruction](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceCheckedConstruction.lean) 的 `rule_cases_bounds`、`rule_intro_bounds`；[InternalCheckedReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedReflection.lean) 的 `checked_rule_bounded_values` | 反演保留原局部查询；固定规则的前提重用内部集合轨迹，构造时合并集合并插入头行 |
| 原证明树的分层内部反射 | [InternalCheckedRanking](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedRanking.lean) 的 `checked_valid_positive`；[InternalProofTraceReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofTraceReflection.lean) 的 `proof_trace_positive` | `ObjectCheckedReflection.proof_valid` 核验十二条原规则，内部强归纳正文具有最终阶段对应；无外部标准性、有限性或良基假设 |
| 原矩阵反射与完整 D3 | [InternalVerificationReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalVerificationReflection.lean) 的 `verification_reflection`、`proof_matrix_reflection`；[ReducedIntrospection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedIntrospection.lean) 的 `ReducedProvability.introspection` | 原验证图、数码实例及 quotation 不变；局部查询、骨架和连边反射义务全部消去 |

`proofMatrix_split` 保持原矩阵逐字分解，`matrix_of_verification` 通过自然数反射补回 guard。
`verificationMatrix_trace` 精确恢复原 checked 轨迹；`proof_trace_positive` 已覆盖其任意内部见证，
`verification_reflection` 将真值变成原数码实例的内部证明，最后由既有存在引入装配 D3。
模型内部自然数、证明码及轨迹不必在外部标准、有限或良基。

数码命名、参数化 AST 码项、语法／变换／schema 查询与实际行封装均复用既有接口。
`checkedRankedAt_agrees` 核验包含原轨迹和数码可证明性的实际归纳公式；
节点阶段按子证明编码下降，根阶段进入节点阶段。
当前 Δ₀ 图中的幂集界由内部集合轨迹反演、合并和插入直接处理，未将它改写为外部列表，
也未调用额外的一阶算术 Σ₁ 完备性。

## 模式表示的公共接口

下表的正负表示使用普通 `Derives`；拒绝结论覆盖任意错误候选输出及对象界内见证，
不只覆盖宿主已经解码的数据。这里的 Δ₀ 分类相对于扩展支撑语言。

| 调用方要连接的步骤 | 实际接口与源码 | 保留的义务 |
| --- | --- | --- |
| 标签、元数、参数叶子 | [SchemaEnvelope](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaEnvelope.lean) | 原分离／收集解码器的完整外壳 |
| 正文项与变量作用域 | [SchemaTerm](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaTerm.lean)、[SchemaBodyDerives](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaBodyDerives.lean)、[SchemaObjectGraph](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaObjectGraph.lean) 的 `Body.condition` | 实际 Project 项及正文识别的成功／失败 |
| 自然数传输包到原始树 | [NatPacketLink](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/NatPacketLink.lean) | 实际 `NatPacket.decode`，包含非法包和错误候选树 |
| 正文重命名 | [SchemaRenameDerives](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaRenameDerives.lean)、[SchemaObjectGraph](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaObjectGraph.lean) 的 `Rename.condition` | 实际有限表算法，任意错误输出，六个具体位置 |
| 固定模式模板 | [SchemaTemplate](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaTemplate.lean)、[SchemaTemplateDerives](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaTemplateDerives.lean) | 三种模板；槽位装配不自行验证正文或执行对象重命名 |
| 任意长度参数闭合 | [SchemaClosure](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaClosure.lean) | 精确连接实际模式闭句，无固定量词层数上限 |
| 六张重命名表与中间码连接 | [SchemaTable](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaTable.lean)、[SchemaJoinGraph](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaJoinGraph.lean)、[SchemaJoinDerives](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaJoinDerives.lean) | 三张表、三个正文、核心的实际存在连接 |
| Project 树到当前核 quotation | [KernelQuotation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/KernelQuotation.lean)、[SchemaKernelJoin](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaKernelJoin.lean) | 使用正式交换律，不把两种树码直接认作相等 |
| 完整原始包与实际结论 | [SchemaPacketSpec](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaPacketSpec.lean)、[SchemaPacketDerives](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaPacketDerives.lean)、[SchemaConclusion](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaConclusion.lean) | `SchemaPacket.actual_positive_number`、`actual_negative` 与精确目标 AST 比较，覆盖全部输入分支 |

`NatPacket.encode` 是传输编码，`treeValue` 是内部树值，当前公式 quotation 又有
自己的语法含义；只通过上表正式桥梁传输，不能混用。

### 模板与位置规范

`SchemaTemplate` 标签 0、1、2 分别构造分离、收集、替换核心，使用一个、两个、
三个已经重命名的正文槽。`run_isSome` 精确连接正文检查，非法正文不会被装配修复。
参数数为 `n`，下表的 `j` 遍历 `j < n`：

| 正文位置 | 源深度 | 目标深度 | 索引表 |
| --- | --- | --- | --- |
| 分离 | `n+1` | `n+3` | `[0] ++ [j+3]` |
| 收集前件 | `n+2` | `n+3` | `[0,1] ++ [j+3]` |
| 收集像集 | `n+2` | `n+4` | `[0,1] ++ [j+4]` |
| 替换第一输出 | `n+2` | `n+3` | `[1,2] ++ [j+3]` |
| 替换第二输出 | `n+2` | `n+3` | `[0,2] ++ [j+3]` |
| 替换像集 | `n+2` | `n+4` | `[1,0] ++ [j+4]` |

### 原参数公理的兼容接口

[SyntaxCanonical](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SyntaxCanonical.lean)、[SyntaxParameters](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SyntaxParameters.lean) 提供完整类型化项的规范解码和参数列往返。
[SupportParameterDerives](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SupportParameterDerives.lean) 的 `SupportParameter.positive`、`negative` 识别参数证书
合法性；仅凭项数不能区分相同元数的不同公理结论。

| 公理族 | 原证书中项的顺序 |
| --- | --- |
| domain、range、converse | relation |
| cartesianProduct | left、right |
| composition | first、second |
| identity、inductiveCore | source |
| mappingCollection | source、target |
| indexOrder | sourceRelation、sourceCarrier、targetRelation、targetCarrier |
| powerSetBijection | natural |
| symmetricDifference | left、right |

参数外壳为 `N(0; L(freeCount), spine)`；项链为 `N(0; term, rest)`，末尾 `L(0)`。
项的束缚上下文为空，自由上下文由外壳指定。
[SyntaxSubstitution](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SyntaxSubstitution.lean)、[SyntaxInstantiation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SyntaxInstantiation.lean) 实现防捕获代入与实际自由变量抽象；
全称闭合不能只在原始树外添加量词。

[SupportRealization](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SupportRealization.lean) 的 `assemble_eq`、`assemble_quote`、`run_eq_actual`、
`packet_eq_actual` 连接模板、代入、闭合、实际解码结论与内层参数包。
这些是计算层和交换定理，尚不构成原 11 类无限参数公理及全部外层 union 路径的
统一对象表示。该兼容工作不阻塞已完成的有限基路线和裸 ZFC Rosser 实例。

## 版本 1 数据包

宿主传输格式由 `ProofT.NatPacket` 定义，与旧 `ProofCode` 配数格式分别命名。
目前没有声明两者相同，也没有把旧对象图直接用于新格式。

1. 原始有限树为 `Tree.node tag children`，标签与子树数量均为自然数。
2. token 顺序为版本号 `1`，随后先序遍历每个节点的「标签、子树数、各子树」。
3. 每个 token 使用规范 unsigned LEB128：每字节低七位是数值位；最高位表示后续字节。
4. 若字节列为 `b₀,…,bₖ₋₁`，输入自然数为 `Σᵢ bᵢ·256ⁱ + 256ᵏ`。
   最高位字节 `1` 是终止标记。解码必须恰好消费全部数据。

`NatPacket.decode_encode` 已证明任意有限数据树的传输往返；
`NatEncode.tree_roundtrip` 证明全部六条规则的证书往返，二者组合为自然数往返定理。截断、尾随 token、未知版本和非规范 varint 均拒绝。
字节解析按自然数值递减，树 token 解析燃料取自输入长度；语法和证明解码沿有限子树
直接递归。这些递归都没有固定的证明长度或公式级别上限。

下表以 `N(t; x₁,…,xₙ)` 表示节点，以 `L(n) = N(n;)` 表示数值叶子。
这只是本页的数据记法，不是新增对象语言符号。

## 项、公式与替换

上下文为 `L(n)`，表示 `n` 个唯一排序 `SetSort.set`。
函数与关系编号固定为 `SyntaxDecode.functionSymbols`、`relationSymbols` 数组中的零基位置；
当前分别有 76 与 55 个符号。参数数目严格由 `signature` 检查。

| 项 | 树 |
| --- | --- |
| 束缚变量 | `N(0; L(index))` |
| 自由变量 | `N(1; L(index))` |
| 函数应用 | `N(2; L(symbol), argument₁, …)` |

变量索引从上下文头开始，必须小于对应上下文长度。替换参数列为
`N(0; term₁, …)`，长度必须恰好等于源自由上下文长度；各项在目标上下文中解码。

| 公式标签 | 参数 |
| --- | --- |
| 0、1 | 无参数，分别为假、真 |
| 2 | 关系编号叶子及符合签名的项参数列 |
| 3 | 两个项：相等 |
| 4 | 一个公式：否定 |
| 5、6、7、8 | 两个公式：合取、析取、蕴涵、双条件 |
| 9、10 | 一个公式：全称、存在；解析正文时增加一个束缚变量 |

## 公理证书

顶层 `N(0; zfc)` 是 ZFC 公理像，`N(1; support)` 是原支撑公理理论。

ZFC 固定标签 `0,…,7` 依次为外延、空集、配对、并集、幂集、无穷、正则、选择，
均不带参数。`N(8; L(n), body)` 是分离 schema，`N(9; L(n), body)` 是收集 schema。
它们分别在束缚深度 `n+1`、`n+2` 解码，并检查 `FreeClosed`。

Project schema 项仅允许 `N(0; L(index))` 形式的有效束缚变量。
Project 公式标签 `0、1、4,…,10` 与上表一致，`2` 接收两个项表示成员关系，
`3` 接收两个项表示外延相等，`11` 接收两个项表示子集。

支撑公理严格沿 `IntrinsicAxiomCertificate` 的呈现结构解析：

| 呈现 | 证书树 |
| --- | --- |
| `singleton` | `L(0)` |
| `union` 左、右分支 | `N(0; child)`、`N(1; child)` |
| `insert` | 与 `union (singleton …) …` 相同 |
| `indexed` | `N(0; index, child)`；先解析索引，再解析该索引对应的证书 |

参数化分离族的索引依次是自由上下文和该族全部项参数；项均在该上下文中解析。
支撑呈现层均有对应的可计算解码函数，包括嵌套 `insert` 的各固定公理。

## 逻辑公理与推导规则

逻辑公理节点的标签按 `HilbertBaseAxiom` 构造子顺序固定。

| 标签 | 构造子 | 参数 |
| --- | --- | --- |
| 0 | implication_distribution | 三个公式 |
| 1 | self_implication | 一个公式 |
| 2 | weakening | 两个公式 |
| 3 | contradiction | 两个公式 |
| 4 | classical | 一个公式 |
| 5 | explosion | 两个公式 |
| 6 | case_analysis | 两个公式 |
| 7 | truth_intro | 无 |
| 8 | falsum_elimination | 一个公式 |
| 9、10 | negation_intro、negation_elimination | 一个公式 |
| 11 | conjunction_intro | 两个公式 |
| 12、13 | conjunction_elim_left、conjunction_elim_right | 两个公式 |
| 14、15 | disjunction_intro_left、disjunction_intro_right | 两个公式 |
| 16 | disjunction_elimination | 三个公式 |
| 17 | biconditional_intro | 两个公式 |
| 18、19 | biconditional_elim_left、biconditional_elim_right | 两个公式 |
| 20 | forall_specialization | 一个新增束缚变量下的正文、实例项 |
| 21 | forall_distribution | 两个新增自由变量下的公式 |
| 22 | vacuous_forall | 当前自由上下文的公式 |
| 23 | exists_introduction | 一个新增束缚变量下的正文、实例项 |
| 24 | exists_elimination | 新增自由变量下的正文、当前自由上下文的结论 |
| 25 | equality_substitution | 两个项、一个新增束缚变量下的正文 |
| 26 | equality_reflexivity | 一个项 |

证明树在给定自由上下文中递归解析；公开自然数入口从空上下文开始。

| 规则标签 | 参数及检查 |
| --- | --- |
| 0 | 逻辑公理树 |
| 1 | 顶层理论公理证书树 |
| 2 | 前提证明、蕴涵证明；前提结论必须等于蕴涵左端 |
| 3 | 新增一个自由变量下的证明；输出全称一般化 |
| 4 | 当前上下文的目标公式、增大上下文中的证明；后者结论必须等于目标的 `weakenFree` |
| 5 | 源上下文、替换参数列、源上下文的证明；输出统一替换后的结论 |

所有多余或缺失参数、未知标签、非法作用域以及规则连接错误均返回 `none`。
公式连接检查使用已有结构码的可计算相等判定及其单射定理。

## 核验

格式往返、检查器可靠性与完备性、实际解码器一致性和对象正负表示由上述通用定理
保证。执行 `lake --wfail build` 和 `bash scripts/check-all.sh` 检查正式源码；
不另设只重复这些定理的枚举样本模块。入口从
`YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory` 导出。
当前源码核验与既有可信依赖边界统一见 [UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md)。
