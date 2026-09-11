# 证明基础设施指路表

按调用方要消除的证明义务查表。这里记录可复用接口与适用条件；
已完成计划的实施过程、逐轮行数和耗时记录由 Git 历史保存。
裸 ZFC 与编码接口分别见 [ELIMINATION.md](ELIMINATION.md)、[NAT_DECODING.md](NAT_DECODING.md)。

## 元数学调用入口

| 调用方要完成的工作 | 先用的接口 | 保留的合同 |
| --- | --- | --- |
| 从原证明谓词取得 D1–D3 | [ReducedProvability](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProvability.lean)、[ReducedDerivability](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedDerivability.lean)、[ReducedIntrospection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedIntrospection.lean) | 原完整 AST quotation 和任意内部自然数证明码；反射链见本页下文 |
| 复用 Löb、哥二或 Tarski 的一般逻辑推导 | [Loeb](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Loeb.lean)、[SecondIncompleteness](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SecondIncompleteness.lean)、[Tarski](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Tarski.lean) | 通用层显式消费其推导条件；具体实例中的固定点已有构造 |
| 把句子或开放公式的推导传回裸 ZFC | [PureSentenceTransfer](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSentenceTransfer.lean)、[PureOpenTransfer](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureOpenTransfer.lean) | 保留原模型对应和自由参数环境；无闭项时使用开放完备性 |
| 直接调用裸 ZFC 的可证明性、Löb 与哥二 | [PureProvability](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureProvability.lean)、[PureLoeb](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLoeb.lean)、[PureSecondIncompleteness](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSecondIncompleteness.lean) | 使用原检查器的纯语言表示，不替换证明编码 |
| 构造最终纯公式自身编码的固定点 | [PureQuotation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureQuotation.lean)、[PureFixedPoint](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFixedPoint.lean) | 有限纯数码公式绑定编码槽；参数保留为自由变量 |
| 排除带参数的纯真值定义 | [PureTarski](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTarski.lean) | 全部相同参数上下文的纯公式；编码不随赋值改变 |

最终结论及其前提集中在 [TROPHIES.md](TROPHIES.md)，可信依赖和验证范围集中在
[UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md)。

## 公式和模板的闭合性

集合论公式缩写定义后使用 `derive_free_closed f`，生成普通定理 `f_freeClosed` 并注册为
`simp` 规则。实现见 [DeriveFreeClosed](YesMetaZFC/Automation/DeriveFreeClosed.lean)：
它保留原构造的全部参数，只为项、参数向量和公式输入添加闭合性前提，展开该缩写一层，
再组合已有合同。生成证明必须通过 Lean 内核；无法完成时构建失败。
`OrderedPairConvention.code_freeClosed` 和 `BinarySchema.instantiate_freeClosed` 是
编码及模板代入的边界合同，任意有序对约定及任意参数数量均保留。

[Hierarchy/Syntax](YesMetaZFC/SetTheory/Definitional/Project/Hierarchy/Syntax.lean) 的
`UnarySchema`、`BinarySchema` 在构造时自动填充 `freeClosed`，`Delta0` 模板继承同一检查。
常规模板只写 `body`；专用公式先派生自身合同。证书仍在结构中，调用者复用 `.freeClosed`，
不重复展开函数、序数或基数定义。原 `Formula` 仍允许自由变量，只有模板要求闭合。
闭合性自动化使用 `simp -implicitDefEqProofs`，保留侧条件的显式证明，避免 Lean 4.33.1
在较低透明度下无法赋值简化后的证明；此选项不设为全局设置。

全称闭包的语义复用 [ModelClosure](YesMetaZFC/Automation/ModelClosure.lean) 的
`close_of_curried`，直接逐变量 `intro`，由 `Curried.apply` 统一接回任意排序的 `Values`。
参数代入后的环境等式复用 [RelationalEnvironment](YesMetaZFC/Automation/RelationalEnvironment.lean)
的 `pullback_arguments` 和 `pullback_free_arguments`。

## 理论包含与最小支撑

[TheoryInclusion](YesMetaZFC/Automation/TheoryInclusion.lean) 的
`derive_theory_subset weak ⊆ strong` 在理论组合边界生成普通包含定理，默认名称为
`weak_subset_strong`，可用 `=> name` 指定名称。`private`、文档注释、`sentence` 和
`hSentence` 命名参数均保留。调用方仍可直接使用这些已检查的定理。

`theory_inclusion` 沿理论的 `union`、`insert` 和别名寻找包含路径；源理论为并时，
两个分支都必须包含在目标中。搜索缓存已访问节点，只展开理论谓词，不展开公理正文。
它生成假设、析取引入／消去或空理论消去的普通证明，不负责数学推导或模型满足性。
若 `have` 尚未确定结果理论，用 `show Theory.Extends strong weak from by theory_inclusion`
显式固定边界；任意支撑 `S` 仍须先给出相应的 `S.contains_*` 合同。

有限序列的最小支撑由 `finite_sequence_support_instance` 统一组装；算术联合理论直接
弱化这一实例，再补其无穷和配数合同。ZFC 幂集包含统一使用
`intrinsic_zfc_contains_power`，不在每个证明消费者重新复制包含链。

## 有限公理基的模型满足

[FiniteBasisModels](YesMetaZFC/Automation/FiniteBasisModels.lean) 的
`finite_basis_models [h₁, …, hₙ]` 装配显式的 `Theory.Models ℳ basis.theory` 目标。
证据必须是同一模型中的闭句语义或已验证子基；合取证据可拆分，子基沿 `singleton`、
`insert`、`union`、`congr` 和别名组合。命名子基缓存为普通内核定理，不展开公理列表，
也不搜索或补造缺失的数学证据。实际调用见 `ZFC/PureSupportModels.support_models`。
参数分离族仍由闭模板的模型证明及 `FiniteAxiomBasis.models_iff` 接回原理论。

## 语法、替换与 Quine

| 调用方需要 | 公共接口与源码 | 使用边界 |
| --- | --- | --- |
| 项与参数列的共同结构归纳 | [Logic/Syntax](YesMetaZFC/Logic/Syntax.lean) 的 `Arguments.listRec`；[HenkinEmbedding](YesMetaZFC/Logic/FirstOrder/HenkinEmbedding.lean)、[HenkinConservativity](YesMetaZFC/Logic/FirstOrder/HenkinConservativity.lean)、[HenkinWitnessSupport](YesMetaZFC/Logic/FirstOrder/HenkinWitnessSupport.lean) 的相互递归和往返证明 | 保留排序、变量上下文及环境；不另造两套完整递归 |
| 类型化槽位代入与复合 | [Derivation/Substitution/Algebra](YesMetaZFC/Logic/FirstOrder/Derivation/Substitution/Algebra.lean) 的 `postcompose`、`map_cons` 和弱化尾映射接口 | 模板实例只提供参数列，避免按元数复制替换证明 |
| 任意长度存在见证块 | [QuantifierBlock](YesMetaZFC/Logic/FirstOrder/Derivation/QuantifierBlock.lean) 的 `Arguments.substitutionWith`、`Formula.existsFreePrefix`、`Derives.existsFreePrefix_intro` | 列表头对应最内层见证；保留外部自由参数与任意排序 |
| Hilbert 编译像归纳 | [Hilbert/Translation](YesMetaZFC/Logic/FirstOrder/Hilbert/Translation.lean) 的 `Formula.hilbertize_induction` | 五种原始构造统一处理派生联结词；不把 Hilbert quotation 当作完整 AST 编码 |
| quotation 公式闭包 | [QuotationInduction](YesMetaZFC/Automation/QuotationInduction.lean) 的 `FormulaClosure` | 可把码域事实并入归纳谓词；真实深度结论由 `*_of_depth` 实例化 |
| 四种 Quine 变换的 shape 装配 | [TransformStructuralCorrectness](YesMetaZFC/Logic/FirstOrder/FormalSystem/QuineEncoding/TransformStructuralCorrectness.lean) 的 `syntax_transform_*_shape` | 声明在 `QuineEncoding` 命名空间；任意目标理论、空自由上下文；常量是附带内部 ω 成员证明的任意闭项 |
| Quine 的 scope、深度与总码域 | [QuineEncoding/StructuralCorrectness](YesMetaZFC/Logic/FirstOrder/FormalSystem/QuineEncoding/StructuralCorrectness.lean)、[FormulaStructuralCorrectness](YesMetaZFC/Logic/FirstOrder/FormalSystem/QuineEncoding/FormulaStructuralCorrectness.lean)、[FormulaTransformStructuralCorrectness](YesMetaZFC/Logic/FirstOrder/FormalSystem/QuineEncoding/FormulaTransformStructuralCorrectness.lean) | shape 接口不替代这些义务；先固定操作码、深度、变量位置及替换项 |
| 共同 guard 下的命题等价 | [FirstOrder/Metatheory/Propositional](YesMetaZFC/Logic/FirstOrder/Metatheory/Propositional.lean) 的 `guarded_conj_congr_m` | 保留原 guard，不通过增强调用方前提缩短证明 |
| 当前完整公式的单射 quotation | [IntrinsicQuotation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/IntrinsicQuotation.lean) 的 `unquote_quote`、`quote_injective`、`quote_ne` | 保留全部十一种构造子；紧凑结构项不展开为巨大一元 numeral |

[Substitution/Basic](YesMetaZFC/Logic/FirstOrder/Derivation/Substitution/Basic.lean) 的
`Term`、`Arguments`、`Formula.renameMapped_eq_substituteMapped` 同时覆盖任意 bound/free
重命名。复合操作先用 `substituteMapped_comp` 合并，再按变量像作函数外延；
不为两层、三层弱化或闭包往返重新遍历项和公式。
`Formula.substituteMapped_abstractFreeTop_lift` 保留任意替换与上下文，统一自由槽抽象的
交换律；全称、存在量词只接各自构造子。公式弱化后的尾映射合同位于 `Substitution/Algebra`。
这些是普通内核定理，不改变 AST 执行器、闭上下文嵌入算法或原定理的适用范围。

含量词公式的参数化码与类型化代入交换，复用
[ObjectCodeSubstitution](YesMetaZFC/Automation/ObjectCodeSubstitution.lean) 的
`formula_mapped_of_depth` 与 `formula_substituteFree`。自由重命名复用同一公式遍历，
binder 骨架复用 `SyntaxTransform.boundLift` / `freeLift`。图谓词的数码同余消费
[InternalPredicateTransport](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPredicateTransport.lean) 的 `predicate_transport`。

Horn 图的内部反射先复用 [PureSourceHornElimination](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceHornElimination.lean)
的 `rule_cases` 反演原集合轨迹，再用 [InternalHornReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalHornReflection.lean)
的 `horn_rule_values` 装配实际规则证明；不为每条规则重复数码命名、项求值或守卫反射。
[InternalProjectionReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProjectionReflection.lean) 提供非标准索引归纳的完整实例。
[InternalSyntaxReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSyntaxReflection.lean) 提供项、参数列和公式的同时强归纳实例。
[PureSourceStrongInduction](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceStrongInduction.lean) 的 `strong_induction` 只对具有最终阶段对应的实际正文
使用有界全称归纳；[PureSourceSyntaxRank](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceSyntaxRank.lean) 的 `rule_ranked` 和 `rank_unique`
保证递归按输入语法码下降，量词下的上下文增长不进入秩。

分层递归图复用 [InternalHornRanking](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalHornRanking.lean) 的 `horn_valid_positive`：
[SchemaReflectionPlans](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaReflectionPlans.lean) 和 [ObjectTransformRanking](YesMetaZFC/Automation/ObjectTransformRanking.lean)
只提供原规则的有限形状／阶段证书，同层使用具有最终阶段对应的实际公式作内部强归纳。
有隐含中间参数的规则使用 `rule_cases_bounds`、`horn_rule_bounded_values`，保留原量词界。
[InternalPacketReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPacketReflection.lean) 的非结构下降由 [PureSourcePacketBounds](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourcePacketBounds.lean) 的 `affine_bounds` 给出。

正向查询的组合使用 [InternalPositiveFormula](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPositiveFormula.lean) 的 `Positive`、`Evaluates`、`instantiate`，
及 [InternalPositiveQuantifiers](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPositiveQuantifiers.lean) 的 `boundedExists`、`quantify`。
这些接口保留实际模板和 binder，不要求 Horn 图的负反射；
[InternalSchemaQueries](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaQueries.lean) 提供完整 schema／公理查询的调用实例。

有限局部规则表使用 [InternalLocalDecisionReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalLocalDecisionReflection.lean) 的 `localMatrix`、`localRule`、`localTest`。
每个查询只提供其实际模板的正反射，头表达式、见证界及有限合取／析取由公共层处理。
[InternalProofQueries](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofQueries.lean) 复用该接口覆盖原逻辑公理、六类节点和完整行封装；
[InternalProofRowReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofRowReflection.lean) 提供复合项、数码和普通 `Derives` 终点。
[InternalCheckedStepReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedStepReflection.lean) 的 `proof_step_values` 将原 Horn 连边证明与局部真值
合成为实际 `ObjectCheckedTrace.step` 的证明；不要求轨迹项可求值为自然数。
`finite_verification_of_links` 继续复用原有限轨迹装配，只保留连边证明和局部真值输入。


任意已检查轨迹复用 [PureSourceCheckedConstruction](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSourceCheckedConstruction.lean) 的 `rule_cases_bounds`、`rule_intro_bounds`：
根行反演保留局部查询，前提重用原内部集合；构造端用公共 `collect` / `insert` 合并。
[InternalCheckedReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedReflection.lean) 的 `checked_rule_bounded_values` 把局部真值与前提实例证明装配为结论实例证明。
[InternalCheckedRanking](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedRanking.lean) 的 `checked_valid_positive` 消费原规则的阶段／字段秩证书、局部正反射及最终阶段对应。
[ObjectCheckedReflection](YesMetaZFC/Automation/ObjectCheckedReflection.lean) 的 `proof_valid` 核验原证明树全部十二条规则，
节点阶段按子证明编码下降，根阶段进入节点阶段。
[InternalProofTraceReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofTraceReflection.lean) 的 `proof_trace_positive` 已为原证明树消去上述合同；
[InternalVerificationReflection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalVerificationReflection.lean) 的 `verification_reflection`、`proof_matrix_reflection` 精确接回原矩阵，
[ReducedIntrospection](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedIntrospection.lean) 的 `ReducedProvability.introspection` 给出 D3 普通推导。

Löb 推导复用 [Loeb](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Loeb.lean) 的
`DerivabilityConditions_m`，任意签名、理论和算子共用 `imp_m`、`iff_m`、`loeb_axiom_m`、`loeb_m`。
[ObjectLoebFixedPoint](YesMetaZFC/Automation/ObjectLoebFixedPoint.lean) 将原证明图包装为
反射模板；`reflection_apply_m` 用公共自由代入定律恢复原句子，`fixed_point_m`
消费既有 `ObjectDiagonal.fixedPoint_spec`，不展开巨大 quotation。
[ReducedLoeb](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedLoeb.lean)
组装原 D1–D3 和实际固定点，公开内部 Löb 公式及普通 Löb 规则。
[SecondIncompleteness](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SecondIncompleteness.lean)
将同一接口特化到矛盾反射，导出内部与通常的第二不完备结论；
[ReducedSecondIncompleteness](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedSecondIncompleteness.lean)
直接接上 `loebSentence_m .falsum` 和已有 `consistency`，复用原否定消去规则。

纯语言传输复用 [PureSentenceTransfer](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSentenceTransfer.lean)：
`embed_m` 使用公共关系翻译，`translate_embed_m`、`derives_iff_m` 给出纯句子往返与双向推导。
反向 `embed_translate_m` 要求指定源句子的任意模型 `Agreement`；
`agreement_imp_m`、`agreement_of_iff_m` 复用已证对应，不扩大到任意支撑句子。
`translate_derives_imp_m`、`translate_derives_imp_imp_m`、`translate_derives_iff_m`、
`translate_derives_iff_imp_m` 在抽象公式参数上固定逻辑外壳，避免实例层展开检查器和 quotation。
[PureProvability](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureProvability.lean) 的
`source_canonical_m` 连接全部内部证明码对应；D3 经 `source_roundtrip_m` 将原二次可证明性
接到纯语言的二次可证明性。[PureLoeb](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLoeb.lean)
用固定点等价取得指定固定点的对应，再用通用 `iff_m` 提升到可证明性层。

真不可定义性复用 [Tarski](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Tarski.lean)：
`liar_refutes_m` 对任意签名、自由上下文和局部假设成立，只消费否定固定点；
`TruthSchema_m` 覆盖任意自由上下文的可证真值等价式，`DefinesTruth_m` 描述闭句真值；
`DefinesSatisfaction_m` 固定任意模型环境，描述同一参数列下的开放公式真值。
[ObjectTarskiFixedPoint](YesMetaZFC/Automation/ObjectTarskiFixedPoint.lean)
把候选一元模板取否定后交给 `ObjectDiagonal.fixedPoint_spec`，公共代入保持直接恢复正文。
[ReducedTarski](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedTarski.lean)
使用 `ReducedRosser.diagonalSupport`，实际生成每个候选的反例句；
句法终点消费一致性，语义终点消费任意原模型的可靠性，不依赖 D1–D3。

带参数固定点使用 [ObjectParameterDiagonal](YesMetaZFC/Automation/ObjectParameterDiagonal.lean)。
`ObjectDiagonal.instantiate` 将首个编码槽替换为数码、尾部使用 `parameterIdentity_m`；
`parameterCodes_m` 给出这段恒等替换的原项码表。正负表示及任意对象输出唯一性
直接推广原 `ObjectDiagonalSyntax`／`ObjectDiagonalRelation`，不复制图或最小输出证明。
`abstractFreeTop`、弱化及公共 binder 代入定律保留参数上下文；quotation 仍取实际开放公式。
空参数分支保留原空替换，原闭固定点构造的 AST 与推广前定义相等。
[ReducedTarskiParameters](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedTarskiParameters.lean)
导出开放反例、全称闭合反驳及每组参数赋值下的不可定义性；全称闭合复用 `forall_close_of_derives`。

纯关系语言可能没有闭项；开放完备性和一致性使用
[OpenCompleteness](YesMetaZFC/Automation/OpenCompleteness.lean) 的 `derives_open_m`、`consistent_open_m`，
复用 `ModelClosure.forall_close_iff` 和规范重新打开，不逐变量选择闭项。
[PureOpenTransfer](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureOpenTransfer.lean)
只递归参数变量，公式与 binder 仍交给 `RelationalTranslation`；`embed_canonical_m` 在同一纯模型
的同一环境中保留真值，`translate_embed_m`、`derives_iff_m` 给出开放往返和双向推导。
[PureTarskiSource](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTarskiSource.lean)
消费这些接口及已有源反例。`predicate_satisfies_m` 将纯候选与编码首槽、原参数环境明确连接，
不需要额外的原模型全语言对应，也不重写自代入图。

纯公式自身编码固定点复用 [ObjectExpressionIteration](YesMetaZFC/Automation/ObjectExpressionIteration.lean)
的固定表达式递推图与 [ObjectMinimumSemantics](YesMetaZFC/Automation/ObjectMinimumSemantics.lean)
的任意模型最小输出合同；具体数码、码形状及纯图按下表实例化。
绑定输入槽让最终编码只需计算固定语法外壳，无需给整套消元翻译另造编码算法。
[FormulaBinderSemantics](YesMetaZFC/Automation/FormulaBinderSemantics.lean) 先对抽象公式核验
存在、合取、否定、等价的语义外壳及绑定弱化；大纯图的装配使用这些引理。
不要对具体大图用 `change` 依赖语义递归的定义相等，避免内核展开整张图。
纯、源排序不同，弱化处显式给出纯签名和上下文。

| 纯自身编码构造步骤 | 接口与源码 | 调用时须保留 |
| --- | --- | --- |
| 完整纯 AST 的编码及可逆性 | [PureQuotation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureQuotation.lean)：`tree_m`、`code_m`；[PureQuotationFaithful](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureQuotationFaithful.lean)：`code_injective_m`、`decode_tree_m` | 编码结构嵌入逐节点保留原纯 AST，不经过插入见证的消元翻译 |
| 用公式定义标准数码并绑定输入槽 | [PureNumeralFormula](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNumeralFormula.lean)：`PureQuotation.numeral_satisfies_m`、`specialize_satisfies_m`、`instance_satisfies_m` | 纯语言无闭数码项；归纳输入为宿主有限自然数，模型及环境任意 |
| 连接最终公式自身码与实际纯图 | [PureQuotation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureQuotation.lean)：`self_code_m`；[PureDiagonalGraph](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureDiagonalGraph.lean)：`satisfies_m` | 标准编码输入处排除任意对象输出伪见证，不要求模型内部自然数标准 |
| 装配带参数固定点及 Tarski 反例 | [PureFixedPoint](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFixedPoint.lean)：`fixed_point_m`；[PureTarski](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTarski.lean)：`liar_fixed_point_m`、`undefinable_parameters_m` | 最终推导理论为裸 ZFC，语义合同保留每个参数赋值 |

## 有限序列、轨迹与 ProofT

下列 ProofT 文件的命名空间前缀为 `YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT`；
文件路径中的 `Metatheory` 不属于该命名空间。

| 调用方需要 | 公共接口与源码 | 调用方保留的内容 |
| --- | --- | --- |
| 从精确定义域取得行索引成员 | [FiniteSequenceConstruction](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/FiniteSequenceConstruction.lean) 的 `row_index_mem_of_domain` | 真实长度和定义域证据 |
| 同域函数按值相等 | [FiniteSequenceExtensionality](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/FiniteSequenceExtensionality.lean) 的 `function_equality_of_extensional_agreement`、`function_equality_of_finite_values` | 函数性、定义域和逐点值；不重新展开关系外延证明 |
| 标准有限算术轨迹 | [ArithmeticTrace](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ArithmeticTrace.lean) 的 `standard_numeral_trace_value`、`standard_numeral_trace_mapping`、`standard_numeral_trace_step` | 加乘幂各自的数值递推方程；消费者见 [MultiplicationTrace](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/MultiplicationTrace.lean)、[ExponentiationTrace](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ExponentiationTrace.lean) |
| 前缀、末值和序列反演 | [NatSequenceInversion](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/NatSequenceInversion.lean)、[SequenceConditionInversion](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SequenceConditionInversion.lean) 的 `sequence_trace_numeral_data`、[ProofSequenceInversion](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ProofSequenceInversion.lean) | 强化归纳同时携带前缀编码与末值，再使用有限图外延 |
| 同一行表生成公式列和证书列 | [IntrinsicCheckedSequence](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/IntrinsicCheckedSequence.lean) 的 `intro_of_mapped_rows` | 只提交行条件；长度、成员和两列取值坐标由公共引理处理 |
| 逻辑行 quotation 与数码成员 | [IntrinsicLogicalTranscriptSupport](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/IntrinsicLogicalTranscriptSupport.lean) 的 `intrinsic_zfc_quote_*`、`intrinsic_zfc_logical_certificate_mem_omega` | 目标上下文、正文深度和实际逻辑规则 |
| 已检查见证的行、序列与终端投影 | [IntrinsicCheckedWitness](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/IntrinsicCheckedWitness.lean) 的 `witness_row_formula_mem_of_code_body`、`witness_sequences_of_code_body`、`witness_terminal_of_code_body` | 保持公开投影接口；不要在每个消费者中重拆完整证书 |
| 证明终端不匹配推出矛盾 | [IntrinsicProofTerminal](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/IntrinsicProofTerminal.lean) 的 `terminal_falsum_of_standard_sequence_mismatch`、`terminal_falsum_of_proof_sequence_row_mismatch`、`terminal_falsum_of_proof_sequence_list_mismatch` | 按标准序列 → 证明行 → 行列表复用，保留实际结论与行索引 |

## 规范化与自动化

| 调用方需要 | 公共接口与源码 | 使用边界 |
| --- | --- | --- |
| 一阶机械推导 | [FirstOrderDerives/TypedView](YesMetaZFC/Automation/FirstOrderDerives/TypedView.lean)、[HostAvatar/Dispatch](YesMetaZFC/Automation/HostAvatar/Dispatch.lean) 的 `prove_auto` | 保留隐式参数、显式上下文和编译键；优先改进通用 tactic |
| 根重写传播到上下文 | [RewriteTyping](YesMetaZFC/Automation/CoreNormalForm/RewriteTyping.lean)、[ContextualRewriteSoundness](YesMetaZFC/Automation/CoreNormalForm/ContextualRewriteSoundness.lean) 的 `RootRewriteSemantics` 与 `*_of_root` | FOOL 片段 guard、高阶 λ 类型条件不省略 |
| 环境插入、删除和推进 | [CoreNormalForm/Semantics](YesMetaZFC/Automation/CoreNormalForm/Semantics.lean) 的 `Env.ext`、`skip_push`、`drop_push`、`insertAt_push` | 用环境等式承接语义；消费者包括 [NormalizationSoundness](YesMetaZFC/Automation/CoreNormalForm/NormalizationSoundness.lean)、[AntiPrenexSoundness](YesMetaZFC/Automation/CoreNormalForm/AntiPrenexSoundness.lean) |
| 支持范围与新鲜变量传输 | [LocalSkolemSoundness](YesMetaZFC/Automation/CoreNormalForm/LocalSkolemSoundness.lean) 的 `FreeSupport`、`Env.FreeAgreement`、`rebaseOverrideFunction_push` | AST 支持范围、自由变量界、类型与函数界必须显式对应 |
| Skolem 扩张组合 | [LocalSkolemSoundness](YesMetaZFC/Automation/CoreNormalForm/LocalSkolemSoundness.lean) 的 `UniformFrameExtension.refl`、`trans`、`UniformSoundExtension.refl` | 证明模型扩张下可满足性保持，不能改成同一模型内等价；组合保持界限单调性 |
| 定义性 CNF 的构造不变量 | [DefinitionalCnfSoundness](YesMetaZFC/Automation/CoreNormalForm/DefinitionalCnfSoundness.lean) 的 `Definition.BuildState.buildCore_invariant`、`DefinitionalCnf.buildCore_from_empty_sound` | 复用同一次状态归纳取得 includes/freshness；子句语义用 `clauseOfRefsAux_satisfies`、`clausesOfRefs_satisfies` |
| 公共证书及拓扑回放 | [Automation/Certificate](YesMetaZFC/Automation/Certificate.lean)、[Automation/DAGCertificate](YesMetaZFC/Automation/DAGCertificate.lean)、[DAGCertificate/IntrinsicReplay/Semantics](YesMetaZFC/Automation/DAGCertificate/IntrinsicReplay/Semantics.lean) | 后端输出 checked payload；FO 编译环境与 HO 的类型、bound stack 条件分别保留 |
| 重命名、替换与 AVATAR 语义 | [CompileRenaming](YesMetaZFC/Automation/DAGCertificate/CompileRenaming.lean)、[CompileSubstitution](YesMetaZFC/Automation/DAGCertificate/CompileSubstitution.lean)、[DAGCertificate/IntrinsicReplay/AvatarSemantics](YesMetaZFC/Automation/DAGCertificate/IntrinsicReplay/AvatarSemantics.lean) | 共用构造子归纳与已有编译支持合同，不混淆 selector、父字句、guard 和 theory-conflict 来源 |
| 调度、预处理与 residual | [Automation/Scheduler](YesMetaZFC/Automation/Scheduler.lean)、[SourcePreprocessing](YesMetaZFC/Automation/SourcePreprocessing.lean)、[Automation/Resolution](YesMetaZFC/Automation/Resolution.lean)、[PropCdcl](YesMetaZFC/Automation/PropCdcl.lean) | 领域模块只提供合同；搜索实现和公共前端位于 Automation |
| Henkin 调度所需的可数语法 | [SyntaxNatCoding](YesMetaZFC/Automation/SyntaxNatCoding.lean) | 单射编码服务于完备性，不替换对象理论 quotation |

[GuardSemantics](YesMetaZFC/Automation/GuardSemantics.lean) 统一 FO/HO 公用的命题语义：
`Clause.satisfies_canonical_iff`、`satisfies_append_iff` 与 `Clause.Satisfies.transfer`
负责子句外壳；`Guards.learnedClause_satisfies_iff` 把学习子句接到守卫合取的否定，
`Guards.activation_satisfies` 接到守卫蕴含正文。激活接口要求两种赋值在每个原守卫上
真值一致；对象文字的编译、类型和 atom map 外部检查由各自回放层提供。

[IntrinsicReplay/Core](YesMetaZFC/Automation/DAGCertificate/IntrinsicReplay/Core.lean) 的
`parent_compiled_raw_of_snapshot` 只消费实际父索引及已检查快照，供父拷贝、局部规则、
初始子句与冲突回放共用。`IntrinsicReplay/Semantics.literalLinks_satisfies` 只处理
已编译真文字的链接映射；父边、guard 和整体拓扑条件仍由调用者证明。
已知索引存在时先使用 `node?_eq_some_nodeAt`，无需再次划分查找失败分支。

## 核验入口与维护边界

```bash
lake --wfail build
bash scripts/check-all.sh
```

全源脚本覆盖全部独立模块及 `prove_auto_sweep`。扫描器只静态导入
`Automation.HostAvatar.Dispatch`，完整库在运行时加载；动态使用的
`ProveAutoBranchProbe` 不得仅因默认导入图不可达而删除。工具依赖改变时，
检查 `--help` 和一次实际目标扫描，命令使用 `lake env .lake/build/bin/prove_auto_sweep ...`。

当前规模、本轮基点、净减量与同条件耗时对照见
[PROOF_REDUCTION.md](PROOF_REDUCTION.md)。计数包含注释和空行，排除缓存、探针和文档；
新增公共接口必须计入净减量。构建结果只对应该记录标明的源码指纹。
数学成果与原节点可信依赖审计见 [UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md)。
此前 [4ae86c1](https://github.com/lanxinge/YesMetaZFC/commit/4ae86c1b38c756e95d3dee7e8de50a9c60db292b)
的 806 个 Lean 文件、225,346 行总代码是重构历史基点，不是当前规模。

Lean 4.33.1 适配约定：必要的类型别名使用 `@[implicit_reducible]`，定义相等转换
可用 `simpa ... using!`，自由闭合性消费 `code_freeClosed`。
`Resolution.CertificateSlice.compactCore?` 的旧 do elaborator 选项和六个签名／结构
声明的局部 `linter.checkUnivs` 豁免是已有工具链适配，不扩大为全局关闭检查。

## 尚可推进的工作

| 方向 | 先检查的现有基础 | 下一步的验收条件 |
| --- | --- | --- |
| 扩大公共证明接口的消费范围 | 本页序列、环境、状态不变量和 shape 接口 | 找到仍重复的实际消费者；完成迁移后扣除新增抽象再计净减量 |
| DAG 已检查父节点视图与材料化 | [DAGCertificate/IntrinsicReplay/Semantics](YesMetaZFC/Automation/DAGCertificate/IntrinsicReplay/Semantics.lean)、[HOAvatarSoundness](YesMetaZFC/Automation/HOAvatarSoundness.lean)、[SearchMaterialization](YesMetaZFC/Automation/SearchMaterialization.lean)、[HOSearchMaterialization](YesMetaZFC/Automation/HOSearchMaterialization.lean)、[ResourceTrace](YesMetaZFC/Automation/ResourceTrace.lean) | 先核对剩余重复；统一父索引、快照和 payload 提取，保留 FO/HO 特有证据及失败分支 |
| 可组合的纯定义扩张 | [RelationalEnvironment](YesMetaZFC/Automation/RelationalEnvironment.lean) 的 `mapSortValues`、[RelationalTransfer](YesMetaZFC/Automation/RelationalTransfer.lean)、[RelationalInheritance](YesMetaZFC/Automation/RelationalInheritance.lean) | 参数列只沿排序递归；`CoveredExtension.trans` 组合覆盖增长与旧图保持；任意翻译相等仍可直接传输，函数规格用 `specification_regraph`，闭句用 `ModelClosure.templateEnv_nil` |
| 集合图与双射的数学复用 | [FunctionSpaceAlgebra](YesMetaZFC/SetTheory/FunctionSpaceAlgebra.lean)、[Card/Arithmetic/Equinumerosity](YesMetaZFC/SetTheory/Card/Arithmetic/Equinumerosity.lean) | 用模型内部可定义映射及复合消除重复，宿主 `Equiv` 不能替代集合图 |
| 大公式核验性能 | [PureLogicalSchemaSets](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLogicalSchemaSets.lean) 的 `condition_bounded`、[PureFinalSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSyntax.lean) 及 [PureSyntaxTransform](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSyntaxTransform.lean) | 先作声明级测量，将语义形状与具体解释分开，保留原公式及证明前提 |
| 扫描器前端覆盖 | `GoalRequest` 到领域目标的接入 | `Ordinal.transitive` 的现有扫描结果为 `not_closed` / `unknown`；前端接入和搜索成功分别核验 |

测量示例：`lake env lean --profile -Dprofiler.threshold=50 <模块路径>`。
日常构建不开启全量 `Meta.isDefEq` 或 `simp.rewrite` 追踪。
