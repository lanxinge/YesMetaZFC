# 证明基础设施指路表

按调用方要消除的证明义务查表。这里记录可复用接口与适用条件；
已完成计划的实施过程、逐轮行数和耗时记录由 Git 历史保存。
裸 ZFC 与编码接口分别见 [ELIMINATION.md](ELIMINATION.md)、[NAT_DECODING.md](NAT_DECODING.md)。

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

## 核验入口与维护边界

```bash
lake --wfail build
bash scripts/check-all.sh
```

全源脚本覆盖全部独立模块及 `prove_auto_sweep`。扫描器只静态导入
`Automation.HostAvatar.Dispatch`，完整库在运行时加载；动态使用的
`ProveAutoBranchProbe` 不得仅因默认导入图不可达而删除。工具依赖改变时，
检查 `--help` 和一次实际目标扫描，命令使用 `lake env .lake/build/bin/prove_auto_sweep ...`。

当前源码基点为 [4ae86c1](https://github.com/lanxinge/YesMetaZFC/commit/4ae86c1b38c756e95d3dee7e8de50a9c60db292b)：
806 个 Lean 文件、224,509 行；含 Python/Shell 共 225,346 行，严格低于 200,000
还需净减 25,347 行。文档删除不计入代码减量。该基点全源 808 个构建任务、扫描工具
320 个任务通过，零错误、零警告；声明与可信依赖的核验摘要见
[UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md)。

Lean 4.33.1 适配约定：必要的类型别名使用 `@[implicit_reducible]`，定义相等转换
可用 `simpa ... using!`，自由闭合性消费 `code_freeClosed`。
`Resolution.CertificateSlice.compactCore?` 的旧 do elaborator 选项和六个签名／结构
声明的局部 `linter.checkUnivs` 豁免是已有工具链适配，不扩大为全局关闭检查。

## 尚可推进的工作

| 方向 | 先检查的现有基础 | 下一步的验收条件 |
| --- | --- | --- |
| 扩大公共证明接口的消费范围 | 本页序列、环境、状态不变量和 shape 接口 | 找到仍重复的实际消费者；完成迁移后扣除新增抽象再计净减量 |
| DAG 已检查父节点视图与材料化 | [DAGCertificate/IntrinsicReplay/Semantics](YesMetaZFC/Automation/DAGCertificate/IntrinsicReplay/Semantics.lean)、[HOAvatarSoundness](YesMetaZFC/Automation/HOAvatarSoundness.lean)、[SearchMaterialization](YesMetaZFC/Automation/SearchMaterialization.lean)、[HOSearchMaterialization](YesMetaZFC/Automation/HOSearchMaterialization.lean)、[ResourceTrace](YesMetaZFC/Automation/ResourceTrace.lean) | 先核对剩余重复；统一父索引、快照和 payload 提取，保留 FO/HO 特有证据及失败分支 |
| 可组合的纯定义扩张 | [PureCollectionStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureCollectionStage.lean)、[PureSequenceStage](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSequenceStage.lean)、[RelationalTransfer](YesMetaZFC/Automation/RelationalTransfer.lean) | 在连续小阶段上验证新旧图保持和规格传输；不从最终巨大解释项展开 |
| 集合图与双射的数学复用 | [FunctionSpaceAlgebra](YesMetaZFC/SetTheory/FunctionSpaceAlgebra.lean)、[Card/Arithmetic/Equinumerosity](YesMetaZFC/SetTheory/Card/Arithmetic/Equinumerosity.lean) | 用模型内部可定义映射及复合消除重复，宿主 `Equiv` 不能替代集合图 |
| 大公式核验性能 | [PureLogicalSchemaSets](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLogicalSchemaSets.lean) 的 `condition_bounded`、[PureFinalSyntax](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFinalSyntax.lean) 及 [PureSyntaxTransform](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSyntaxTransform.lean) | 先作声明级测量，将语义形状与具体解释分开，保留原公式及证明前提 |
| 扫描器前端覆盖 | `GoalRequest` 到领域目标的接入 | `Ordinal.transitive` 的现有扫描结果为 `not_closed` / `unknown`；前端接入和搜索成功分别核验 |

测量示例：`lake env lean --profile -Dprofiler.threshold=50 <模块路径>`。
日常构建不开启全量 `Meta.isDefEq` 或 `simp.rewrite` 追踪。
