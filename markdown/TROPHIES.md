# 形式化成果奖杯表

本表登记当前源码中的结论；构造和证明细节通过基础设施指南定位。

## 裸 ZFC 成果总览

以下入口均已有实际证明。`ZFC` 指 `PureModel.theory`，推导使用普通 `Derives`；
可证明性算子沿用原检查器的纯语言表示，自身编码固定点直接编码最终纯公式。

| 成果 | 最终入口 | 前提与范围 |
| --- | --- | --- |
| 原生小图 ZFC 模型与一致性 | [SmallGraph/ZFC](../YesMetaZFC/Model/SmallGraph/ZFC.lean)：`sg_models_zfc`、`zfc_consistent` | Lean 元层直接构造良基小图双模拟商；验证原 ZFC 全部公理与模式，无模型存在或一致性前提 |
| Rosser 双侧独立性 | [PureRosserComplete](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean)：`PureRosser.independent` | 裸 ZFC 一致；具体纯闭句及其否定均不可证 |
| 可证明性 D1–D3 | [PureProvability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureProvability.lean)：`necessitation_m`、`distribution_m`、`introspection_m` | 无一致性或标准模型前提；任意纯闭句 |
| Löb 内部公式与规则 | [PureLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLoeb.lean)：`PureProvability.loeb_axiom_m`、`loeb_m` | 固定点实际构造；不另假定反射原则 |
| 哥德尔第二不完备定理 | [PureSecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSecondIncompleteness.lean)：`PureProvability.second_incompleteness_m` | 裸 ZFC 一致时，不能证明对应的对象一致性句子 |
| 纯公式自身编码的带参数固定点 | [PureFixedPoint](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFixedPoint.lean)：`fixed_point_m` | 任意有限参数；编码是最终纯公式自身的完整 AST 码 |
| Tarski 真不可定义性 | [PureTarski](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTarski.lean)：`undefinable_syntax_m`、`undefinable_parameters_m` | 句法版假定一致；语义版覆盖任意裸模型和参数赋值，量化同一参数上下文的全部纯开放公式 |

源理论、保留源编码的纯翻译和纯公式自身编码的具体合同分列如下。
原元数学核验覆盖 530 个依赖审计入口；小图层另核验 38 个关键接口，当前全源构建
覆盖 979 个 Lean 模块，未新增可信依赖。原公理的 8 处句法闭合性原生依赖仍保留；详见
[UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md)。

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
| 具体纯句子与普通 Hilbert 固定点推导 | [PureRosser](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosser.lean) 的 `sentence`、`fixed_point` |
| 任意原模型上的句子对应 | [PureRosserComplete](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) 中 `PureRosser.agreement` |
| 裸 ZFC 双侧不可证性 | [PureRosserComplete](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) 中 `PureRosser.independent` |
| 三参数纯 Δ₀ 矩阵及实际推导等价 | [PureRosserDelta0](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `matrix_delta0`、`parameters_exists`、`parameters_unique`、`representation_derives` |
| 当前纯句子非 Δ₀，以及一致性下排除无参数闭 Δ₀ 等价代表 | [PureRosserDelta0](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `sentence_not_delta0`、`no_closed_delta0_equivalent` |

纯 Δ₀ 矩阵为 $\neg\exists p\in w\,(p\in A\land\forall q\in p\,q\notin B)$。
参数定义未分类为 Δ₀，保留定义的完整存在闭句非 Δ₀。

## 普通可证明性的 D1–D3、Löb 与第二不完备定理

令 $T=\texttt{intrinsic_zfc_theory}$，$\Box\varphi$ 为
`ReducedProvability.provable φ`，使用原有
`ReducedNaturalProofPresentation.presentation.graph` 和完整 AST quotation。

| 成果 | 声明与源码 |
| --- | --- |
| D1：$T\vdash\varphi$ 推出 $T\vdash\Box\varphi$ | [ReducedProvability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProvability.lean) 的 `necessitation`；通用表示版见 [Provability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Provability.lean) |
| D2：$T\vdash\Box(\varphi\to\psi)\to(\Box\varphi\to\Box\psi)$ | [ReducedDerivability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedDerivability.lean) 中 `ReducedProvability.distribution` |
| D3：$T\vdash\Box\varphi\to\Box\Box\varphi$ | [ReducedIntrospection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedIntrospection.lean) 的 `ReducedProvability.introspection`；原验证矩阵反射已完整填入 |
| 具体 Löb 固定点 $T\vdash\psi\leftrightarrow(\Box\psi\to\varphi)$ | [ReducedLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedLoeb.lean) 的 `loebSentence_m`、`loeb_fixed_point_m`；复用原码域和对角构造 |
| 内部 Löb 公式 $T\vdash\Box(\Box\varphi\to\varphi)\to\Box\varphi$ | [ReducedLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedLoeb.lean) 的 `loeb_axiom_m` |
| Löb 规则：若 $T\vdash\Box\varphi\to\varphi$，则 $T\vdash\varphi$ | [ReducedLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedLoeb.lean) 的 `loeb_m` |
| 对象一致性句子 $\neg\Box\bot$ 及相对支撑语言的 Π₁ 分类 | [ReducedProvability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProvability.lean) 的 `consistency`、`consistency_pi1` |
| 内部第二不完备公式 $T\vdash\mathrm{Con}(T)\to\neg\Box\mathrm{Con}(T)$ | [ReducedSecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedSecondIncompleteness.lean) 的 `second_incompleteness_internal_m` |
| 第二不完备定理：若 $T$ 一致，则 $T\nvdash\mathrm{Con}(T)$ | [ReducedSecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedSecondIncompleteness.lean) 的 `second_incompleteness_m`；使用上述 `consistency` |
| 任意内部自然数证明码上的实际 MP 构造 | [ReducedProofComposition](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofComposition.lean) 的 `modus_ponens` |

D1–D3、Löb 和内部第二不完备公式不假定 $T$ 一致、可靠或其模型的自然数域外部标准。
D2 合并内部轨迹，
验证新增 MP 节点和根行，最后由既有强完备性导出普通 Hilbert 推导。
D3 通过实际公式的内部强归纳反射原已检查轨迹。Löb 的通用推导见
[Loeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Loeb.lean)，只消费 D1–D3
与固定点等价；具体实例实际构造该固定点，不把它另列为假设。
第二不完备定理将 Löb 规则应用于 $\bot$，只以 $T$ 一致为前提排除 `consistency` 的推导。
裸 ZFC 中的对应成果使用下述纯语言算子。

## 裸 ZFC 的可证明性、Löb 与第二不完备定理

令 $Z=\texttt{PureModel.theory}$，$e$ 为纯句子向原支撑语言的嵌入，$\tau$ 为支撑消元翻译。
纯语言算子定义为 $\Box_Z\varphi=\tau(\Box_T e(\varphi))$；
它仍使用原 quotation 和检查器，且 `checked_iff_m` 已证明接受嵌入句子证书
当且仅当 $Z\vdash\varphi$。

| 成果 | 声明与源码 |
| --- | --- |
| 纯句子双向推导 $T\vdash e(\varphi)\iff Z\vdash\varphi$ | [PureSentenceTransfer](../YesMetaZFC/Model/ZFC/Pure/PureSentenceTransfer.lean) 的 `derives_iff_m`；`translate_embed_m` 给出实际往返等价推导 |
| 纯语言可证明性的精确表示及 D1–D3 | [PureProvability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureProvability.lean) 的 `checked_iff_m`、`necessitation_m`、`distribution_m`、`introspection_m` |
| 实际固定点、内部 Löb 公式和 Löb 规则 | [PureLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLoeb.lean) 的 `loeb_fixed_point_m`、`loeb_axiom_m`、`loeb_m` |
| $Z\vdash\mathrm{Con}_Z\to\neg\Box_Z\mathrm{Con}_Z$ | [PureSecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSecondIncompleteness.lean) 的 `second_incompleteness_internal_m` |
| 若裸 ZFC 一致，则 $Z\nvdash\mathrm{Con}_Z$ | 同文件 `second_incompleteness_m`；其中 $\mathrm{Con}_Z=\neg\Box_Z\bot$，`consistency_translation_m` 证明它等于原一致性句子的纯翻译 |

上述最终定理均在 `PureProvability` 命名空间中，句子只含纯隶属语言的符号。
固定点和 D3 使用任意原模型上的可证明性对应，没有额外反射或标准性前提。
这里没有另换一套直接编码纯 ZFC 证明树的检查器；与另选原生编码在对象理论内部的等价
不包含在这些结果中。

## 原支撑理论的塔斯基真不可定义性

令 $T=\texttt{intrinsic_zfc_theory}$，候选真谓词 $P$ 为无额外自由参数的任意
`FormulaTemplate.Unary`，$P(\ulcorner\varphi\urcorner)$ 使用当前 `IntrinsicQuotation.quote`。
下列入口均在 [ReducedTarski](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedTarski.lean) 中。

| 成果 | 声明 |
| --- | --- |
| 实际反例句 $L_P$ 及 $T\vdash L_P\leftrightarrow\neg P(\ulcorner L_P\urcorner)$ | `liarSentence_m`、`liar_fixed_point_m` |
| $T\vdash\neg(P(\ulcorner L_P\urcorner)\leftrightarrow L_P)$ | `liar_refutes_m`；不要求理论一致 |
| 一致性下，相应真值等价式不可证 | `biconditional_unprovable_m` |
| 一致性下，不存在全部真值等价式均可证的一元公式 | `undefinable_syntax_m` |
| 任意 $\mathcal M\models T$ 中，不存在对全部闭句正确的无参数真谓词 | `undefinable_semantics_m`；模型载体宇宙任意 |

反例句复用原对角构造，未留下固定点前提；逻辑核心见
[Tarski](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Tarski.lean)。
无参数语义版量化宿主 `SetSentence`，允许模型内部自然数非标准。
保留源编码及使用最终纯公式自身编码的裸 ZFC 版本均见下文。
既有 `TarskiTruth` 提供集合结构的满足关系规格，与这里的真不可定义性分别登记。

### 任意有限参数的逐赋值版本

[ReducedTarskiParameters](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedTarskiParameters.lean)
的命名空间为 `ReducedTarski.Parameters`。候选 $P(x,\bar z)$ 允许任意有限参数列，
实际构造开放公式 $L_P(\bar z)$，其原 quotation $\ulcorner L_P\urcorner$ 不随参数取值变化。

| 成果 | 声明 |
| --- | --- |
| $T\vdash L_P(\bar z)\leftrightarrow\neg P(\ulcorner L_P\urcorner,\bar z)$ | `liarFormula_m`、`liar_fixed_point_m` |
| $T\vdash\forall\bar z\,\neg(P(\ulcorner L_P\urcorner,\bar z)\leftrightarrow L_P(\bar z))$ | `liar_refutes_closed_m`；无一致性前提 |
| 一致性下，任意有限参数上下文均不能具有全部可证真值等价式 | `biconditional_unprovable_m`、`undefinable_syntax_m` |
| 同一反例在任意原模型的每一组参数赋值下使等价式失败 | `liar_fails_at_m` |
| 固定任意参数赋值，排除全部候选公式 | `undefinable_at_m` |
| 同时排除任意有限参数数目、取值及候选公式 | `undefinable_parameters_m` |

真值合同是对所有相同自由上下文中的宿主开放公式 $\varphi(\bar z)$，要求
$P(\ulcorner\varphi\urcorner,\bar a)\leftrightarrow\varphi(\bar a)$。
参数是任意模型元素，不要求由闭项或标准数码命名。这个合同包含使用参数本身的反例公式；
它不等同于仅要求候选判定无参数闭句的真值集合，也不把非标准内部语法的满足关系列为已构造内容。

### 裸 ZFC 中保留源编码的纯语言版本

[PureTarskiSource](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTarskiSource.lean)
允许任意纯候选 $P(x,\bar z)$。令 $S_P$ 为其嵌入原语言后实际生成的反例，
$L_P=\tau(S_P)$ 为纯反例，$\tau$ 是现有的完整关系消元。以下推导均使用裸 `PureModel.theory`。

| 成果 | 声明 |
| --- | --- |
| 纯候选、源反例及实际纯反例 | `Candidate_m`、`sourceLiar_m`、`liarFormula_m` |
| 消元后的候选实例恰好应用原纯候选，保留全部参数 | `predicate_satisfies_m`；编码值由 `quotation_m` 给出，与赋值无关 |
| $L_P$ 与对应候选实例的否定等价，以及反驳式的全称闭合 | `liar_fixed_point_m`、`liar_refutes_closed_m`；无一致性前提 |
| 裸 ZFC 一致性下，排除相应等价式及全部可证真值等价式 | `biconditional_unprovable_m`、`undefinable_syntax_m` |
| 任意裸 ZFC 模型、每组有限参数赋值下均失败 | `liar_fails_at_m`、`undefinable_at_m`、`undefinable_parameters_m` |
| 直接排除原纯候选定义规范扩张中全部源开放公式的真值 | `undefinable_source_at_m` |

合同量化源公式 $\varphi(\bar z)$，在其原编码处要求
$P(\ulcorner\varphi\urcorner,\bar a)\leftrightarrow\tau(\varphi)(\bar a)$。
因此这里的反例编码是 $\ulcorner S_P\urcorner$，不是 $\ulcorner L_P\urcorner$。
这个接口保留其源编码合同；纯公式自身编码的结果由下一独立接口给出。

### 裸 ZFC 中纯公式自身编码的版本

[PureQuotation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureQuotation.lean) 与 [PureQuotationFaithful](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureQuotationFaithful.lean)
提供完整纯 AST 编码、单射性及原编解码器对应。
[PureFixedPoint](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFixedPoint.lean) 的 `fixed_point_m` 对任意有限参数的纯候选 $P$
实际构造纯公式 $L$，证明 $\mathrm{ZFC}\vdash L(\bar z)\leftrightarrow P(\ulcorner L\urcorner,\bar z)$；
其中编码是最终纯公式 $L$ 本身的码，编码实例用纯数码公式定义。

[PureTarski](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTarski.lean) 导出：

| 成果 | 声明 |
| --- | --- |
| 实际纯反例及自身编码 liar 固定点 | `liarFormula_m`、`liar_fixed_point_m` |
| 裸 ZFC 直接反驳相应真值等价式及其全称闭合 | `liar_refutes_m`、`liar_refutes_closed_m`；无一致性前提 |
| 一致性下排除全部可证纯真值等价式 | `biconditional_unprovable_m`、`undefinable_syntax_m` |
| 任意裸模型、任意有限参数赋值下排除纯真值定义 | `liar_fails_at_m`、`undefinable_at_m`、`undefinable_parameters_m` |

合同量化所有相同自由上下文的纯公式 $\varphi(\bar z)$，要求
$P(\ulcorner\varphi\urcorner,\bar a)\leftrightarrow\varphi(\bar a)$。
编码独立于参数赋值；参数不要求闭项名称，模型不要求标准。
这仍是宿主有限公式的真不可定义性，不是非标准内部语法满足关系的构造。

## 内部数码与轨迹反射

继续使用现有 `ObjectNumeralSyntax.condition` 与完整 AST 编码。
其输入和输出是任意内部自然数，不要求能解码为宿主 `Nat`。

| 成果 | 声明与源码 |
| --- | --- |
| 数码图总性与唯一性的实际对象闭句推导 | [PureSourceNumeralTotality](../YesMetaZFC/Model/ZFC/Pure/PureSourceNumeralTotality.lean) 中 `PureSourceNumeralSyntax.totalUnique_derives` |
| 数码输出通过当前完整语法图的闭项检查 | [InternalNumeralQuotation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralQuotation.lean) 中 `PureSourceNumeralSyntax.wellFormed_derives`、`quotation_exists_unique`；`graph_term` 还覆盖任意内部上下文长度 |
| 标准输入与既有 AST 编码算法一致 | [PureSourceNumeralTotality](../YesMetaZFC/Model/ZFC/Pure/PureSourceNumeralTotality.lean) 中 `PureSourceNumeralSyntax.standard_iff` |
| 固定完整 AST 的非标准自由代入 | [PureSourceSubstitution](../YesMetaZFC/Model/ZFC/Pure/PureSourceSubstitution.lean) 中 `PureSourceInstantiation.formula_substitution`、`unary_substitution`；接入当前模式 3 变换图 |
| 数码命名与代入在整个内部 ω 上的实际总性推导 | [InternalNumeralSubstitution](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralSubstitution.lean) 的 `total_derives`；同一个合法闭项数码作为代入表条目 |
| 非标准结论码上的六类节点装配和 MP | [ReducedProofComposition](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofComposition.lean) 的 `codeProof_of_node`、`modus_ponens_code`；保留原证明图与实际语法条件 |
| 内部逻辑公理及存在引入 | [ReducedProofLogicalConstruction](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofLogicalConstruction.lean) 的 `logical_rule`、`exists_introduction`；须提供实际模式 2 实例化证书及正文、项和实例的语法证书 |
| 自由代入与点实例化的同一输出 | [PureSourcePointInstantiation](../YesMetaZFC/Model/ZFC/Pure/PureSourcePointInstantiation.lean) 中 `PureSourceInstantiation.unary_point`；抽象后的模式 2 输出等于原公式的模式 3 输出 |
| 无额外语法义务的数码存在引入 | [InternalNumeralProof](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralProof.lean) 的 `instance_wellFormed`、`exists_introduction`；只消费数码图及实例的内部证明 |
| 已证定理的全部内部数码实例 | [InternalNumeralSpecialization](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralSpecialization.lean) 中 `InternalNumeralProof.specialize_values`、`specialize_finite`；任意有限参数数目，旧单参数入口与 MP 复用统一构造 |
| 连续特化保持已代入数码 | [InternalNumeralTransform](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralTransform.lean) 中 `PureSourceNumeralSyntax.graph_transform`；[InternalNumeralParameters](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralParameters.lean) 的 `PureSourceInstantiation.numeral_point`，保持任意内部深度下的合法数码 |
| 任意内部数码可证明属于 ω | [InternalNumeralArithmeticReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralArithmeticReflection.lean) 中 `InternalNumeralReflection.natural`、`natural_derives`；实际可分离公式归纳，零／后继步骤无反射假设 |
| 内部数码零测试的正负反射 | [InternalNumeralZeroReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralZeroReflection.lean) 中 `InternalNumeralReflection.zero`、`nonzero`；两种真值均生成当前证明图接受的内部证明 |
| 任意两个内部数码的相等与不等反射 | [InternalNumeralEqualityRules](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralEqualityRules.lean) 中 `InternalNumeralReflection.equal`；[InternalNumeralEqualityReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralEqualityReflection.lean) 中 `unequal`、`unequal_derives`，对非标准自然数也成立 |
| 内部自然数严格／非严格序的正负反射 | [InternalNumeralOrderReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralOrderReflection.lean) 的 `order`、`weak_order`、`order_derives`；序关系及其否定都生成原证明图接受的内部证明 |
| 任意内部自然数的加乘幂数码求值 | [InternalArithmeticEvaluation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalArithmeticEvaluation.lean) 的 `addition_evaluation`、`multiplication_evaluation`、`exponentiation_evaluation`、`arithmetic_evaluation_derives`；三个运算复用实际公式的内部归纳，没有求值反射假设 |
| Gödel 配对及复合编码项求值 | [InternalPairingEvaluation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPairingEvaluation.lean) 的 `pairing_evaluation`、`pairing_evaluation_derives`；[InternalCodingEvaluation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCodingEvaluation.lean) 覆盖字段列、节点、Horn 表达式和参数化 AST 码项，共用 `binary_term_evaluation` |
| 既定 quotation 的求值证明 | [InternalQuotationEvaluation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalQuotationEvaluation.lean) 的 `quotation_evaluation`；保持原树编码，输出原证明谓词接受的数码等式证明 |
| 复合项原子及逻辑联结词的正负反射 | [InternalAtomicReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalAtomicReflection.lean) 的 `atomic_reflection`；[InternalBooleanReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalBooleanReflection.lean) 的 `boolean_reflection`，数值与内部证明可非标准 |
| 任意内部自然数界的量词反射 | [InternalBoundedTerms](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalBoundedTerms.lean) 的 `bounded_term_reflection`；全称／存在、正／负方向共用界项求值与 `bounded_bundle`，不假定内部区间外部有限 |
| 原验证矩阵的有限轨迹证明装配 | [InternalVerificationTrace](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalVerificationTrace.lean) 的 `finite_verification`；原检查器及局部条件不变，有限骨架及各行内部证明仍是输入 |
| 任意内部数码递归轨迹的正负反射 | [InternalNumeralTraceReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralTraceReflection.lean) 的 `numeral_trace_positive`、`numeral_trace_positive_derives`；[InternalNumeralTraceDecision](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralTraceDecision.lean) 的 `numeral_trace_negative`、`numeral_trace_reflection`；使用原 `ObjectNumeralSyntax.condition` 和原证明图；实际对象公式归纳，无外部有限轨迹或反射假设，支持已求值复合项 |
| 原投影图全部七条规则的内部正反射 | [InternalProjectionReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProjectionReflection.lean) 的 `projection_positive`、`projection_term_positive`、`projection_positive_derives`；索引、输入和原轨迹均可非标准，取尾递归使用实际对象公式归纳 |
| 原一般语法图的内部正反射 | [InternalSyntaxReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSyntaxReflection.lean) 的 `syntax_positive`、`syntax_term_positive`、`syntax_positive_derives`；项、参数列和公式共用实际公式的内部强归纳，覆盖非标准输入与上下文，并保留原检查器规则 |
| 原四种语法变换的内部正反射 | [InternalTransformReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalTransformReflection.lean) 的 `transform_positive`、`transform_term_positive`、`transform_positive_derives`；原 28 条规则共用分层内部强归纳 |
| 原 schema 与传输包图的内部正反射 | [InternalSchemaGraphs](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaGraphs.lean)、[InternalPacketReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPacketReflection.lean)；正文、重命名、表生成、闭句、quotation 转换及传输包的原规则均已反射 |
| verifier 实际 schema／公理查询的内部正反射 | [InternalSchemaQueries](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaQueries.lean) 的 `packet_term_positive`、`axiom_term_positive`、`axiom_query_positive`、`axiom_query_positive_derives`；保留原有界查询和数码，覆盖非标准参数，无查询反射前提 |
| 原逻辑／证明行查询的内部正反射 | [InternalProofRowReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofRowReflection.lean) 的 `logical_term_positive`、`node_term_positive`、`row_term_positive`、`row_named_positive` 及三项 `*_positive_derives`；全部原逻辑公理、六类节点及实际行封装，无局部查询反射假设 |
| 实际检查步骤的局部证明装配 | [InternalCheckedStepReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedStepReflection.lean) 的 `proof_step_values`、`finite_verification_of_links`；局部查询只需真值，原 Horn 连边证明仍须提供 |
| 原证明树任意内部已检查轨迹反射 | [InternalProofTraceReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofTraceReflection.lean) 的 `proof_trace_positive`、`proof_trace_values`、`proof_trace_positive_derives`；覆盖全部原规则与非标准根行，不要求外部骨架或连边证明 |
| 原验证矩阵与完整证明矩阵的数码反射 | [InternalVerificationReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalVerificationReflection.lean) 的 `verification_reflection`、`proof_matrix_reflection`；保留原图、quotation 和自然数 guard |

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
| 完整自然数证书往返与可推导性表示 | [ZFC/NatEncode](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/NatEncode.lean)、[ZFC/NatDecode](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/NatDecode.lean) | [证书和对象图](NAT_DECODING.md) |
| 当前 quotation 的具体证明表示与源 Rosser 实例 | [ReducedProofPresentation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofPresentation.lean)、[ReducedNaturalProofPresentation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedNaturalProofPresentation.lean)、[ReducedRosser](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedRosser.lean) | [证书和对象图](NAT_DECODING.md) |
| 有限基使用的 64 个函数、46 个关系的纯定义 | [PureCompletedStage](../YesMetaZFC/Model/ZFC/Pure/PureCompletedStage.lean) | [定义与规格](ELIMINATION.md) |
| 119 条有限基及原无限参数支撑理论的模型验证 | [PureSupportModels](../YesMetaZFC/Model/ZFC/Pure/PureSupportModels.lean) 的 `support_models` | [逐项公理索引](UNIFIED_VERIFICATION.md) |
| 原 ZFC 像、纯翻译、模型扩张与约化 | [PureZFCModels](../YesMetaZFC/Model/ZFC/Pure/PureZFCModels.lean) 的 `models`、`translated_models`、`expands`、`reduction` | [模型与推导](UNIFIED_VERIFICATION.md) |
| 全部内部自然数证明码的实际图对应 | [PureSourceLocalTests](../YesMetaZFC/Model/ZFC/Pure/PureSourceLocalTests.lean) 的 `proof_agreement` | [内部模型对应](UNIFIED_VERIFICATION.md) |

一般反向句法保守性未包含在上表结论中。原递归序列族之并在合法递归器下的
ω 全域性仍是独立数学待办。源码核验与可信依赖以
[UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md) 的当前基点为准。
