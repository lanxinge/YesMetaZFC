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
