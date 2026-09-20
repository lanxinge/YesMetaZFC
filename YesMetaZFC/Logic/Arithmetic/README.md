# 算术理论

本目录提供独立 Q/PA 及双排序 Z₂ 的最小语言、公理模式和对象推导。
`import YesMetaZFC.Logic.Arithmetic` 导入数码计算、PA 归纳、Z₂ 完整理解及其导出的全公式归纳。
模型性、任意模型中的可定义归纳及标准模型一致性从 `YesMetaZFC.Model.Arithmetic` 单独导入。
只需要 PA 时可导入 `YesMetaZFC.Logic.Arithmetic.PA.Induction`，不引入 Z₂。
一般加法规律由 `PA.Addition` 提供；乘法零律、单位律、后继律、交换律、双侧分配律与结合律由 `PA.Multiplication` 提供。
这些接口保留任意 PA 扩张、自由参数、局部假设与输入项，不仅适用于外部数码。
任意 PA 模型中的对应结果见 `YesMetaZFC.Model.Arithmetic.PA.Operations`，只消费推导可靠性。

Z₂ 的数目公理与 Q 共用 `Robinson` 模板，理解允许任意数／集合量词和有限混合参数。
全公式归纳是理解与集合归纳的对象推论，不是另加的公理。
PA→Z₂ 的项、公式、代入、推导翻译已由 `PA.Interpretation` 提供；
`Model.Arithmetic.Z2.Reduct` 给出任意 Z₂ 模型的 PA 数域约化。Stage 1、2 的核心合同已核验。
翻译只证明正向解释，不宣称 Z₂ 对 PA 保守。
Z₂ 使用多排序一阶呈现，标准全数集模型的存在不等于 Full 二阶逻辑的完备性。

实施顺序：PA 核心 → Z₂ 理解与归纳及 PA 翻译 → 内部算术／编码 → 原始递归表示。
签名、公理、对象推导放本目录；标准模型与任意模型的语义对应放 `YesMetaZFC/Model/Arithmetic/`。
使用现有 Lake 库，不另建嵌套工程，不导入 BMS 或 Mathlib。

接口、来源和本批验证见[实作说明](../../../markdown/ARITHMETIC_STATUS.md)，后续见[实施计划](../../../markdown/ARITHMETIC_PLAN.md)。
命名与 agent 协作遵循[上游规范](../../../markdown/AGENTS.md)和[命名规则](../../../markdown/ProofNaming.md)。
