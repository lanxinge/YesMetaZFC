# 算术理论

本目录提供独立 Q/PA 及双排序 Z₂ 的最小语言、公理模式和对象推导。
`import YesMetaZFC.Logic.Arithmetic` 导入数码计算、PA 归纳、Z₂ 完整理解及其导出的全公式归纳。
模型性、任意模型中的可定义归纳及标准模型一致性从 `YesMetaZFC.Model.Arithmetic` 单独导入。
只需要 PA 时可导入 `YesMetaZFC.Logic.Arithmetic.PA.Induction`，不引入 Z₂。
一般加法规律由 `PA.Addition` 提供；乘法零律、单位律、后继律、交换律、双侧分配律与结合律由 `PA.Multiplication` 提供。
这些接口保留任意 PA 扩张、自由参数、局部假设与输入项，不仅适用于外部数码。
任意 PA 模型中的对应结果见 `YesMetaZFC.Model.Arithmetic.PA.Operations`，只消费推导可靠性。
`PA.Cancellation` 提供加法消去和零和定理；`PA.Order`、`PA.StrictOrder` 提供
可定义序的自反、传递、反对称、后继保持及严格序不可自返性的对象推导。
`Model.Arithmetic.PA.LinearOrder` 与 `Model.Arithmetic.PA.Minimum` 另证明任意 PA 模型中的全序性和
带任意参数的可定义最小元：归纳使用实际公式，不假定内部数域外部良基。
对象推导从 `Model.Arithmetic.PA.Provability` 按需导入：全序性、带余除法和最小化
由所有 PA 模型上的已证结论经上游一阶完备性得到，结论是原 `Derives`。
`Model.Arithmetic.Z2.Minimum` 将最小化推广到任意混合数／集参数公式，并提供非空内部数集的最小元。
PA 与 Z₂ 共用最小化推理，但分别构造所需的实际公式归纳实例，不对任意宿主谓词假设归纳。
`Model.Arithmetic.Z2.Provability` 提供混合参数最小化的对象推导。
两个可选完备性桥实际构造符号编码和公平调度，不要求调用者补交证书，且不进入基础入口。
共享的 `Minimum.candidate_m` 及模型语义允许任意签名、排序和参数，未预设关系为序。
`Division.graph_m` 是原算术语言中的商余关系；`Model.Arithmetic.PA.Division` 对非零内部除数
证明商余数存在且唯一，并证明规范商余关系排除零除数。`Division.domain_m` 是存在商余数的公式；
对象存在性接口仍显式保留除数非零条件。没有调用宿主自然数除法。
`Pairing.graph_m` 固定平方分层配对；正向总性／函数性在任意理论中可证。
`Model.Arithmetic.PA.PairingBounds` 与 `PA.Unpairing` 证明任意 PA 模型全数域上的
双射及左右投影图，不假定外部有限性。可选的 `PA.PairingProvability` 提供满射性、
单射性、左右投影总性与函数性的对象推导；可经既有 PA→Z₂ 翻译直接使用。
`FiniteRange` 的通用模板保留输入、输出和原参数。`Model.Arithmetic.PA.bound_m` 与
`Z2.bound_m` 分别对算术／混合公式证明内部有限函数的统一值域界，只要求所需截段上
存在唯一输出。两个可选 `Provability.bound_m` 提供任意长度项处的相应对象推导。

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
