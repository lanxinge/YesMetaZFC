# 可数分配力迫的 ZF 保持层

`Distributive_d B R z ω` 量化模型内部的集合关系 H；第 i 行是第 i 个稠密开集。
`distributive_intersection_l` 在 ZF 中把任意带有限参数的公式族收集为这样的关系码。
因此分配性与闭性分开，公共保持定理均不要求地模型选择公理。

| 接口 | 背景与结论 |
| --- | --- |
| `distributive_fn_dense_l` | ZF＋分配性；统一决定取值于旧集合的函数名称 |
| `no_new_reals_l` | ZF＋分配性；返回实数名称的实际旧子集原像 |
| `no_new_functions_l` | ZF＋分配性；返回旧值序列的实际旧函数图 |
| `no_new_countable_l` | ZF＋分配性；新可数旧集合的精确旧原像及旧可数性 |
| `distributive_countable_reflect_l`、`distributive_omega_one_l` | ZF＋分配性；反射可数性并保持 ω 的 Hartogs 数 |
| `distributive_extension_l` | 一次返回 ZF 模型性、规范嵌入及上述序列、子集、可数性、ω₁ 结论 |

可数子集的可数性使用自然数纤维的最小原像，不使用一般满射的纤维选择。
三个名称判定／反射接口还允许任意给定指标集，只要求该指标集上的相应分配性。

[Closed/Basic](../Closed/Basic.lean) 的 `closed_distributive_l` 在 ZF 中显式消费当前 ω 的
`Dc_d`，从内部可数闭性构造分配性实例。[DC 语义](../../SetTheory/DependentChoice.lean)
提供 `ZFDC.dc_l` 和 `ZFC.dc_l`；原 CH 构造与闭扩张入口直接使用这些实际实例。
`ZFDC` 是 ZF 加原对象语言的 DC 句子，`ZFC.models_zfdc_l` 证明所有现有 ZFC 模型实现它。

完整内部名称、任意原公式真值和 ZF 公理保持继续消费 ZF；本层没有将其宣称为 KP 结果。
properness、一般见证名称选择及支撑迭代保留各自现有背景要求。
