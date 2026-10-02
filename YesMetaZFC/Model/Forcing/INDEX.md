# Forcing 功能目录与构造脉络

382 个 Lean 模块按数学职责归入 11 个一级目录。各子目录的 README 列出全部文件、原平铺文件名和用途，并按导入依赖排列。

总入口仍为 `import YesMetaZFC.Model.Forcing`。细分导入使用下面的新路径；数学声明保持 `YesMetaZFC.Model.Forcing` 及其原有命名空间。

[语义边界与使用说明](README.md) · [迭代证明与调用接口](ITERATION.md)

## 功能导航

| 目录 | 模块数 | 内容 |
| --- | ---: | --- |
| [Order](Order/README.md) | 4 | 预序、相容性、稠密映射、分离商和有限序列条件。 |
| [Boolean](Boolean/README.md) | 5 | 非零布尔条件、正则开完备化、规范稠密映射及模型内编码。 |
| [External](External/README.md) | 11 | 早期外部名称求值、相对名称域、公式真值与可数泛型设施；保留其实际语义边界。 |
| [Internal](Internal/README.md) | 85 | 内部名称、泛型商、真值、ZFC 保持、自同构、不增加序数及弱齐性 OD/HOD 比较。 |
| [Stage](Stage/README.md) | 17 | 完全嵌入、复合、名称搬运、原子对应、泛型回拉及扩张嵌入。 |
| [TwoStep](TwoStep/README.md) | 51 | 实际二步偏序、名称转换、泛型分解、扩张同构及 CCC、proper、可数闭保持。 |
| [CCC](CCC/README.md) | 5 | CCC 原公式、有限部分函数实例、基数界和可数预稠密子族。 |
| [Proper](Proper/README.md) | 62 | 主条件、内部初等闭包、N[G] 提升、H(χ) 对应及 proper 扩张保持。 |
| [Closed](Closed/README.md) | 12 | 内部可数稠密交、名称下降链、不新增旧目标序列与可数子集，以及实际 proper club。 |
| [Iteration](Iteration/README.md) | 97 | 共同条件表示、内部超限递归、支撑极限，以及有限支撑 CCC、可数支撑 proper 和闭性保持。 |
| [Applications](Applications/README.md) | 33 | Cohen 添加、弱齐性与 OD/HOD 比较，可数部分函数塌缩和 CH 独立性；各实例接入对应的支撑迭代接口。 |

## 沿构造历史阅读

这里按本层实际发展的数学路线组织阅读，不把目录名当作额外的公理层级。单个定理的理论强度仍由参数和审计切片确定。

| 阶段 | 先读 | 随后得到 |
| --- | --- | --- |
| 1．通用偏序与布尔装配 | [Order](Order/README.md)、[Boolean](Boolean/README.md) | 加强方向、相容性、分离商、正则开完备化与稠密映射。 |
| 2．外部名称与泛型解释 | [External](External/README.md)、[Cohen 起始实例](Applications/Cohen/README.md) | 图求值、相对名称域、完整公式真值与新实数构造。 |
| 3．任意地模型的内部名称 | [Names](Internal/Names/README.md)、[Check](Internal/Check/README.md)、[Atomic](Internal/Atomic/README.md)、[Forcing](Internal/Forcing/README.md)、[Extension](Internal/Extension/README.md) | 内部规范递归、泛型商、ZFC 保持；适用于外部非良基及内部 ω 非标准的地模型。 |
| 4．CH 两侧构造与保持设施 | [CCC](CCC/README.md)、[Closed](Closed/README.md)、[Cohen](Applications/Cohen/README.md)、[Collapse](Applications/Collapse/README.md)、[Continuum](Applications/Continuum/README.md) | 参数化添加与塌缩、基数保持、CH 两侧模型及原推导核中的独立性。 |
| 5．二步装配与阶段比较 | [Maximum](Internal/Maximum/README.md)、[Stage](Stage/README.md)、[TwoStep](TwoStep/README.md) | 混合闭名称库、阶段完全嵌入、两阶段泛型、名称转换和摊平同构。 |
| 6．支撑迭代与内部递归 | [Condition](Iteration/Condition/README.md)、[Stage](Iteration/Stage/README.md)、[Limit](Iteration/Limit/README.md)、[Recursion](Iteration/Recursion/README.md)、[FiniteSupport](Iteration/FiniteSupport/README.md) | 任意内部序数长度的实际迭代、有限支撑直接并与 CCC 保持。 |
| 7．内部小模型与完整 proper 迭代 | [Proper](Proper/README.md)、[二步主条件](TwoStep/Proper/README.md)、[Fusion](Iteration/Fusion/README.md)、[区间迭代引理](Iteration/Proper/README.md) | N[G]、H(χ)、二步主条件分解、极限主前缀融合和全阶段 proper 保持。 |
| 8．可数闭迭代与保持装配 | [Closed](Iteration/Closed/README.md)、[闭扩张](Closed/README.md)、[塌缩迭代](Applications/Collapse/Iteration.lean) | 完整闭区间、不新增旧目标序列与可数子集、可数闭推出 proper，以及 ω₁、可数性和 ω 共尾性保持。 |

## 常用入口

| 工作 | 文件与接口 |
| --- | --- |
| 通用偏序与布尔完备化 | [Order/Basic.lean](Order/Basic.lean)、[Boolean/Completion.lean](Boolean/Completion.lean) |
| 任意地模型的 ZFC 泛型扩张 | [Internal/Extension/Choice.lean](Internal/Extension/Choice.lean)：`preserves_zfc_l` |
| CH 独立性 | [Applications/Continuum/Independence.lean](Applications/Continuum/Independence.lean)：`ch_independent_l` |
| 有限支撑 CCC 迭代 | [Iteration/FiniteSupport/RecursionCCC.lean](Iteration/FiniteSupport/RecursionCCC.lean)：`row_iteration_ccc_exists_l` |
| 完整 proper 区间与全阶段保持 | [Iteration/Proper/Induction.lean](Iteration/Proper/Induction.lean)：`row_iteration_pr_l`；[Extension.lean](Iteration/Proper/Extension.lean)：`row_iteration_preserves_l` |
| 可数支撑闭迭代 | [Iteration/Closed/Induction.lean](Iteration/Closed/Induction.lean)：`row_iteration_closed_exists_l` |
| Cohen／塌缩的可直接调用实例 | [Cohen/CountableSupport.lean](Applications/Cohen/CountableSupport.lean)、[Collapse/Iteration.lean](Applications/Collapse/Iteration.lean) |
| 名称自同构与力迫不变性 | [Internal/Automorphism/Forcing.lean](Internal/Automorphism/Forcing.lean)：`aut_forces_closed_l`、`aut_check_forces_l`；[Cohen/Flip.lean](Applications/Cohen/Flip.lean)：`cohen_flip_l` |
| 不增加序数与 OD 序数子集恢复 | [Ground/Ordinals.lean](Internal/Ground/Ordinals.lean)：`check_map_ordinals_l`；[Homogeneous/OrdinalSubsets.lean](Internal/Homogeneous/OrdinalSubsets.lean)：`whom_od_ordinal_subset_l`；[Cohen/OrdinalSubsets.lean](Applications/Cohen/OrdinalSubsets.lean)：`cohen_od_recovery_l` |
| 弱齐性 HOD 比较 | [Homogeneous/HOD.lean](Internal/Homogeneous/HOD.lean)：`whom_hod_comparison_l`、`whom_hb_comparison_l`；[Cohen/HOD.lean](Applications/Cohen/HOD.lean)：`cohen_hod_comparison_l` |

## 维护约定

新增模块放入相应职责目录，同步该目录的 README 和 `scripts/check_forcing.py` 中对应理论强度的审计切片。审计脚本检查目录中的每个模块都已登记。

跨领域的集合论或内部模型基础仍放在 `SetTheory`、`Model/SetTheory/Internal`，本层索引只组织力迫模块。总入口 `Model/Forcing.lean` 保持原有导出范围。
