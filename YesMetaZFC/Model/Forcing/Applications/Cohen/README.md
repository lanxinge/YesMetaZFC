# Cohen 实数与迭代

从单个外部 Cohen 实数到任意内部添加量、真实名称后继、有限支撑 CCC 和可数支撑 proper 迭代。

[总索引](../../INDEX.md) · [上级目录](../README.md)

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [Coordinates.lean](Coordinates.lean) | `CohenCoordinates.lean` | 参数化 Cohen 坐标的稠密要求 |
| [Presentation.lean](Presentation.lean) | `CohenPresentation.lean` | 参数化 Cohen 偏序的原公式规格 |
| [FlipSyntax.lean](FlipSyntax.lean) | — | 内部坐标集上的逐位翻转、条目像公式和单值性 |
| [Flip.lean](Flip.lean) | — | 保留内部有限性的实际条件自同构、翻转还原及固定空条件 |
| [Homogeneous.lean](Homogeneous.lean) | — | 用差异坐标翻转和有限并图证明弱齐性 |
| [OrdinalSubsets.lean](OrdinalSubsets.lean) | — | 呈现的 OD 性，以及自动构造地嵌入、不增加序数和恢复 OD 序数子集 |
| [HOD.lean](HOD.lean) | — | 仅需 ZF 的 `cohen_hod_comparison_l`：扩张 HOD 的对象均有地模型 HOD 原像 |
| [Add.lean](Add.lean) | `CohenAdd.lean` | 一次添加任意参数量的 Cohen 实数 |
| [Algebra.lean](Algebra.lean) | `Cohen.lean` | 一个 Cohen 实数的布尔条件代数 |
| [NameSyntax.lean](NameSyntax.lean) | `CohenNameSyntax.lean` | 规范 Cohen 名称的原公式规格 |
| [Names.lean](Names.lean) | `CohenNames.lean` | Cohen 后继的全局名称装配 |
| [TwoStep.lean](TwoStep.lean) | `CohenIteration.lean` | 扩张内部 Cohen 偏序的后继装配实例 |
| [Successor.lean](Successor.lean) | `IterationCohen.lean` | 添加量名称参数化的坐标后继实例 |
| [FiniteSupport.lean](FiniteSupport.lean) | `CohenIterationCCC.lean` | 参数化 Cohen 有限支撑迭代的一键 CCC 实例 |
| [Proper.lean](Proper.lean) | `CohenProper.lean` | 任意添加量名称的实际 properness 力迫证书 |
| [CountableSupport.lean](CountableSupport.lean) | `CohenIterationProper.lean` | 参数化 Cohen 可数支撑迭代的 proper 保持及完整区间实例 |
| [Real.lean](Real.lean) | `CohenReal.lean` | Cohen 名称及可数旧实数族之外的新实数 |
| [Theory.lean](Theory.lean) | `CohenTheory.lean` | Cohen 扩张中全公式真值的自动装配 |
| [Internal.lean](Internal.lean) | `InternalCohen.lean` | Cohen 条件与名称的实际内部实例 |
