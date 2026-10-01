# 完整 proper 迭代引理

固定前缀主加强、内部区间复合、后继与极限、超限归纳及全阶段保持装配。

[总索引](../../INDEX.md) · [上级目录](../README.md)

## 子目录

| 目录 | 模块数 | 职责 |
| --- | ---: | --- |
| [Model](Model/README.md) | 6 | 条件支撑、稠密枚举、实际辅助图、共同 N 与 proper 原公式规则。 |
| [Prefix](Prefix/README.md) | 3 | 旧商名称在变动主前缀下的比较、后继保持及极限还原。 |
| [Thread](Thread/README.md) | 13 | 实际 ω 递归状态、逐项选择、一致性、整列名称比较、共尾尾段、融合及主性。 |

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [Lemma.lean](Lemma.lean) | `IterationProperLemma.lean` | proper 迭代引理的内部命题与区间复合 |
| [Natural.lean](Natural.lean) | `IterationProperNatural.lean` | 内部有限阶段的完整区间迭代引理 |
| [Limit.lean](Limit.lean) | `IterationProperLimit.lean` | 任意内部极限的完整 proper 区间步骤 |
| [Master.lean](Master.lean) | `IterationMaster.lean` | 坐标后继的固定前缀主条件 |
| [Successor.lean](Successor.lean) | `IterationProperSuccessor.lean` | proper 后继的固定前缀主加强 |
| [SuccessorGeneric.lean](SuccessorGeneric.lean) | `IterationSuccessorGeneric.lean` | proper 迭代引理的完整相邻后继结论 |
| [Induction.lean](Induction.lean) | `IterationProperInduction.lean` | 任意内部序数上的完整 proper 区间迭代引理 |
| [Ground.lean](Ground.lean) | `IterationProperGround.lean` | 零前缀的迭代引理给出旧条件的真实主加强 |
| [Preservation.lean](Preservation.lean) | `IterationProper.lean` | 任意内部长度的可数支撑 proper 保持 |
| [Extension.lean](Extension.lean) | `IterationProperPreservation.lean` | 可数支撑迭代的 ZFC、ω₁ 与旧可数性保持 |
| [Dense.lean](Dense.lean) | `IterationProperDense.lean` | 已证明迭代区间的稠密主加强 |
| [Omega.lean](Omega.lean) | `IterationProperOmega.lean` | 首个内部极限的完整 proper 区间迭代引理 |
