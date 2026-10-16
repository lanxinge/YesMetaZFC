# 参数化塌缩与迭代

可数部分函数塌缩、规范名称、确定规则、闭性与 properness，以及完整可数支撑迭代。

[总索引](../../INDEX.md) · [上级目录](../README.md)

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [Basic.lean](Basic.lean) | `Collapse.lean` | 地模型内部的可数部分函数塌缩 |
| [Generic.lean](Generic.lean) | `CollapseGeneric.lean` | 塌缩泛型函数的内部名称 |
| [Presentation.lean](Presentation.lean) | `CollapsePresentation.lean` | 可数部分函数偏序的原公式规格 |
| [Names.lean](Names.lean) | `CollapseNames.lean` | 可数部分函数后继的实际名称 |
| [Closed.lean](Closed.lean) | `CollapseClosed.lean` | 可数闭首阶段后的参数化塌缩 |
| [NameUniqueness.lean](NameUniqueness.lean) | `CollapseNameUniqueness.lean` | 塌缩后继名称的字面唯一性 |
| [NameSyntax.lean](NameSyntax.lean) | `CollapseNameSyntax.lean` | 规范塌缩名称三元组的原公式 |
| [RuleSyntax.lean](RuleSyntax.lean) | `CollapseRuleSyntax.lean` | 参数化塌缩的确定后继规则 |
| [Rule.lean](Rule.lean) | `CollapseRule.lean` | 参数化塌缩规则的存在、唯一性与闭性实例 |
| [Proper.lean](Proper.lean) | `CollapseProper.lean` | 参数化塌缩的实际 proper 后继规则 |
| [Iteration.lean](Iteration.lean) | `CollapseIteration.lean` | 任意内部长度的参数化可数闭塌缩迭代 |
| [FiniteSequence.lean](FiniteSequence.lean) | — | 内部有限序列的 Col(ω,X)，实际泛型满射 |
| [FiniteRecode.lean](FiniteRecode.lean) | — | 沿字母表双射精确重编码有限条件与泛型 |
| [Lift.lean](Lift.lean) | — | 共同低秩段固定小条件域，自动证明目标泛型性并提升初等嵌入 |
| [DenseNames.lean](DenseNames.lean) | — | 小坍缩之上大坍缩的有界全局稠密集名称库及完整覆盖 |

后两项服务于用户优化路线中的 7.22–7.23。实数吸收的迭代树及“每条共尾良基分支”
结论尚未完成；具体缺口见 [大基数入口](../../../../SetTheory/LargeCardinal/README.md)。
