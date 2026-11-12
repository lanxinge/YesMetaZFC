# 大基数、迭代与 L(ℝ) 的决定性

公开终点为 [Determinacy/LReal](Determinacy/LReal.lean) 的 `wd_lr_ad_l`：
任意结构满足 ZFC 且内部有真类个 Woodin，即满足规范句子 `Axioms.lr_ad`。
`lr_ad_axiom_sat_l` 将其识别为实际 `lr_model_l` 满足 AD。

详细数学路线、关键不变量及前提边界见 [L(ℝ) 的 AD](../../../markdown/LR_AD.md)。
声明保留 `YesMetaZFC.SetTheory.LargeCardinal` 命名空间，文件按数学职责分类。

## 阅读顺序

| 目录 | 内容 |
| --- | --- |
| [Cardinals](Cardinals/README.md) | Woodin、派生测度、可测性、秩界及含指定参数的初始可数源 |
| [Extender](Extender/README.md) | 原关系扩展器、有限支撑超幂、Łoś、良基极限、秩保持及复制 |
| [Iteration](Iteration/README.md) | 原迭代树、活动边、两步复制、完整历史、nice 树与返回分支 |
| [Types](Types/README.md) | 类型、弹性、subtype/exceeds、一步伸展与精确实现高度 |
| [Game](Game/README.md) | 辅助闭博弈、档案、内部运行、奇偶分支及原局策略投影 |
| [Demand](Demand/README.md) | 深度调度、内部幂集编码、枚举、demanding 运行与分支覆盖 |
| [Absorption](Absorption/README.md) | 实数及稠密任务吸收、同实数极限、单向正确性和高度提升 |
| [Determinacy](Determinacy/README.md) | 正负查询树、坍缩覆盖、双树赢家、最小坏收益反证与最终 AD |

## 关键构造

`Woodin_d` 在 Vδ 中量化带谓词的实际初等嵌入，`Wd_proper_d` 要求它们在内部序数中无界。
大基数对象、公式码、满足关系、超幂代表和嵌入都在背景模型内部解释。
模型的外部非良基性和非标准自然数不被默默排除。

扩展器层先处理实际关系源和共同秩段，再构造有限支撑分量及整个直接极限。
迭代层从原操作产生复制历史；返回定理消费同一树和同一历史。
类型游戏保留实际排列及角色恢复，完整对局经前缀因果性投影回原博弈。
Demand 层通过奇祖先深度覆盖每条非偶数枝上的枚举任务。

吸收列同时服务实数与稠密任务，并保存交换返回因子。原测试 hull 的精确实数迹
等于极限派生实数族；备用 Woodin 吸收良序代码提升高度，并保持旧乘积与旧泛型。
同一较低 Jensen 层识别收益，规范策略实数及 Δ₀ 获胜条件完成最终下传。

## 支撑层

| 位置 | 职责 |
| --- | --- |
| [内部模型](../../Model/SetTheory/Internal/README.md) | 程序、真值、关系源、反射、超幂及模型间解释 |
| [坍缩](../../Model/Forcing/Collapse/README.md) | 有限支撑乘积、前缀名字、齐性、派生实数与无新实数 |
| [相对 Jensen](../InnerModel/Relative/README.md) | 规范 L(ℝ)、收益呈示、最小坏码及带符号见证 |
| [自然数博弈](../Descriptive/Game/README.md) | 内部策略、闭决定性及策略实数编码 |

## 范围

当前完成的是 ZFC＋真类 Woodin 版本。Neeman 原文“ω 个 Woodin＋上方可测”的较弱前提
版本仍需测度尾部的实际复制返回构造；不能把当前高度提升直接替换到那个前提下。
编码版 demanding 入口使用实际内部幂集单射及非空最小辅助域，其适用范围单列于数学说明。
不同 Woodin 刻画之间的完整形式化等价也不由当前对象定义自动给出。

```text
lake build YesMetaZFC.SetTheory.LargeCardinal.Determinacy.LReal
lake build YesMetaZFC.SetTheory.LargeCardinal
```
