# 真类 Woodin 与 L(ℝ) 的决定性

## 定理与语义

对任意结构 M，已证明

\[
M\models\mathrm{ZFC},\qquad
\forall\alpha\in\operatorname{Ord}^{M}\ \exists\delta>\alpha\;M\models\text{“δ 是 Woodin”}
\quad\Longrightarrow\quad M\models\mathrm{AD}^{L(\mathbb R)}.
\]

正式入口为 [终点](../YesMetaZFC/SetTheory/LargeCardinal/Determinacy/LReal.lean) 的 `wd_lr_ad_l`。输入为 `M.Models ZFC` 和 `Wd_proper_d`，
输出为 `M.SatisfiesSentence Axioms.lr_ad`。[L(ℝ) 的 AD 语义](../YesMetaZFC/SetTheory/InnerModel/Relative/PayoffQuerySound.lean) 的 `lr_ad_axiom_sat_l`
把该句子识别为规范 `lr_model_l` 满足 `Axioms.ad_axiom`。

实数是模型内部的 ω→ω 集合函数，策略是全部内部有限局面上的 ω 值函数。
AD 量化 L(ℝ) 自己的全部收益集、策略与对局。相对 Jensen 构造以 TC({ℝ}) 为种子；
`lr_model_zf_l` 只需背景 ZF，并保留全部原实数。内部 ω 不要求在外部标准。

Woodin 使用 Vδ 中的 A-strong 刻画：δ 不可达；对每个 A⊆Vδ，存在固定 κ<δ，
对每个 ν<δ 有带谓词初等嵌入，临界点 κ，j(κ)>ν，目标包含 Vν，且两谓词在 Vν 一致。
定义及原公式对应见 [Woodin 与初始源](../YesMetaZFC/SetTheory/LargeCardinal/Cardinals/WoodinInitial.lean)；所用数学刻画见
[Welch，定义 4.5 与定理 4.6](https://people.maths.bris.ac.uk/~mapdw/Birkbeck-NDJFL.pdf#page=15)。

## 证明的组织

大基数源码分为 Cardinals、Extender、Iteration、Types、Game、Demand、Absorption、Determinacy。
数学声明仍在原命名空间；模型语义和解释构造位于 `Model/SetTheory`，力迫位于 `Model/Forcing`。
各目录 README 列出合并后的模块及其数学内容，完整导航见[大基数目录](../YesMetaZFC/SetTheory/LargeCardinal/README.md)。

| 环节 | 可调用入口 | 产出的数学对象 |
| --- | --- | --- |
| 原反例 | [原反例](../YesMetaZFC/SetTheory/InnerModel/Relative/PayoffQuerySound.lean)：`lr_counterexample_data_l` | 固定二值实数参数、序数码、收益及 Δ₀ 非决定性证书 |
| 初始可数源 | [Woodin 与初始源](../YesMetaZFC/SetTheory/LargeCardinal/Cardinals/WoodinInitial.lean)：`wd_initial_l` | 含 Woodin 列及备用 Woodin 的可数传递源、实际返回图和泛型 |
| 吸收 | [反例吸收](../YesMetaZFC/SetTheory/LargeCardinal/Absorption/CounterLimit.lean)：`wd_counterexample_run_l`、`Ab_counter_run_d.limit_l` | 同一测试壳、完整运行、交换返回方块与精确实数迹 |
| 高度与收益 | [高度](../YesMetaZFC/SetTheory/LargeCardinal/Absorption/CounterHeight.lean)：`wd_counterexample_height_l`；[收益](../YesMetaZFC/SetTheory/LargeCardinal/Absorption/CounterPayoff.lean)：`wd_counterexample_payoff_l` | 超过测试壳的高度、同一实数族和同一收益的实际原像 |
| 固定参数决定性 | [双树与派生决定性](../YesMetaZFC/SetTheory/LargeCardinal/Determinacy/TwinTreeOutward.lean)：`qs_derived_det_l` | 任意序数码呈示的该参数收益具有内部获胜策略 |
| 规范策略运输 | [规范策略运输](../YesMetaZFC/Model/SetTheory/Images/GameCanonicalImage.lean)：`det_canonical_image_l` | 目标实数族上的有界获胜断言 |
| 最终反证 | [终点](../YesMetaZFC/SetTheory/LargeCardinal/Determinacy/LReal.lean)：`wd_lr_ad_l` | 排除原非决定性证书 |

## 扩展器、复制与类型博弈

扩展器层使用实际内部函数码、有限支撑及原关系超幂。Łoś 定理比较模型自己的
完整内部满足关系；代表归一化、分量间交换、直接极限和传递坍塌均产生实际集合图。
所属模型与施加父模型分别保留自己的秩层、幂集和函数码，不能混用两侧的闭包。

迭代层保存模型、树序、嵌入、操作、支撑和复制历史。后继构造实际产生两次施加，
极限通过相容图取并。[nice 树返回](../YesMetaZFC/SetTheory/LargeCardinal/Iteration/NiceReturn.lean) 从完整 nice 复制历史和移位下降秩得到返回分支；
它保留原树与指定返回嵌入，供后续吸收继续使用。

[一步伸展](../YesMetaZFC/SetTheory/LargeCardinal/Types/OneStep.lean) 的一步伸展保留原 subtype/exceeds 中允许的有限排列及同一扩展器。
辅助闭博弈的规则检查实际查询表；自然数输入、低层图和保存档案沿原关系图运输。
从辅助博弈策略取得原博弈策略时，必须证明每条服从对局的有限前缀恰好等于运行保存的前缀。
指定良基枝上的三张图相容取并后，第一张图恢复原对局，另两张图给出树分支见证。
坐标角色与排列的数学边界单列于[类型博弈](TYPE_GAME.md)。

## demanding 调度与实数吸收

奇枝任务按奇祖先深度调度。若某奇节点的深度为 d+1，令 (i,e)=unpair(d)，
从深度 i 的祖先枚举读取第 e 个对象，再沿实际边送到当前节点。
配对代码满足 i≤d，因此被读取的祖先严格早于当前节点。

每条非偶数共尾枝在每个深度恰经过一个奇节点。给定深度 i 的对象及其枚举编号 e，
深度 ⟨i,e⟩+1 的节点必服务该任务。覆盖由奇父链和深度后继方程推出，
不向调用者要求每条枝命中特定的全局轮号。

枚举的可数性来自源内部的实际单射 U₁↪𝒫(δ) 与幂集成员载体计数。
有限支撑超幂通过有界函数码保持该计数；它包含新模型的全部相关字母，
不仅包含旧模型的像。稠密集族和规范名字族分别构造所需的内部编码。
本接口保留最小第一辅助域非空的前提；不据此宣称任意外部可数辅助域的原版 7.8 已实现。

收缩映射在原域上为恒等，树沿收缩映射拉回，首层补全保持最小辅助域。
这一组合把 demanding 的分支输出接到实际坍缩泛型及指定实数名字值。
`ag_absorb_l` 消费可数源、Woodin 和给定秩层返回图，产生同一次运行的真实返回枝。

## 派生实数与无新实数

固定内部 Woodin 列的有限支撑坍缩乘积 Q 及泛型 H，令

\[
\mathbb R^*[H]=\bigcup_{n<\omega}\mathbb R^{N[H\restriction n]}.
\]

规范名字、前缀泛型及名字解释都属于同一个乘积。尾部自同构固定前缀参数，
给出有限实数参数断言的稳定性，并用于逐数字恢复定义所得实数。
相对 Jensen 层中的对象由实数基集、一个内部有限参数列和地序数码定义；
有限列有实际共同前缀，齐性遂把实数恢复到该前缀扩张。

因此派生 L(ℝ*) 的完整 Baire 空间恰为 ℝ*。这一步是实际无新实数定理，
不能用“把 ℝ* 叫作实数基集”的约定代替。规范参数表示、最小坏收益和后续策略编码
都消费这份完整空间识别。实现集中于[坍缩层](../YesMetaZFC/Model/Forcing/Collapse/README.md)。

## 带返回图的吸收列

先固定原反例的实数参数 a，取含 a、Woodin 列及备用 Woodin 的可数秩层 hull N₀。
再取包含原反例定义资料、N₀、返回图及计数见证的测试 hull P。反坍塌逐点固定自然数及 a。
测试壳只承担有限反射和已构造闭包，不被额外赋予 ZF。

同一状态记录当前模型、乘积、有限前缀泛型、待处理实数和稠密任务、返回因子及历史。
保存前缀在后续步骤中不变；公平调度使每个测试实数被吸收，每个目标稠密集被命中。
极限返回图由实际相容图得到，并与零轮嵌入组成交换方块。

正向包含来自每个实数任务的实际名字值；反向包含来自前缀名字的回读。
两者给出字面相等 ℝ*[H]=ℝ∩P。弱测试壳的实数迹在此始终与背景全部实数区分。
同一构造还提供 Σ₁(ℝ) 单向正确性 `ab_lemma85_l`，见 [吸收正确性](../YesMetaZFC/SetTheory/LargeCardinal/Absorption/QueryHull.lean)：
有限实数参数及存在见证经共同 Jensen 层送入真实背景 L(ℝ)。

## 最小坏收益与双树

固定 a 及收益呈示公式。若某序数码给出不决定收益，内部最小化取得最小坏码。
无新序数把该码回收到地模型；尾部齐性把最小性统一到顶条件。
正负查询共用同一最小性和参数，只改变查询实数属于收益的符号。

查询树的任意分支实际构造可数源和泛型，单向正确性把其见证送到真实 L(ℝ)。
最小坏收益的唯一性排除正负投影的交集。统一小坍缩证明两树覆盖扩张中的全部实数；
双树定理给出地面赢家及反方反例树的序数秩。
把同一投影识别为最小坏收益，就与其非决定性矛盾。

固定参数决定性沿实际返回初等图使用此结论：十二项乘积、名字、参数及力迫资料整体运输，
仅在真实返回秩层调用顶条件矛盾。可数出发模型自身不必拥有背景不可数基数。
较小 Woodin 的界约束的是第一坐标的真实返回像。

## 高度提升与最终反证

由 P 的实际计数构造其可数序数高度 β，并将 β 编码为实数。
在备用 Woodin 以下先选共同低秩界，覆盖原乘积及规范名字；再吸收这个良序代码。
序型回收给出 β 属于新源，同时低秩固定性保持旧 H 泛型和原 ℝ*。

原反例的 Jensen 层号及序数参数属于 P，故低于 β；它们在高源中有实际原像。
名字扩张的背景坍塌识别同一实数基集及传递种子，相对 Jensen 递归唯一性识别同一较低层。
在派生模型中分离得到的收益，其背景像于是精确等于原反例收益。

固定参数决定性给出实际获胜策略。全部有限局面的规范自然数单射把策略编码为一个实数，
该实数仍属于 ℝ∩P。完整有限局面空间、编号和自然数上的奇偶判断被逐项对齐，
Δ₀ 获胜条件沿成员满嵌入运输，直接反驳原 `¬Gs_det_d`。

## 前提边界

- 当前终点使用 ZFC＋真类 Woodin；没有宣称降低到 Neeman 原文的全部前提范围。
- [Neeman 定理 8.24](https://www.math.ucla.edu/~ineeman/detLR.pdf/#page=78)
  的“ω 个 Woodin＋上方可测”版本仍需测度尾部及其实际复制返回构造。
- 当前终点先固定参数再选 hull，不要求先证明任意新参数的完整派生模型 AD。
- Vδ 中的 Woodin 定义已给出公式语义对应；与所有其他大基数刻画的形式化等价另行处理。
- 本文的数学路线采用 Neeman 预印本及项目审阅稿的改进。角色坐标的讨论属于仓库论证，
  不标作作者正式勘误。

## 使用

```lean
import YesMetaZFC.SetTheory.LargeCardinal.Determinacy.LReal
-- YesMetaZFC.SetTheory.LargeCardinal.wd_lr_ad_l
```

```text
lake build YesMetaZFC.SetTheory.LargeCardinal.Determinacy.LReal
```

公共汇总入口仍为 `YesMetaZFC.SetTheory.LargeCardinal`。模块路径与声明命名空间分开维护；
调用者直接使用新模块路径及原定理名。
