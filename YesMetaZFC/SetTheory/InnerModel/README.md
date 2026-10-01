# J 层级与可容许递归

入口为 `YesMetaZFC.SetTheory.InnerModel`。当前工作沿 Jensen 的 rudimentary
有限基构造 J 层级，允许背景模型的自然数、序数和隶属关系在外部非标准、非良基。
OD、HOD 留待 J 层级与内部解释完成后发展。

## 已实现的数学接口

| 入口 | 结论与前提 |
| --- | --- |
| [KP/Sigma1](../KP/Sigma1.lean) | `KP.s1_collection_l` 同时收集 Σ₁ 输出和见证；`KP.d1_separation_l` 分离两条互补 Σ₁ 定义；`KP.s1_image_l` 构造 Σ₁ 单值关系的精确像集。只要求现有 KP。 |
| [KP/Kuratowski](../KP/Kuratowski.lean) | Kuratowski 编码的 Δ₀ 图及 KP 中的实际笛卡尔积。 |
| [Rudimentary/Syntax](Rudimentary/Syntax.lean) | 九个 Jensen 基础运算与四个传递性辅助运算的关系规格、Project 公式和语义对应；`rd_fun_unique_l` 只需外延性。 |
| [Rudimentary/Construction](Rudimentary/Construction.lean) | `rd_fun_exists_l` 在任意 KP 模型中构造全部十三项运算的输出。F₈ 的纤维族保留空纤维，也允许关系输入含非有序对对象。 |
| [Rudimentary/Graph](Rudimentary/Graph.lean) | 十三项运算均有真正的 Δ₀ 图；双向成员条件保证输出完整，不把任意容器内的截断输出当成函数值。 |
| [Rudimentary/Step](Rudimentary/Step.lean) | 一步扩张 `s(U)` 的 Δ₀ 图、KP 总性及传递性保持。 |
| [Axioms/KPInduction](../Axioms/KPInduction.lean) | 显式理论扩张 `KPi`：原 KP 加所有实际公式的成员归纳模式。 |
| [模型接口](../../Model/SetTheory/KPInduction.lean) | `KPi.models_iff_l` 给出精确语义，`KPi.induction_d` 接入原 Hilbert 核，`ZF.models_kpi_l` 给出现有 ZF 模型上的实例。 |
| [Recursion/Existence](Recursion/Existence.lean) | KPi 中任意实际 Σ₁ 全函数的内部成员递归；传递域上的 Δ₀ 证书先证明一致性，再用 Σ₁ 收集拼接，得到存在性、唯一性和递归方程。 |
| [KP/Natural](../KP/Natural.lean) | KPi 中实际构造内部 ω，证明最小性和自然数的序数性。 |
| [Rudimentary/Hull](Rudimentary/Hull.lean) | `rd_closure_s` 是闭包的实际 Σ₁ 正规形；`rd_closure_spec_l` 证明封闭、包含与最小性，并有唯一性、单调性和传递性保持。 |
| [Jensen/Hierarchy](Jensen/Hierarchy.lean) | `J_d` 的内部层级；`jh_value_exists_l`、`jh_value_unique_l`、`jh_zero_l`、`jh_successor_l`、`jh_limit_l` 给出存在唯一性及三种层级方程。 |

`S1_binary` 目前使用单个存在见证的 Δ₀ 矩阵正规形，矩阵和自由闭合性均携带
真实证书。已实现 Δ₀ 嵌入、复合和函数像集的正规形；尚未声称任意 Levy Σ₁ 语法的归一化、
内部程序求值与半可计算的双向翻译已经完成。

## 理论与模型的分层

仓库的 `KP` 使用集合正则公理。Jensen 的可容许递归使用完整的公式成员归纳；
二者在任意非标准模型上不能未经证明地混用。因此新增 `KPi`，保持原 KP 的
数学含义，并由实际 ZF 模型验证新理论的实例。

后续的 `V=L` 应是一条封闭的原 Project 句子：每个对象属于某个内部 J 层。
其中 J 层必须由已实现的 rudimentary 运算和内部递归公式给出，不能用尚无
实现的 `Constructible` 谓词或一个“全局良序存在”合同代替。

理论侧的最终目标是 `KPi + V=L` 中的原 `Derives` 证明。模型侧分别证明 J
层级存在、公式的内部化和相对化，以及所选内部宇宙满足该理论。现有 Σ₁
收集、Δ₁ 分离、像集和 rudimentary 总性是模型语义定理；没有将它们标作
已经完成的原推导核证书。

可容许递归按照已确定的范围发展：Σ₁ 对应半可计算，Δ₁ 对应可计算，参数
及计算见证均相对于所选模型。独立的程序语法和求值关系需要实际实现，再证明
与公式的双向转换；不以两个同义定义的重命名充当这一结果。基础收集与分离
无需 `V=L`，构造性假设用于进一步的规范编号、搜索和全局良序。

全局良序目标包括统一的序关系公式、集合大小的初段及其编码，而不只是一条
抽象全序。它在非标准背景中首先是内部良序，不能据此推出外部良基性。
单个任意 J 层也不能直接标成 KP 模型；必须证明所选高度的可容许性或另行
证明整个内部 J 宇宙的公理保持。

## 尚未完成

具体的 `V=L` 句子及其 Jensen 模型、规范全局良序、可容许程序与定义公式之间的
翻译均尚未实现。模型性还需证明 J 内的分离、收集和递归历史的内部识别；
不能把背景模型中的层级存在性直接当成 `J ⊨ V=L`。后续相对化
保留加入 `x ↦ x ∩ A` 的运算位置，但本入口目前没有宣称已构造 `L[A]`。

## 数学定义来源

Jensen 的 [第一章 §1.1](https://www.math.uni-bonn.de/~raesch/jensen/jensen/pdf/Jensen_Manuscript_Chapter_1_Transfinite_Recursion_Theory%29.pdf)
给出可容许性、Σ₁／Δ₁ 递归及公式归纳的约定；[第二章定理 2.2.15、引理 2.3.2](https://www.math.uni-bonn.de/~raesch/jensen/jensen/pdf/Jensen_Manuscript_Chapter_2_Basic_Fine_Structure_Theory.pdf)
给出采用的有限基和一步辅助运算。本层固定 Kuratowski 对及右嵌套三元组，
采用宏观索引 `J₀=∅`、`Jₐ₊₁=Rud(Jₐ∪{Jₐ})`、`Jλ=⋃ₐ∈λ Jₐ`。
递归算子统一写作所有前值的后继之并，再证明上述三条方程。尚未在 Lean 中
证明有限基与一般 rudimentary 项定义的等价定理，或与其他 J 索引约定的等价性。
