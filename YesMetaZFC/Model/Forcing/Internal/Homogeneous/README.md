# 弱齐性与 OD/HOD 比较

`Whom_d M B R z` 表示任意两个非零条件 p、q 都有模型内自同构 π，使 π(p) 与 q 相容。
`whom_m` 是这一性质的原公式。Cohen 实例由差异坐标集上的实际位翻转证明，使用 ZF。

| 模块 | 主要结果 |
| --- | --- |
| [Basic.lean](Basic.lean) | 弱齐性原公式，以及地参数正文不能获得相反力迫判定。 |
| [Definition.lean](Definition.lean) | `gforce_m` 量化正条件及有限 check 参数，给出无泛型参数的原公式。 |
| [Truth.lean](Truth.lean) | `whom_ground_truth_l`：地模型的 Gforce 恰好计算泛型扩张中的地参数真值。 |
| [Recovery.lean](Recovery.lean) | 在旧集合上分离 Gforce，恢复具有旧参数定义的子集及其 OD[A] 证书。 |
| [OrdinalSubsets.lean](OrdinalSubsets.lean) | 取回序数参数与序数界，得到 OD 和固定参数 OD[A] 的序数子集比较。 |
| [HOD.lean](HOD.lean) | 恢复序数关系并内部坍塌，得到 HOD 和固定参数 HOD[A] 的完整比较。 |

Gforce 的 check 名称以所量化的条件为基点。自同构搬运后，在共同加强处使用
`check_force_bases_l` 交换基点，因此不假设偏序具有最大条件。
原公式翻译使用宿主有限 AST；内部 OD 定义通过已证的标准解码公式展开，仍允许地模型 ω 非标准。

设 e 是实际地嵌入。`whom_od_ordinal_subset_l` 在以下假设下恢复 X：

- 地模型满足 ZF，U 是给定内部条件序的泛型滤子。
- 条件序弱齐性，完整呈现 B、R、z 都是地模型中的 OD 集。
- X 在扩张中是 OD，且其每个成员在扩张中都是序数。

结论为存在地模型 OD 集 Y，使 e(Y)=X；不要求事先指定 X 的序数界。
`whom_ob_ordinal_subset_l` 将 OD 换为 OD[A]，扩张参数为 e(A)，呈现也只需属于 OD[A]。
`whom_ob_old_subset_l` 还处理任意 OD[A] 旧集合中的 OD[e(A)] 子集，因而可直接恢复代码关系。

[Cohen 的完整端点](../../Applications/Cohen/OrdinalSubsets.lean) `cohen_od_recovery_l`
只需实际 Cohen 呈现、序数添加量与泛型，自动证明呈现的 OD 性、弱齐性并构造地嵌入，
同时返回不增加序数和上述 OD 序数子集恢复结论。

## HOD 的坍塌恢复

`whom_hod_comparison_l` 在上述 ZF、泛型、弱齐性及完整呈现 OD 的前提下，自动构造
成员满的单射 e，并证明序数相同与

\[
\mathrm{HOD}^{M[G]}\subseteq e[\mathrm{HOD}^{M}].
\]

`whom_hb_comparison_l` 把呈现的假设放宽为 OD[A]，结论相应为
`HOD[e(A)]` 的每个对象都是某个地模型 `HOD[A]` 对象的像。两个接口均不要求调用者
另给编码、良基关系、坍塌函数或地嵌入。

证明分为三个实际构造：

1. [HOD/Presentation](../../../../SetTheory/InnerModel/HOD/Presentation.lean) 对 `TC({x})`
   收集定义码的序数界，保留全部有效代码并回拉隶属关系，得到 OD[A] 载体与关系。
2. 不增加序数提供旧序数界；弱齐性把载体及其有序对关系分别恢复为旧集合。
3. [Ground/Collapse](../Ground/Collapse.lean) 把内部良基性回拉，构造地模型的总坍塌图，
   再用扩张内部的坍塌唯一性识别 x。值域传递且所有值为 OD[A]，因此原像为 HOD[A]。

代码可以重复，坍塌把相同对象的代码送到相同值；这避免了背景 AC，也无需外部良基性。
包含方向由扩张指向地模型；定理不主张两边相等，也不主张任意 OD 集都来自地模型。
[Cohen/HOD](../../Applications/Cohen/HOD.lean) 的 `cohen_hod_comparison_l` 从实际呈现、
序数添加量和泛型自动取得全部假设及结论。
