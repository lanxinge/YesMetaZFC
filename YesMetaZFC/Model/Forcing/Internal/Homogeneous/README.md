# 弱齐性与 OD 序数子集恢复

`Whom_d M B R z` 表示任意两个非零条件 p、q 都有模型内自同构 π，使 π(p) 与 q 相容。
`whom_m` 是这一性质的原公式。Cohen 实例由差异坐标集上的实际位翻转证明，使用 ZF。

| 模块 | 主要结果 |
| --- | --- |
| [Basic.lean](Basic.lean) | 弱齐性原公式，以及地参数正文不能获得相反力迫判定。 |
| [Definition.lean](Definition.lean) | `gforce_m` 量化正条件及有限 check 参数，给出无泛型参数的原公式。 |
| [Truth.lean](Truth.lean) | `whom_ground_truth_l`：地模型的 Gforce 恰好计算泛型扩张中的地参数真值。 |
| [Recovery.lean](Recovery.lean) | 在旧集合上分离 Gforce，恢复具有旧参数定义的子集及其 OD[A] 证书。 |
| [OrdinalSubsets.lean](OrdinalSubsets.lean) | 取回序数参数与序数界，得到 OD 和固定参数 OD[A] 的序数子集比较。 |

Gforce 的 check 名称以所量化的条件为基点。自同构搬运后，在共同加强处使用
`check_force_bases_l` 交换基点，因此不假设偏序具有最大条件。
原公式翻译使用宿主有限 AST；内部 OD 定义通过已证的标准解码公式展开，仍允许地模型 ω 非标准。

设 e 是实际地嵌入。`whom_od_ordinal_subset_l` 在以下假设下恢复 X：

- 地模型满足 ZF，U 是给定内部条件序的泛型滤子。
- 条件序弱齐性，完整呈现 B、R、z 都是地模型中的 OD 集。
- X 在扩张中是 OD，且其每个成员在扩张中都是序数。

结论为存在地模型 OD 集 Y，使 e(Y)=X；不要求事先指定 X 的序数界。
`whom_ob_ordinal_subset_l` 将 OD 换为 OD[A]，扩张参数为 e(A)，呈现也只需属于 OD[A]。
这里处理序数集合；一般 HOD 集合的编码与坍塌恢复留给后续比较层，不声称恢复任意 OD 集。

[Cohen 的完整端点](../../Applications/Cohen/OrdinalSubsets.lean) `cohen_od_recovery_l`
只需实际 Cohen 呈现、序数添加量与泛型，自动证明呈现的 OD 性、弱齐性并构造地嵌入，
同时返回不增加序数和上述 OD 序数子集恢复结论。
