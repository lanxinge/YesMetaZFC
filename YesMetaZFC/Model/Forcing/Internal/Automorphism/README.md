# 内部条件自同构与名称作用

条件自同构 `Aut_d M B R z F` 是地模型中的双射图，保持序关系及排除值。
对应的原公式为 `aut_m`；其语义定理 `aut_sat_l` 只要求外延性。

名称作用直接使用已有 `Nmap_d M F x y` 及其内部递归构造，不另设名称类型或外部递归函数。
自同构保留全部标签，包括可能存在的零标签，所以恒等及逆作用是模型对象的严格相等。

| 模块 | 主要结果 |
| --- | --- |
| [Basic.lean](Basic.lean) | 原公式、条件加强的对应，以及实际恒等图、逆图和复合图。 |
| [Names.lean](Names.lean) | 严格逆作用、名称单射与满射、复合律，以及 check 名称的基条件搬运。 |
| [Atomic.lean](Atomic.lean) | 在闭支撑上构造实际双模拟，证明等号和隶属力迫不变。 |
| [Forcing.lean](Forcing.lean) | 全部原公式、有限 bound 参数及固定 check 参数的力迫不变性。 |

在 `M.Models ZF` 下，`nmap_exists_l` 构造每个名称的像，`nmap_unique_l` 保证唯一；
`aut_nmap_inverse_l` 给出逆图上的严格还原，`aut_nmap_onto_l` 为量词提供名称原像。
`aut_forces_closed_l` 对自由闭合的原公式只要求有限 bound 参数的名称与作用证书。
这里的公式是宿主给出的原 Project 公式；未把该结论声称为模型内任意非标准公式码的统一力迫定理。

`aut_check_l` 将基条件 b 上的 check 名称送到 π(b) 上的 check 名称。
仅当 b 固定时才由 `aut_check_fixed_l` 得到逐对象固定；`aut_check_forces_l` 随后保持有限地参数公式的力迫。
没有顶条件的预序不能直接省略这一条件。

[Cohen 翻转](../../Applications/Cohen/Flip.lean)在任意内部坐标集上构造实际自同构，且固定空函数这一最大条件，
因此可直接调用上述地参数接口。[弱齐性比较层](../Homogeneous/README.md)进一步交换 check 基点，
处理无最大条件的地参数真值，并恢复 OD 序数子集。

所有递归、收集和双模拟证书都在模型内部；不要求外部良基性、外部可数性或背景选择公理。
