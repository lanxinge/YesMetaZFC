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
| [Separation/Bounded](Separation/Bounded.lean) | `rd_separation_l` 从有限基的真值表和参数纤维构造 Δ₀ 分离集；分离封闭性是证明结论。 |
| [Jensen/Class](Jensen/Class.lean)、[Separation](Jensen/Separation.lean) | J 并类的实际 Σ₁ 定义、统一层界、类内分离及全部内部序数的包含性。 |
| [Jensen/Model](Jensen/Model.lean) | `l_model_l` 是实际隶属结构；`l_model_kp_l` 验证原 KP 的全部公理。 |
| [Jensen/Relativization](Jensen/Relativization.lean) | `l_rel_m` 相对化任意原公式，`l_rel_sat_l` 证明语义对应，`l_model_kpi_l` 证明 J 自身满足完整公式成员归纳。 |
| [Axioms/Constructible](../Axioms/Constructible.lean) | 封闭原句子 `vl_axiom`，理论 `KPL = KP + V=L`、`ZFL = ZF + V=L` 及各自原 `Derives` 公理证书。 |
| [Jensen/Constructibility](Jensen/Constructibility.lean) | `l_jh_value_iff_l` 双向识别 J 内外的层级；`l_model_vl_l` 证明原可构造公理，`l_model_kpl_l` 给出实际 `KPL` 模型。 |
| [Jensen/ZF/Reflection](Jensen/ZF/Reflection.lean) | `jl_cut_l` 将对构造查询封闭的传递集之 J 部分识别为一个实际 J 极限层；`jl_closed_layer_l` 从背景 Lévy 反射得到任意有限公式族的 J 见证闭包。 |
| [Jensen/ZF/Separation](Jensen/ZF/Separation.lean) | `l_model_full_separation_l` 反射量词子公式及反例，再用有界相对化和原 KP 分离构造任意原公式的分离集。 |
| [Jensen/ZF/Collection](Jensen/ZF/Collection.lean) | `l_model_full_collection_l` 将任意原公式相对化到 J，以背景全收集、J 部分筛选及统一层界构造内部见证集。 |
| [Jensen/ZF/PowerSet](Jensen/ZF/PowerSet.lean) | `l_model_power_l` 构造恰由 J 内部子集组成的幂集；其规格量化 J 的对象域。 |
| [Jensen/ZF/Model](Jensen/ZF/Model.lean) | `l_model_zf_l`、`l_model_zfl_l` 将同一结构提升为实际 ZF、ZF + V=L 模型，可直接调用仓库已有的 ZF 替换及递归接口。 |
| [Computation/Program](Computation/Program.lean)、[Totality](Computation/Totality.lean) | 独立的 `Cp_code`、关系求值 `Cp_eval_d` 及有界计算证书；`cp_eval_unique_l` 只需外延性，`cp_cert_total_l`、`cp_eval_total_l` 在原 KP 中证明总性。 |
| [Computation/Formula](Computation/Formula.lean)、[Sigma1](Computation/Sigma1.lean) | `cp_graph_s`、`cp_negative_s` 实际生成图及其补集的 Σ₁ 公式；`cp_graph_sat_l`、`cp_negative_sat_l` 证明这些公式恰定义求值和非求值，给出 Δ₁ 图。 |
| [Computation/Decision](Computation/Decision.lean)、[Delta0](Computation/Delta0.lean) | `Cp_test` 的集合程序、Δ₀ 公式两个后端；`cp_delta_l` 解析任意自由闭合 Δ₀ 公式并编译判定程序。`cp_delta_correct_l` 证明真值对应，`cp_parse_test_l`、`cp_delta_roundtrip_l` 证明反向编译的语法往返。 |
| [Computation/Sigma1](Computation/Sigma1.lean) | `cp_verifier_l` 把 Σ₁ 矩阵编译为实际见证验证程序，`cp_witness_s` 反向编译接受执行；`cp_verifier_roundtrip_l` 证明语义往返。 |
| [Computation/DSL](Computation/DSL.lean)、[Library](Computation/Library.lean) | `setfn!` 支持局部变量、集合表达式及 `union_for`。`cp_intersection_sat_l`、`cp_product_sat_l` 证明实际 DSL 程序分别计算交集和笛卡尔积。 |
| [Computation/Stage](Computation/Stage.lean)、[Search](Computation/Search.lean) | `Cs_code` 沿实际内部 J 层级扫描；`Cs_scan_d` 要求所有此前阶段实际返回空集，`cs_graph_sat_l` 在 KP 中把执行关系内部化为 Σ₁ 公式，`cs_eval_unique_l` 在 KPi 中证明唯一性。 |
| [Computation/SearchTotal](Computation/SearchTotal.lean) | `cs_scan_exists_l` 对实际原公式使用内部成员归纳：一旦某层命中，即有最早停机层，允许外部非标准、非良基模型。 |
| [Computation/Delta1](Computation/Delta1.lean) | `cd_compile_l` 把互补的两条 Σ₁ 正规形编译为同时搜索正反见证的程序；`cd_eval_total_l`、`cd_eval_iff_l` 在 KPi + V=L 中证明总性及完整布尔规格，`cd_basic_in_j_l` 接入实际 Jensen 模型。 |
| [Computation/Readback](Computation/Readback.lean) | `cs_pair_l` 把总搜索程序反向编译为互补 Σ₁ 定义；`cd_roundtrip_l` 证明语义往返，`cd_equiv_l` 给出 `D1_defined_d R ↔ Cs_computable_d R`。 |
| [ProofCode/Syntax](ProofCode/Syntax.lean)、[Rules](ProofCode/Rules.lean) | 叶码 `(0,α)` 与运算码 `(k+1,(a,(b,c)))`；固定标签使用实际有限序数码，局部规则及有界自然数标签都有 Δ₀ 公式。 |
| [ProofCode/Certificate](ProofCode/Certificate.lean)、[Uniqueness](ProofCode/Uniqueness.lean) | 历史每行记录内部自然数高度、码和值；`pc_eval_s` 是求值的实际 Σ₁ 正规形，`pc_eval_unique_l` 用模型内部归纳证明一致性。 |
| [ProofCode/WellFormed](ProofCode/WellFormed.lean)、[Erasure](ProofCode/Erasure.lean) | 语法历史只记录高度与码，检查时不查询 J 层值；`ps_eval_total_l` 证明合法码都有值，`ps_valid_iff_l` 识别精确求值域。 |
| [ProofCode/Coverage](ProofCode/Coverage.lean) | `pc_coded_iff_l` 证明 `Pc_coded_d x ↔ L_d x`；覆盖性通过 rudimentary 迭代与内部 J 层级归纳获得。 |
| [ProofCode/Table](ProofCode/Table.lean)、[SetCover](ProofCode/SetCover.lean) | `pc_table_s` 编译完整求值表，`pc_set_cover_l` 为任何成员均属 L 的模型内集合构造合法码集合及满射求值图。 |

`S1_binary` 使用单个存在见证的 Δ₀ 矩阵正规形，矩阵和自由闭合性均携带真实证书。
已完成见证验证，以及两条互补正规形所表达的 Δ₁ 关系与总 J 搜索程序的双向编译。
一般 Levy Σ₁ 语法转为这个正规形的归一化仍需进一步发展。

## 理论与模型的分层

仓库的 `KP` 使用集合正则公理。Jensen 的可容许递归使用完整的公式成员归纳；
二者在任意非标准模型上不能未经证明地混用。因此新增 `KPi`，保持原 KP 的
数学含义，并由实际 ZF 模型验证新理论的实例。

`Axioms.vl_axiom` 是封闭的原 Project 句子：每个对象属于某个内部序数处的 J 层。
其中层级由实际有限基、内部 ω 和 Σ₁ 递归证书定义。没有新加未解释的
`Constructible` 原子，也没有把全局良序作为替代公理。

理论侧入口为 `KPL` 和 `ZFL`，其定义和原推导核公理证书不要求使用者提供 Jensen
模型。模型侧的 `l_model_kpl_l` 从任意 `M.Models KPi` 构造实际 `KP + V=L`
模型；同时 `l_model_kpi_l` 给出该模型的完整成员归纳。上述基本构造只要求
KPi。ZF 扩展通过 `ZF.models_kpi_l` 使用同一结构，再由 `l_model_zf_l` 和
`l_model_zfl_l` 验证更强的原理论；没有复制层级定义或另造一个 ZF 版对象域。

证明顺序为：有限基真值表给出 Δ₀ 分离，背景 Σ₁ 收集给出统一层界，再验证
J 的 KP 与公式成员归纳。在 J 自身的 KPi 实例中运行同一递归定义，以 Σ₁
向上绝对性和背景唯一性识别内外层，最后验证 `V=L`。现有收集、分离和层级
构造主要是模型语义定理；没有将它们误标为已完成的原 `Derives` 证明。

ZF 全分离使用已有的背景 Lévy 反射：同时收集后继、J 层值、构造证书和目标
公式的有限见证查询。反射层中的 J 部分因而恰好是一层 `Jₐ`；该层上的有界
相对化与 J 中的原公式等价。幂集则从背景幂集中筛出属于 J 的子集，给出统一
J 层界，再在 J 内分离。整个证明允许背景模型在外部非标准、非良基。

可容许递归按照已确定的范围发展：Σ₁ 对应半可计算，Δ₁ 对应可计算，参数
及计算见证均相对于所选模型。本轮程序片段由十三个 rudimentary 运算、复合、
局部绑定和集合有界并合组成，求值不调用公式真值。真假分别用 ∅、{∅} 表示，
成员测试与逻辑联结都编译成实际集合运算。有限 `Cp_code` 的总性只需原 KP。
新增 `Cs_code` 是可能不终止的 J 搜索层，返回 ∅ 表示继续，返回 {y} 表示以 y 停机。
其 Σ₁ 执行证书在同一个内部集合中保存终止层及所有此前阶段的计算证据。
Δ₁ 编译每层分别检查正、反见证，返回 {1}、{0} 或 ∅；互补性保证结果正确，
V=L 提供包含实际见证的 J 层，KPi 的原公式归纳保证存在最早停机层。

`cd_equiv_l` 的前提明确是仓库的 `KPi` 加原句子 `Axioms.vl_axiom`。
执行关系的 Σ₁ 编译和 Δ₁ 程序的单向正确性只需 KP；证明没有调用 ZF。
这里的 Δ₁ 接口包含实际公式及互补性证据，`cd_basic_l` 与 `cd_basic_compl_l`
由已验证基础程序自动生成实例；`cd_basic_in_j_l` 无需再提供层级或枚举接口。

全局良序目标包括统一的序关系公式、集合大小的初段及其编码，而不只是一条
抽象全序。它在非标准背景中首先是内部良序，不能据此推出外部良基性。
这里证明的是所有内部 J 层的并类的公理保持；单层的可容许性仍需对其高度
另作证明，有限公式反射也不声称某一层满足全部 ZF。

## C 风格集合 DSL

```lean
def cp_product_l : Cp_code 2 := setfn! (x, y) {
  return union_for (a : x) {
    return union_for (b : y) {
      set p = opair(a, b);
      return pair(p, p);
    };
  };
}
```

形参依次对应寄存器 0、1……；`set` 引入局部绑定，可遮蔽外层同名变量。
`union_for` 遍历模型内部源集合并取各次返回值的并，所以例子返回每个有序对的
单元素集，再并合为笛卡尔积。循环不依赖宿主枚举顺序，也允许模型内部无限集合。

表达式包括空集 `{}`、差集 `-`、交集 `&`、二元并 `|`，优先级依次为 `-`、`&`、`|`。
原语调用有 `pair`、`diff`、`prod`、`mid`、`last`、`union`、`range`、`memrel`、
`fibers`、`opair`、`triple`、`adj`、`fiber`，布尔调用有 `has(x, y)`（x ∈ y）、
`subset`、`equal`、`not`、`and`、`or`。原语参数数目、未绑定变量和重复形参均在展开时检查。

编译器处理宿主侧有限语法，再把其计算关系内部化为实际 Project 公式；模型的自然数、
序数和隶属关系无需外部标准性或良基性。统一解释模型内部的非标准程序码属于后续层。
求值接口是模型中的关系规格；不把任意抽象模型的成员关系当作宿主可执行的判定器。

## J 构造推导码

独立入口为 `YesMetaZFC.SetTheory.InnerModel.ProofCode`。码本身是模型中的集合：
叶码引用一个内部序数处的 J 层，运算码引用三个子码。求值证书的高度属于
模型自身的自然数；子推导高度必须属于父高度，因此包含外部非标准的有限推导。
规则只使用已有 J 递归证书和十三个已验证集合运算。

语法证书与求值证书分开：前者只有 `(高度,码)` 行，后者有 `(高度,码,值)` 行。
`pc_eval_valid_l` 在 KP 中擦除值列；反向的 `ps_eval_total_l` 在 KPi 中构造值。
函数性、叶/运算证书的拼接、J 覆盖性以及集合大小求值表均已证明，不是前提字段。

规范码名取模型内三元组 `(α,n,c)`，要求 `α` 为序数、`n` 为内部自然数，
`c ∈ rud(α)` 且语法高度不超过 `n`。先比较 `α`，再比较 `n`，最后按叶参数、
运算标签和三个子码的字典次序比较 `c`。这里允许同一树有多个码名，尚未挑选最小代表。

`po_height_min_l` 用内部高度归纳证明固定高度的字典良序；
`pn_min_l` 证明每个模型内非空合法码名集合有最小元。
序律不依赖 V=L，也不假定模型外部良基。序数界放在高度之前，确保前驱能统一界在
`(α+1) × ω × rud(α)` 的三元组集合中；这是 `pn_initial_bound_l` 的结论。

`pn_lt_s`、`pn_not_lt_s` 是实际正反 Σ₁ 正规形；`pn_delta1_l` 证明它们在合法码名域互补。
合法性由 `pn_decode_s` 给出 Σ₁ 定义；`pn_eval_s` 将解码复合到原 J 求值。
`pn_cover_l` 证明所有 J 内对象都有这样的码名。
`pn_order_table_l` 自动构造指定合法码族上的比较表，并返回仓库已有的
`IsSetCodedWellOrder` 实例；`pn_initial_in_l` 构造该码族内的精确前段。

尚需构造包含全部合法前驱的精确全局初段，并据此证明 L 对象的最小代表存在及其
Σ₁ 定义。统一前驱界目前允许包含非法码名，不能直接作为完整求值表的定义域。
不受界的否定求值会提高复杂度，因此现有规范码序与求值表不被直接当作最小代表定理。

## 尚未完成

L 对象的规范全局良序、一般 Levy Σ₁ 归一化及通用 DSL 内部非标准程序码的统一解释器尚未实现；上节码名良序和 J 构造推导码的内部求值已实现。
当前总搜索等价仍使用 KPi + V=L；向原 KP + V=L 降低归纳前提需要另证。本层用 J 层级表达
可构造公理；与另行以 `Def` 递归定义的 Gödel L 层级之间的等价性尚未形式化。后续相对化
保留加入 `x ↦ x ∩ A` 的运算位置，但本入口目前没有宣称已构造 `L[A]`。

## 数学定义来源

Jensen 的 [第一章 §1.1](https://www.math.uni-bonn.de/~raesch/jensen/jensen/pdf/Jensen_Manuscript_Chapter_1_Transfinite_Recursion_Theory%29.pdf)
给出可容许性、Σ₁／Δ₁ 递归及公式归纳的约定；[第二章定理 2.2.15、引理 2.3.2](https://www.math.uni-bonn.de/~raesch/jensen/jensen/pdf/Jensen_Manuscript_Chapter_2_Basic_Fine_Structure_Theory.pdf)
给出采用的有限基和一步辅助运算。本层固定 Kuratowski 对及右嵌套三元组，
采用宏观索引 `J₀=∅`、`Jₐ₊₁=Rud(Jₐ∪{Jₐ})`、`Jλ=⋃ₐ∈λ Jₐ`。
递归算子统一写作所有前值的后继之并，再证明上述三条方程。尚未在 Lean 中
证明有限基与一般 rudimentary 项定义的等价定理，或与其他 J 索引约定的等价性。
