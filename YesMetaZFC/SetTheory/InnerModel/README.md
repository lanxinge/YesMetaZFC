# J 层级、OD、HOD 与可容许递归

当前已完成 Jensen J 层级及其 L 内模型的 ZFC＋GCH、J 层内统一局部良序、
OD/HOD 的内部定义与参数模型，以及弱齐性力迫的 HOD 比较。本文按可调用定理
整理研究进度；详细实现沿“J 与计算 → 良序 → 凝聚与 GCH → OD/HOD → 力迫比较”阅读。

内模型入口为 `YesMetaZFC.SetTheory.InnerModel`；力迫比较另导入
`YesMetaZFC.Model.Forcing.Internal.Homogeneous.HOD`，或总入口 `YesMetaZFC.Model.Forcing`。
底层 [规范编码](../../Model/README.md) 支持内部有限序数列、公式码及统一满足关系。
全部模型侧结论允许背景 ω 非标准、隶属关系外部非良基；良序、序数、有限性和幂集
始终按所选模型解释。代码中的 ZF 前提不包含该模型的选择公理。

## 进度总览

| 研究层 | 已完成的可调用结果 | 所需背景与范围 |
| --- | --- | --- |
| J 闭包、层级与可构造公理 | [Jensen/Constructibility](Jensen/Constructibility.lean)：`l_model_kpl_l`、`l_model_kpi_l` | KPi 构造实际 J 并类；其满足 KP＋V=L 及完整公式成员归纳 |
| 基本集合计算与 DSL | [Totality](Computation/Totality.lean)、[Delta0](Computation/Delta0.lean)、[Sigma1](Computation/Sigma1.lean)、[DSL](Computation/DSL.lean) | KP；基础运算、Δ₀ 判定及 Σ₁ 见证验证的双向编译，提供 `setfn!` 前端 |
| Δ₁ 可定义与可计算等价 | [Readback](Computation/Readback.lean)：`cd_equiv_l` | KPi＋V=L；互补 Σ₁ 正规形与总 J 搜索布尔程序对应 |
| 全局及逐层 Jensen 良序 | [Order/Statement](Order/Statement.lean)：`jh_order_model_l`；[Uniform](Order/Uniform.lean)：`jh_local_sigma1_l` | KPi；每个非空 J 层统一局部 Σ₁，比较为 Δ₁，完整初段留在同层；无需该层可容许 |
| 坍塌凝聚 | [Condensation](Condensation.lean)：`jc_bounded_condensation_l` | KPi；任意内部大小的 Σ₁ 子结构坍塌为唯一 J 层，并有高度界 |
| L 的最终模型 | [GCH/Model](GCH/Model.lean)：`l_model_gch_l` | 背景仅 ZF；同一实际 L 模型满足 ZFC＋GCH，内部解释后继基数及幂集 |
| OD/HOD 成员、最小码及选择 | [OD](OD.lean)、[HOD](HOD.lean)：`od_iff_external_l`、`hod_sigma_sat_l`、`hod_model_choice_l` | ZF；内部定义、Σ₂ 成员证书、OD 最小代表与全局良序、HOD 选择集 |
| 两种参数内模型 | [BracketChoice](HOD/BracketChoice.lean)：`hb_model_zfc_l`；[Models](HOD/Models.lean)：`hp_model_zf_l` | ZF；HOD[A] 满足 ZFC，HOD(A) 满足 ZF；圆括号使用内部有限 A 参数列 |
| 弱齐性 HOD 比较 | [Homogeneous/HOD](../../Model/Forcing/Internal/Homogeneous/HOD.lean)：`whom_hod_comparison_l`、`whom_hb_comparison_l` | ZF、泛型及弱齐性；完整呈现为 OD 或 OD[A]，扩张 HOD 恢复到地模型；已有 Cohen 实例 |

本表的模型性是对原 Project 公理和模式的实际语义证明。可构造公理已接入原演绎核，
但不能把每项模型语义定理自动视为已给出的 `Derives` 证明。理论强度的精确区分见
[理论与模型的分层](#理论与模型的分层)，尚缺的接口统一列在[尚未完成](#尚未完成)。

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
及计算见证均相对于所选模型。程序片段由十三个 rudimentary 运算、复合、
局部绑定和集合有界并合组成，求值不调用公式真值。真假分别用 ∅、{∅} 表示，
成员测试与逻辑联结都编译成实际集合运算。有限 `Cp_code` 的总性只需原 KP。
`Cs_code` 是可能不终止的 J 搜索层，返回 ∅ 表示继续，返回 {y} 表示以 y 停机。
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
运算标签和三个子码的字典次序比较 `c`。同一树允许有多个码名；对象随后按其唯一最小码名排序。

`po_height_min_l` 用内部高度归纳证明固定高度的字典良序；
`pn_min_l` 证明每个模型内非空合法码名集合有最小元。
序律不依赖 V=L，也不假定模型外部良基。序数界放在高度之前，确保前驱能统一界在
`(α+1) × ω × rud(α)` 的三元组集合中；这是 `pn_initial_bound_l` 的结论。

`pn_lt_s`、`pn_not_lt_s` 是实际正反 Σ₁ 正规形；`pn_delta1_l` 证明它们在合法码名域互补。
合法性由 `pn_decode_s` 给出 Σ₁ 定义；`pn_eval_s` 将解码复合到原 J 求值。
`pn_cover_l` 证明所有 J 内对象都有这样的码名。
`pn_order_table_l` 自动构造指定合法码族上的比较表，并返回仓库已有的
`IsSetCodedWellOrder` 实例；`pn_initial_in_l` 构造该码族内的精确前段。

`Pg_level_d T n Y` 是实际的内部语法检查器：从前值的并中读取子码，并在 `T` 中作
Δ₀ 分离。`pg_level_height_l` 证明其成员恰为 `T` 内语法高度不超过 `n` 的码，允许
`n` 外部非标准。正反证书计算同一个语法层和 rud 闭包，因此能在上述候选界内精确分离合法码名。

`pi_initial_s` 的图由 `pi_initial_sat_l` 验证：输出集合恰含目标码名的所有合法严格前驱。
`pm_min_exists_l` 在此前段加端点的完整求值表中分离同值纤维，再取码序最小元；
`pm_min_unique_l` 证明全局唯一性，`pm_min_s`、`pm_min_sat_l` 给出实际 Σ₁ 图。
最小性证书只否定完整表中的条目，不否定无界 Σ₁ 求值。

## 目标全局良序

| 接口 | 已证明的内容 |
| --- | --- |
| `lo_lt_s` / `lo_lt_sat_l` | L 对象按唯一最小 J 码名排列，无参数 Σ₁ 定义 |
| `lo_compare_l` / `lo_trans_l` / `lo_min_l` | 严格线序及每个模型内非空 L 对象集合的最小元 |
| `lo_delta1_l` | 正反 Σ₁ 证书在 L 域上互补，即 Δ₁ 判定 |
| `lo_initial_s` / `lo_initial_sat_l` | 对象的精确全局前驱集合；其函数图为无参数 Σ₁ |
| `lo_order_table_l` | 任意 L 对象集合上的实际 `IsSetCodedWellOrder` 实例 |
| `lo_universe_l` / `lo_l_model_l` | KPi + V=L 以及具体 Jensen 模型满足原 Project 全局良序句子 |
| `lo_l_absolute_l` / `lo_rel_sat_l` | 背景比较、J 内部比较和公式相对化结果一致 |
| `lo_initial_in_l_l` | 每个 L 对象的精确初段本身属于 L |

背景中只要求 KPi；V=L 仅在把此序视为整个背景宇宙的全局良序时使用。
`lo_universe_s` 是已证明的目标句子，没有作为新增公理加入理论。
这些良序结论均按模型内部集合解释，不声称非标准模型的关系外部良基。

## J 层的统一局部 Σ₁ 定义

逐层构造采用 `S(U)=s(U∪{U})`：保留旧序，按固定 rud 运算菜单、输入三元组的
字典最小原像依次追加新对象。原 `lo_*` 的 L 并类绝对性不直接给出小 J 层中的局部性。

| 接口 | 已证明的内容 |
| --- | --- |
| [Order/Successor](Order/Successor.lean) 的 `rw_successor_correct_l` | 实际微后继载体、集合编码良序及端延拓；只需背景 KP |
| [Order/Sigma1](Order/Sigma1.lean) 的 `rw_successor_s`、`rw_successor_sat_l` | 同一 Δ₀ 验证矩阵产生规范微后继的 Σ₁ 图，且输出存在唯一 |
| [Rudimentary/SetImage](Rudimentary/SetImage.lean) 的 `rd_step_closed_l` | 传递 U 属于有限基闭包 C 时，整个 s(U) 属于 C；未假定 C 满足 KP |
| `rw_successor_carrier_closed_l` | 微后继载体自身属于同一个 rud 闭包 |
| [Jensen/Definable](Jensen/Definable.lean) 的 `jh_definable_l` | 任意原公式在非空 Jₐ 内定义的子集属于 Jₐ₊₁；不要求 Jₐ 可容许 |
| [Order/Coherence](Order/Coherence.lean) 的 `js_coherence_l`、`js_end_l` | 有序微层级的内部递归、各层实际良序及端延拓 |
| [Order/LocalSuccessor](Order/LocalSuccessor.lean) 的 `rw_successor_absolute_l` | 规范微后继的同一 Σ₁ 公式在传递 rud 闭包中的局部解释 |
| [Order/HistoryLocal](Order/HistoryLocal.lean) 的 `js_state_in_l` | 若微层 Sᵦ 本身属于传递 rud 闭包 C，则其完整递归证书也属于 C |
| [Order/Access](Order/Access.lean) 的 `js_cut_l` | 以有界可见历史收集真实序数截口，识别由较早微层覆盖的闭包 |
| [Order/Macro](Order/Macro.lean) 的 `jh_order_rep_l` | 原宏观 Jₐ 是同一有序微层级中的实际一层，不增设索引对应假设 |
| [Order/Uniform](Order/Uniform.lean) 的 `jh_local_sigma1_l` | 固定无参数 Σ₁ 公式 `js_less_s` 在每个非空 Jₐ 内定义 `Js_lt_d` 的限制 |
| `jh_local_wellorder_l`、`jh_order_initial_l` | 合并实际集合编码良序与层内定义，并证明各 Jₐ 都是全局序的初段 |
| [Order/InternalState](Order/InternalState.lean) 的 `js_l_value_iff_l`、`js_value_constructible_l` | 内外有序微层及关系表一致，微层本身和关系表均属于 L |
| [Order/Initial](Order/Initial.lean) 的 `jh_initial_in_l` | 每个 x∈Jₐ 的完整全局前驱集合本身属于同一个 Jₐ |
| [Order/InitialSigma1](Order/InitialSigma1.lean) 的 `js_initial_s`、`jh_initial_local_l`、`jh_initial_function_l` | 初段函数的实际 Σ₁ 图在每层内都可靠、完备且有唯一输出 |
| [Order/Global](Order/Global.lean) 的 `js_min_l`、`js_delta1_l`、`jh_local_delta1_l` | 全局最小元与正反 Σ₁ 证书；同一对公式在每个非空 J 层内互补 |
| [Order/Internal](Order/Internal.lean) 的 `js_l_absolute_l`、`js_initial_l_absolute_l` | 比较和初段在实际 Jensen 模型内外一致；`js_rel_sat_l`、`js_initial_rel_sat_l` 给出原公式相对化接口 |
| [Order/Statement](Order/Statement.lean) 的 `js_universe_l`、`js_l_model_l`、`jh_order_model_l` | KPi + V=L、实际 Jensen 模型以及每个非空 J 层满足同一全局良序句子，包含严格初段集合性 |

公共真值表现在支持坐标映射；原 Δ₀ 分离直接复用完整定义集构造。
上述接口允许背景模型外部非标准、非良基，所有存在性均以集合关系证明。
完整局部定理只要求背景满足 KPi；不要求 Jₐ 本身满足 KP、可容许性或收集模式。
对所有 x,y∈Jₐ，同一个无参数公式满足
`Jₐ ⊨ js_less_s(x,y) ↔ Js_lt_d(x,y)`。因此不同层在共同对象上的比较自动一致。
J₀ 的空良序也已包括在 `jh_local_wellorder_l` 中；非空条件仅用于建立仓库的非空结构载体。

完整前驱集合 `Iₓ={y : Js_lt_d(y,x)}` 留在包含 x 的每一个 Jₐ 中，
`js_initial_s` 在该层内部准确计算 Iₓ。证明从更早微层的状态证书读取关系表，
只用 Δ₀ 分离构造完整初段；端延拓排除了层外遗漏的前驱。
`jh_order_model_l` 表达的是单层满足这条特定良序句子，并不据此赋予该层 KP 模型性。

[通用句子模板](../Definitional/Project/GlobalOrder.lean) 的 `gw_sentence_s` 只接受原二元公式；
`gw_sentence_sat_l` 在外延结构中展开其严格线序、集合最小元及初段集合性语义。
原 `lo_universe_s` 与新 `js_universe_s` 都已直接使用此模板，未加入新理论公理。

极限阶段使用 Δ₀ 查询精确收集可见的短历史，重用较早层作为所有旧见证的共同界。
宏观层的识别通过最小 rud 闭包和序数截口证明，没有假设微层与原层级的等价性。
`Js_lt_d` 是逐层端延拓得到的 Jensen 序；上节 `lo_*` 是最小构造码名序。
两者各有已证接口，当前没有声称这两个关系逐点相同。

## 坍塌凝聚及 GCH 前件

入口为 [Condensation](Condensation.lean)，通用隶属坍塌入口为
[SetTheory/Collapse](../Collapse.lean)。对模型内部的任意大小集合 X，
`S1_sub_d X U` 以实际“∃见证＋Δ₀ 矩阵”及任意有限参数表达 Σ₁ 初等性。
在背景 KPi 中，X≺Σ₁Jₐ 的传递坍塌是唯一的原 Jᵦ，且有实际单射 β→X。

| 接口 | 结论与前提 |
| --- | --- |
| [Collapse/Recursion](../Collapse/Recursion.lean) 的 `mc_value_exists_l`、`mc_value_equation_l` | π(a)={π(b):b∈a∩X} 的实际内部递归；背景 KPi |
| [Collapse/Mostowski](../Collapse/Mostowski.lean) 的 `mc_collapse_l` | 外延隶属子结构的传递值域、集合图及隶属同构；`Mc_iso_d.bijection_l` 接入原集合双射接口 |
| [Collapse/Uniqueness](../Collapse/Uniqueness.lean) 的 `mc_iso_unique_l` | 任意传递坍塌均等于规范递归，值域和图均唯一 |
| [Collapse/Transport](../Collapse/Transport.lean) 的 `Mc_iso_d.formula_l` | 通过集合编码同构传输原公式，有限参数逐项回拉 |
| [Condensation/Recognition](Condensation/Recognition.lean) 的 `jc_rud_macro_l` | rud 封闭微层必是原宏观 J 层；通过原公式内部归纳证明 |
| [Condensation/Collapse](Condensation/Collapse.lean) 的 `jc_condensation_l`、`jc_condensation_unique_l` | Σ₁ 子结构坍塌到唯一原 J 层；没有可数性或外部良基性前提 |
| [Condensation/Size](Condensation/Size.lean) 的 `jc_bounded_condensation_l` | 同时返回实际高度单射 β→X；若 A 传递、A⊆X、x∈X 且 x⊆A，则 π(x)=x |
| [Condensation/Internal](Condensation/Internal.lean) 的 `jc_internal_l` | 直接消费已有全内部 `Selem_d` 证书；解码原公式的现有接口要求背景 ZF |
| `jc_countable_hull_l` | 从现有内部可数种子实际构造初等壳及其凝聚；壳构造使用 ZFC，凝聚主定理不限于可数壳 |

证明先构造 Mostowski 集合图，再把 rud 运算及完整微层证书的存在式传入坍塌。
传递值域于是 rud 封闭并由可见微层覆盖；规范截口和宏观层识别给出 Jᵦ。
高度界通过 γ↦Jγ 的集合编码单射及坍塌逆图取得，只需 KPi。
取 A=κ 后，X 中的 κ 子集均被坍塌固定并属于 Jᵦ，这是后续 GCH 论证需要的保持结论。

## GCH 与 ZF 背景下的最终模型

[GCH](GCH.lean) 的 `l_model_gch_l hZF` 证明：任意 ZF 模型中的同一实际 Jensen
内模型满足 `ZFC_GCH kpair_convention_l`。无需外部选择公理，也无需外部良基性。
这里的 κ、κ⁺、幂集与双射均在 L 内解释；没有把外部 κ⁺ 当作内部后继基数。

| 接口 | 已证明的内容 |
| --- | --- |
| [Jensen/ZF/Choice](Jensen/ZF/Choice.lean) 的 `l_model_zfc_l` | 从逐层 Jensen 全局良序分离最小元，导出 L 内原选择集公理；背景只需 ZF |
| [Card/FiniteSequenceCountable](../Card/FiniteSequenceCountable.lean) 的 `ZF.fseq_bound_l` | ZF 中 κ 小字母表的全部内部有限序列仍为 κ 小；固定递归编号覆盖非标准长度 |
| [Internal/ElementaryHull](../../Model/SetTheory/Internal/ElementaryHull.lean) 的 `selem_hull_bound_l` | ZFC 中实际构造包含任意 κ 小种子的 κ 小内部初等子模型，量化全部内部公式码 |
| [Collapse/Sigma1Bound](../Collapse/Sigma1Bound.lean) 的 `s1_value_bound_l` | ZFC 中传递 κ 小参数的唯一 Σ₁ 输出仍为 κ 小；完整 Skolem 壳和 Mostowski 图均自动构造 |
| [GCH/Bounds](GCH/Bounds.lean) 的 `jh_cardinal_bound_l` | 当 κ 无限且 \|α\|≤κ 时，\|Jα\|≤κ；直接实例化真实的 Σ₁ 层递归图 |
| `jh_subset_bound_l` | 构造性的 κ 子集经小壳凝聚，被固定在高度 β<κ⁺ 的 Jβ 中，因而属于 Jκ⁺ |
| [GeneralizedContinuum](../GeneralizedContinuum.lean) 的 `gch_sentence_l`、`gch_sat_l` | 原 Project 句子及其语义：每个无限 κ 的幂集与 Hartogs(κ) 存在内部双射 |
| `ZF.hartogs_power_eq_l` | 仅用 ZF，将幂集的 Hartogs 上界提升为等势；Cantor 排除较小序型 |
| [GCH/Model](GCH/Model.lean) 的 `js_gch_l`、`js_gch_sentence_l`、`l_model_gch_l` | ZF+V=L 的 GCH、原句子满足性及任意 ZF 背景中的实际 L 模型实例 |
| `ZF.gch_power_l` | 给定已证 GCH 实例与无限 κ，自动取得内部幂集、κ⁺ 和完整双射图 |

证明先在 ZF+V=L 中导出选择，再于该模型内运行一般小壳构造。
凝聚给出 `P(κ)⊆Jκ⁺`，唯一 Σ₁ 层值的计数给出 `|Jκ⁺|≤κ⁺`，二者合并为
`|P(κ)|≤κ⁺`；实际序型构造及 Cantor 定理最终得到 `2^κ=κ⁺`。
原可数积、并、有限序列和 Skolem 壳的入口均已改用同一套一般无限基数证明。

## 内部 OD

入口为 [OD](OD.lean)。`Od_d x` 是固定 Kuratowski 编码下的无参数原公式谓词，
不量化宿主 AST。定义见证包含内部累积层 `Vθ`、内部公式自然数码和内部有限序数
参数列码；空集补齐列外赋值，零号变量读取候选对象，要求该候选在层内唯一满足公式。

| 接口 | 结论与前提 |
| --- | --- |
| [Syntax](OD/Syntax.lean) 的 `od_code_unique_l` | ZF 中相同定义码的输出唯一；层、公式、参数列的辅助表示均不影响结果 |
| [Source](OD/Source.lean) 的 `od_source_l` | 从原公式及其序数参数的唯一性，经实际有限反射与统一编译生成内部定义码 |
| `od_code_external_l`、`od_in_iff_external_l` | 内部 OD 恰为原公式序数参数唯一可定义的对象，即使公式码或参数长度非标准也成立 |
| `od_convention_l` | 更换实际有序对编码约定不改变 OD 类 |
| [Code](OD/Code.lean) 的 `od_eval_unique_l`、`od_one_parameter_l` | 单序数代码求值单值；每个 OD 对象由同一条固定原公式和一个序数参数唯一指定 |
| [Definition](OD/Definition.lean) 的 `od_sat_l`、`od_iff_external_l` | 公开谓词的原公式解释及 ZF 中的通常 OD 语义 |
| `od_ordinal_l`、`od_parameter_free_l`、`od_separation_l` | 全部序数与无参数唯一可定义对象属于 OD；任意集合与 OD 的交实际存在 |
| `od_rel_sat_l` | 同一原公式在内部传递集合结构中的相对化解释；该结构的 OD 按自身满足关系计算 |
| [Complexity](OD/Complexity.lean) 的 `od_sigma_complexity_l`、`od_sigma_sat_l` | 实际 `∃∃∃∃∃∀Δ₀` 公式及其与既有 OD 谓词的等价证明 |
| [Minimum](OD/Minimum.lean) 的 `od_min_exists_l`、`od_min_unique_l`、`od_min_injective_l` | 每个 OD 对象的最小序数代码存在、唯一，不同对象的最小代码不同 |
| [Order](OD/Order.lean) | 最小码诱导严格线序；每个非空 OD 元素集合有最小元，每个严格初段为实际集合 |
| [Choice](OD/Choice.lean) 的 `od_unique_parameter_l`、`od_choices_exists_l` | 从 OD 参数唯一可定义的对象仍为 OD，规范选择集可直接由分离构造 |

数学存在性与等价定理仅用背景 ZF，不要求背景选择公理、外部良基性或 ω 标准性。
语法解释和相对化使用较弱的语义条件。反向对应通过标准解码公式读取内部代码，
不把非标准程序转换为宿主 AST。相对化结论不声称内部 OD 与背景 OD 的限制相同。
Σ₂ 证书先将固定解码公式限制在一个真实 V 层：层内唯一性是 Δ₀ 性质；
正向由有限反射取得该层，反向用层高度与解码序数唯一指定对象。
[CumulativeCertificate](../CumulativeCertificate.lean) 对层历史给出全称 Δ₀ 检查，
并在 KP 下证明证书与原递归值等价。证明没有假定所有非标准公式一起反射。

## HOD 与选择公理

[HOD/Definition](HOD/Definition.lean) 用全部成员属于 OD 的内部传递容器定义 `Hod_d`，
`hod_tc_l` 证明它恰为 `TC({x})⊆OD`；该类传递并包含全部内部序数。
`hod_sigma_complexity_l` 与 `hod_sigma_sat_l` 给出实际 Σ₂ 公式及语义等价。

[HOD/Choice](HOD/Choice.lean) 的 `hod_choice_set_l` 对 HOD 中任意互不相交非空族，
构造属于 HOD 的选择集。每行选择最早出现的序数定义码，所得集合从原族唯一可定义，
故仍是 OD；其元素又属于原族的遗传 OD 容器，因此整个集合属于 HOD。
`hod_model_choice_l` 将此结果落实为实际 `hod_model_l` 满足原 `Axioms.choice`。
背景仅假设 ZF，未假设背景 AC，也没有从存在命题选择外部数据。

OD 良序在背景模型中计算，不宣称同一公式在 HOD 内重算得到原关系。
原无参数 `hod_model_l` 目前有选择公理接口；实际完整 ZFC 模型入口为下节的
`hb_model_zfc_l`。`hb_ordinal_parameter_l` 已证明序数参数 A 下 HOD[A]=HOD，
但尚未把完整模型性迁移到 `hod_model_l`。成员 Σ₂ 证书与原解码／良序图的复杂度是不同接口。

## 两种参数版本及实际模型

参数约定采用 [Jech §13，195–196 页](https://daiwz.net/course/disc_math/2023/set_theory_jech.pdf#page=195)：
`OD[A]` 允许整个 A 作固定参数；`OD(A)` 在此之外允许 A 中的有限参数列。
相应的遗传类分别为 HOD[A] 和 HOD(A)。本库中的 A 总是背景模型内部的集合。

| 原公式与语义接口 | 已证明的内容 |
| --- | --- |
| [OD/Brackets](OD/Brackets.lean) 的 `Ob_d`、`ob_m`、`ob_iff_external_l` | OD[A] 的内部谓词，等价于标准原公式从 A 和序数参数唯一可定义；允许背景非标准 |
| `ob_code_l`、`ob_eval_unique_l` | A 固定后的单序数定义码及单值求值 |
| [OD/Relative](OD/Relative.lean) 的 `Op_d`、`op_statement_l` | OD(A) 精确等于某条内部有限 A 序列 s 下的 OD[A,s]；二参数以 Kuratowski 对表示 |
| [OD/RelativeClosure](OD/RelativeClosure.lean) 的 `oa_unique_l`、`op_member_l` | 两种参数类均对有限唯一原公式定义封闭，A 的每个成员属于 OD(A) |
| [HOD/Parameters](HOD/Parameters.lean) 的 `hb_statement_l`、`hp_statement_l` | 遗传类恰由 TC({x}) 的全部元素属于相应 OD 类刻画 |
| `hb_subset_hp_l`、`hp_transitive_parameter_l` | HOD[A]⊆HOD(A)；传递 A 连同其成员属于 HOD(A) |
| [HOD/Models](HOD/Models.lean) 的 `ha_model_zf_l`、`hp_model_zf_l` | 两个实际隶属结构的全部原 ZF 公理，包括任意模式的全分离和全收集 |
| [HOD/BracketChoice](HOD/BracketChoice.lean) 的 `hb_model_zfc_l` | 仅用背景 ZF，HOD[A] 满足原 ZFC；选择集自身属于 HOD[A] |
| [OD/Parameters](OD/Parameters.lean) 的 `ob_ordinal_parameter_l`、[HOD/Relative](HOD/Relative.lean) 的 `hb_ordinal_parameter_l` | A 为内部序数时，OD[A]=OD、HOD[A]=HOD |
| [OD/Relations](OD/Relations.lean) 的 `ob_product_l`、`ob_relation_l` | OD[A] 对笛卡尔积及任意原公式定义的关系集合化封闭 |

固定参数通过 OD 偏函数图在 A 处的值解释。[OD/Graph](OD/Graph.lean) 将任意原公式的
唯一值部分限制到真实 V 层，实际构造这样的 OD 图；反向由既有单序数解码恢复标准公式。
因此参数版本继续使用原内部满足关系与规范编码，没有新增解释语言或可定义性公理。

圆括号的有限性始终是模型内部有限性。[FiniteSequenceJoin](../Card/FiniteSequenceJoin.lean)
用内部序数加法拼接参数列，并给出可定义的前段与尾段投影，从而合并任意有限多个参数包。
`op_statement_l` 不声称非标准有限 A 序列可以展开为宿主标准有限个 A 元素。

共同的模型证明先构造 `H∩Vα`，并证明它仍属于相应遗传类。全收集在背景取得见证界后，
直接使用这样的秩切片；没有为每个对象挑选一个参数列。只有方括号的选择证明对固定 A
后的序数定义码取最小值。圆括号模型定理不附加 AC，也不宣称它总是不满足 AC。

## 序数关系呈现与力迫比较

[HOD/Coding](HOD/Coding.lean) 的 `ob_code_bound_l` 在 ZF 内收集一个集合的全部
OD[A] 对象所需的定义码界；`ob_code_graph_l` 在该界内保留所有有效代码，构造实际解码满射。
[HOD/Presentation](HOD/Presentation.lean) 的 `hb_presentation_l` 对 `TC({x})` 应用此构造，
把隶属关系回拉到代码载体，证明载体、关系均为 OD[A]，解码图恰为其总坍塌图。
重复代码允许坍塌到同一个值，故背景无需 AC。

[通用关系坍塌](../Collapse/RelationExistence.lean) 的 `wc_collapse_l` 对任意内部集合良基
关系构造总图和传递值域；唯一性通过原公式的内部关系归纳证明。这里不要求模型外部良基，
也不把非外延关系的坍塌误称为单射。

[弱齐性 HOD 比较](../../Model/Forcing/Internal/Homogeneous/HOD.lean) 先恢复这些代码，
再利用地模型的实际坍塌和扩张内部的唯一性，取得以下实际接口。e 是定理自动构造的
成员满单射；两个模型的序数相同也由定理返回，不是调用者另给的假设。

| 接口 | 精确前提与结论 |
| --- | --- |
| `whom_hod_comparison_l` | M 满足 ZF，U 为泛型，呈现 B、R、z 弱齐性且各自属于 OD；`HOD^{M[U]} ⊆ e[HOD^M]` |
| `whom_hb_comparison_l` | 同上，将呈现的 OD 前提放宽为 OD[A]；`HOD^{M[U]}[e(A)] ⊆ e[HOD^M[A]]` |
| [Cohen/HOD](../../Model/Forcing/Applications/Cohen/HOD.lean) 的 `cohen_hod_comparison_l` | 实际 Cohen 呈现、序数添加量及泛型自动给出无参数比较，不另要求 OD 或自同构证书 |

不增加序数本身只需 ZF 与泛型。比较不要求偏序有最大条件，也不要求背景 AC。
包含方向由扩张指向地模型；不据此断言两边相等、恢复所有 OD 对象，或给出 HOD(A) 的比较。

## 尚未完成

下列是现有接口之外的研究任务，不作为已完成定理的隐含前提。

| 待建部分 | 当前已具备的基础与尚缺的结论 |
| --- | --- |
| L[A] 的相对 J 构造 | 普通 J 层级及 rud 有限基已经完成；含谓词 A 的闭包、层递归及相应模型定理尚未实现，OD[A] 不代替 L[A] |
| 一般可容许递归接口 | 已处理实际 `S1_binary` 正规形及互补 Δ₁ 关系；一般 Lévy Σ₁ 语法的归一化、内部非标准 DSL 程序码的统一解释器尚未实现 |
| 降低归纳强度 | J 总搜索、层递归和全局良序使用 KPi；将相关端点降至原 KP＋V=L 仍需证明，不能只改参数类型 |
| 传统层级与有限基比较 | 尚未证明所选 rud 有限基与一般 rudimentary 项定义、其他 J 索引、独立 Def 递归的 Gödel L 层级之间的等价 |
| OD 图的复杂度强化 | OD/HOD 成员的 Σ₂ 证书已完成；原解码图、最小代表图和良序图的 Δ₂ 证书尚未认证，背景 OD 序在 HOD 内重算的绝对性也未证明 |
| 无参数 HOD 模型接口归并 | `hb_ordinal_parameter_l` 已识别序数参数下 HOD[A]=HOD；仍需把已证的完整参数模型性接到原 `hod_model_l` |
| 更广的力迫比较 | 已完成 HOD 与固定参数 HOD[A] 的弱齐性比较及 Cohen 实例；HOD(A) 比较和迭代后的比较端点尚未提供 |

## 数学定义来源

Jensen 的 [第一章 §1.1](https://www.math.uni-bonn.de/~raesch/jensen/jensen/pdf/Jensen_Manuscript_Chapter_1_Transfinite_Recursion_Theory%29.pdf)
给出可容许性、Σ₁／Δ₁ 递归及公式归纳的约定；[第二章定理 2.2.15、引理 2.3.2](https://www.math.uni-bonn.de/~raesch/jensen/jensen/pdf/Jensen_Manuscript_Chapter_2_Basic_Fine_Structure_Theory.pdf)
给出采用的有限基和一步辅助运算。本层固定 Kuratowski 对及右嵌套三元组，
采用宏观索引 `J₀=∅`、`Jₐ₊₁=Rud(Jₐ∪{Jₐ})`、`Jλ=⋃ₐ∈λ Jₐ`。
递归算子统一写作所有前值的后继之并，再证明上述三条方程。尚未在 Lean 中
证明有限基与一般 rudimentary 项定义的等价定理，或与其他 J 索引约定的等价性。
Σ₁ 凝聚的数学目标见 Jensen 原论文
[The Fine Structure of the Constructible Hierarchy，Lemma 2.6](https://www.math.cmu.edu/~laiken/papers/FineStructure.pdf#page=18)。
