# 力迫偏序、布尔完备化与名称解释

[功能目录与构造历史索引](INDEX.md)

导入 `YesMetaZFC.Model.Forcing`，声明位于 `YesMetaZFC.Model.Forcing`。
`YesMetaZFC.Model` 已导出此层。任意宿主预序已有实际正则开完备布尔代数和规范
稠密映射。名称求值直接消费现有 `Model.Boolean.BV_graph`，输出实际 `SG_set`。
已有相对名称域的解释扩张、完整一阶真值对应及 Cohen 新实数实例。一次调用
可得到对全部原公式、任意有限参数同时有效的滤子。全部地模型内部名称的扩张另有
完整内部力迫真值定理及原 ZFC 全部公理保持，包括全分离、全收集模式。
`Internal.preserves_zfc_l` 一次返回模型性；内部名称、规范名称递归、原子力迫、
公式翻译和各公理见证均由实际内部集合构造。主扩张载体是内部名称的泛型商，
允许任意外部非良基地模型，载体 universe 与地模型相同。
可数闭塌缩已接入这一名称域；`Internal.ch_model_l` 给出实际 ZFC＋CH 模型存在，
`Internal.ch_extension_l` 从任意可数地模型自动构造相应泛型扩张。
`Internal.cohen_extension_l` 将 Cohen 添加量参数化为模型内指标集 κ，自动产生互异新实数族
并保持旧无限基数；`not_ch_extension_l` 默认添加 ω₂ 条实数。`ch_independent_l` 与
`ch_consistency_l` 已把两侧模型接入原推导核，给出 CH 双侧不可证及两侧扩充的一致性。

## 文献选择

检索与版本核对日期：2026-09-29。下表区分论文发表、预印本修订及工程判断，
不把网页抓取时间或旧论文的新版排版当成新的数学构造。

| 文献 | 已核对的结果 | 对当前层的作用 |
| --- | --- | --- |
| Holliday，[Possibility Frames and Forcing for Modal Logic](https://arxiv.org/abs/2501.11768v2)，2025 年发表，2026-07-23 修订 | 第 2 节以偏序上的正则开集解释部分信息；Remark 2.15、Fact 2.17 联系向下集、双重否定与正则化。 | 采用条件预序及谓词运算作为入口。模态关系属于额外结构，不加入普通力迫条件。 |
| Pierobon–Viale，[Boolean valued models, presheaves, and étalé spaces](https://arxiv.org/abs/2006.14852v6)，2020 年初稿，2026-07-23 修订 | Definitions 1.4–1.7 区分保序、不相容保持、稠密性及布尔完备化；第 4–5 节区分 fullness、mixing 和层条件。 | 映射能力分层；分离商映射允许非单射。后续语义定理按实际所需的 fullness 或 mixing 陈述。 |
| Fritz–Roberts，[Forcing for Second-Order Logic](https://doi.org/10.1007/s10992-026-09843-9)，2026-04-21 发表 | 用 possibility semantics 发展二阶逻辑的力迫，研究二阶 GCH 的不可推导性。 | 是未来二阶语义的参考；该文的结论范围不替代原 ZFC 名称模型。 |
| Lau，[Forcing with Language Fragments…](https://arxiv.org/abs/2402.01213v6)，2024-12-25 修订 | 由语言片段合并生成理论与规范项模型；第二节保留预序和弱嵌入，对扩展 Namba 问题及解释受限理论给出应用。 | 语言片段可作为今后的具体条件类型；通用偏序不附加可数性、语法或项模型参数。 |
| Gunther 等，[The formal verification of the ctm approach to forcing](https://arxiv.org/abs/2210.15609)，2023 年修订，2024 年期刊版 | 在 Isabelle/ZF 中核验泛型扩张与 CH 两侧，并分析所需替换实例。 | 地模型公理按消费者分开；当前序论层不要求给定传递模型。 |
| Bezhanishvili–Holliday，[Choice-free Stone duality](https://arxiv.org/abs/2112.06859)，2020 年期刊论文，2021 年存档 | 以真滤子及适当的正则开集表示布尔代数，避免经典 Stone 空间表示所需的素理想选择原则。 | 支持优先使用显式谓词构造；本层不以超滤子选择构造数据。 |

本项目的选择是保留布尔值内核，以预序及稠密映射接入；这是根据现有实现作出的
工程判断。正则开集方法本身是经典方法，近年的工作主要改进其语义组织与适用范围。
不在基本偏序层引入完整拓扑斯或语言片段语义。

## 数学接口

`R.le p q` 表示 `p` 比 `q` 强。`PO_pre` 只携带自反、传递的关系，`PO_ord`
另加反对称性；非空性、最大条件、分离性、无原子性不是预序的必填字段。

| 模块 | 接口与已经证明的内容 |
| --- | --- |
| [Order/Basic](Order/Basic.lean) | `Cmp_l` 是存在共同加强，`Inc_l` 是不相容；`Lower_l`、`down_l`、反链、无原子性、分离性及条件以下的限制。 |
| [Order/Density](Order/Density.lean) | 稠密、局部稠密及预稠密；预稠密等价于向下闭包稠密；两个稠密集在其中一个向下封闭时交仍稠密。 |
| [Order/Density](Order/Density.lean) 的映射 | `PO_hom` 只保序，`PO_compat` 另保持不相容，`PO_dense` 再要求像稠密；证明稠密开集回拉及稠密映射复合。相容性反射只要求 `PO_compat`。 |
| [Order/Separative](Order/Separative.lean) | 通过相容性定义分离预序与实际商 `Sep_l`，构造 `sep_order_l` 和规范稠密映射 `sep_map_l`；证明商序分离、规范映射保持并反射相容性。 |
| [Boolean/Conditions](Boolean/Conditions.lean) | 任意 `BA_alg B` 的非零部分给出 `positive_order_l`；相容等价于交非零，差 `p ∧ ¬q` 给出分离见证。条件域非空恰要求代数非平凡。 |
| [Order/Tree](Order/Tree.lean) | `List A` 按延长排序；相容恰为前缀可比，任意有限长度的条件稠密；二元树的两个孩子形成反链，整棵树无原子。 |
| [Boolean/RegularOpen](Boolean/RegularOpen.lean) | `RO_l` 是向下且双重伪补稳定的谓词；`ro_algebra_l` 实际装配交、剩余、双重否定及任意上确界，直接返回原 `CB_alg`。 |
| [Boolean/Completion](Boolean/Completion.lean) | `ro_principal_l p` 正则化主向下集；`ro_map_l` 保序且保持不相容，`ro_dense_l` 的像稠密。布尔比较恢复 `Sep_le_l`，非零交恢复 `Cmp_l`；分离时反射原顺序，反对称时进一步单射。 |
| [Applications/Cohen/Algebra](Applications/Cohen/Algebra.lean) | `cohen_algebra_l` 是二元序列树的实际完备布尔代数；`cohen_nontrivial_l` 和 `cohen_atomless_l` 分别给出非平凡性与无原子性。 |
| [External/Generic](External/Generic.lean) | 条件滤子、主滤子、递降序列滤子；`generic_countable_l` 从任意起始条件构造遇到指定可数稠密族的滤子。 |
| [Boolean/Generic](Boolean/Generic.lean) | 条件滤子转布尔真滤子；显式上确界见证稠密集 `sup_dense_l` 及其稠密性；只有遇到相应稠密集才导出无限析取／合取的真值对应。 |
| [External/Valuation](External/Valuation.lean) | `val_graph_l` 删除未接受的边，`val_l` 取双模拟商；成员递归式、规范名称 `check_graph_l` 及还原定理。数据无需滤子、完备性或代表元选择。 |
| [External/Truth](External/Truth.lean) | `Name_generic_l` 列出四类具体稠密集；`val_eq_iff_l`、`val_mem_iff_l` 沿图良基归纳证明原子真值对应。可数节点已有泛型滤子存在端点。 |
| [External/NameGeneric](External/NameGeneric.lean) | `name_family_generic_l` 同时处理可数名称族所有节点对，并允许额外可数稠密要求；有限初段调度直接产生同一个滤子。 |
| [External/Extension](External/Extension.lean) | `name_span_l` 生成子名称封闭域；`ext_structure_l` 是该域的实际求值像，已有传递性、外延性、良基性、规范名称包含及原子语义接口。 |
| [External/RealName](External/RealName.lean) | 任意权重序列给出可数的自然数子集名称；求值逐位读取权重。复用原 ω 图，并提供显式节点枚举。 |
| [Applications/Cohen/Real](Applications/Cohen/Real.lean) | `cohen_extension_l` 构造同一滤子：遇到给定稠密族、避开给定可数旧实数族，并满足整个 `cohen_names_l` 名称域的原子真值要求。 |
| [External/Domain](External/Domain.lean) | 相对名称布尔结构 `domain_str_l` 与原纯语言扩张 `ext_model_l`；求值映射直接满射到解释像，项和环境使用原 `Fn_map` 接口。 |
| [External/Formula](External/Formula.lean) | `val_formula_iff_l` 对原十一种公式构造证明真值对应；量词只遍历指定名称域，保留原 bound/free 上下文。 |
| [External/FormulaGeneric](External/FormulaGeneric.lean) | `fm_dense_l` 由公式及赋值计算量词稠密族，并证明稠密性和向下封闭性；没有让调用者假设量词真值引理。 |
| [External/FormulaEnumeration](External/FormulaEnumeration.lean) | 复用 `SyntaxNatCoding` 的单射编码及原异质赋值列，证明全部有限参数公式实例可枚举；枚举选择只存在于 Prop 证明中。 |
| [External/ZFCBase](External/ZFCBase.lean) | 直接核验原外延性、空集、基础公理；当 ω 在实际解释像中时，核验原无穷公理。 |
| [Applications/Cohen/Theory](Applications/Cohen/Theory.lean) | `cohen_full_extension_l` 一次生成满足全部公式真值、额外稠密族和新实数要求的同一滤子；`cohen_zfc_base_l` 自动给出四条原公理。 |
| [SetTheory/Kuratowski](../../SetTheory/Kuratowski.lean) | 名称与内模型共同使用的 Kuratowski 编码及原 `OrderedPairConvention` 实例；坐标单射、编码唯一性和三步成员下降。 |
| [Internal/Names/Basic](Internal/Names/Basic.lean) | `Internal.Name_d` 的全部量词遍历模型对象；`name_m` 是同一条件的原 Project 公式，已证明语义对应与子名称、标签闭包。 |
| [Internal/Names/Closure](Internal/Names/Closure.lean) | 用模型内部两条明确的分离／收集模式构造支撑，证明 `name_unfold_l`；内部子集和带权二元名称只要求配对与并集。 |
| [Internal/Names/Graph](Internal/Names/Graph.lean) | 从内部支撑和条件集的小呈现解码；`Rep_d` 精确保留并覆盖带权成员，`rep_val_eq_l` 与 `val_exists_unique_l` 保证求值与呈现选择无关。 |
| [Internal/Names/Realization](Internal/Names/Realization.lean) | 原布尔名称实际编码为小图模型中的集合、条件集及支撑；`encode_pred_val_l` 给出求值往返，`sg_check_exists_l` 给出该模型内的规范名称。 |
| [Boolean/Internal](Boolean/Internal.lean) | 以集合编码载体和序关系，实现原 `BooleanZF.Boolean_d`；模型内集合族的上确界直接构造。关系编码无需序公理，上确界只消费 `Sup_order`。 |
| [Applications/Cohen/Internal](Applications/Cohen/Internal.lean) | Cohen 正则开条件有单射的集合编码；`cohen_boolean_l` 是实际内部布尔代数实例，`cohen_internal_name_l` 是实际模型对象。 |
| [Internal/Atomic/Syntax](Internal/Atomic/Syntax.lean)／[Internal/Atomic/Closure](Internal/Atomic/Closure.lean)／[Internal/Atomic/Recursion](Internal/Atomic/Recursion.lean) | 内部带条件双模拟及其最大关系；证明支撑无关性、等号递归方程及隶属力迫的一阶可定义性。 |
| [Internal/Forcing/Conditions](Internal/Forcing/Conditions.lean)／[Internal/Forcing/Definability](Internal/Forcing/Definability.lean)／[Internal/Atomic/Witness](Internal/Atomic/Witness.lean) | 条件预序、模型内稠密集泛型性、实际见证和反例稠密集。 |
| [Internal/Atomic/Equivalence](Internal/Atomic/Equivalence.lean)／[Internal/Extension/Quotient](Internal/Extension/Quotient.lean) | 模型内部双模拟的等价及替换；同 universe 的名称泛型商、原子真值、求值成员方程及外延性。 |
| [Internal/Extension/Foundation](Internal/Extension/Foundation.lean)／[Internal/Check/Forcing](Internal/Check/Forcing.lean) | 由内部公式归纳证明条目极小元、商模型的基础公理及规范名称嵌入单射性；允许外部非良基地模型。 |
| [Internal/Atomic/Truth](Internal/Atomic/Truth.lean) | 外部良基名称图的原子真值及求值对应；图表示层的独立接口。 |
| [Internal/Forcing/Formula](Internal/Forcing/Formula.lean)／[Internal/Forcing/Logic](Internal/Forcing/Logic.lean)／[Internal/Forcing/Truth](Internal/Forcing/Truth.lean) | 原 Project 公式的内部力迫翻译、正则性和泛型商的完整真值定理；量词遍历全部内部名称。 |
| [Internal/Names/Construction](Internal/Names/Construction.lean)／[Internal/Extension/Separation](Internal/Extension/Separation.lean)／[Internal/Extension/Collection](Internal/Extension/Collection.lean)／[Internal/Extension/Power](Internal/Extension/Power.lean) | 有界加权名称构造、任意有限参数的全分离和收集、内部幂集名称。 |
| [Internal/Extension/Operations](Internal/Extension/Operations.lean)／[Internal/Extension/ZF](Internal/Extension/ZF.lean) | 配对、并集、无穷及其余原 ZF 公理装配；`preserves_zf_l` 自动构造名称域非空证书。 |
| `SetTheory.Choice`／[Internal/Maximum/Selection](Internal/Maximum/Selection.lean)／[Internal/Extension/Choice](Internal/Extension/Choice.lean) | 从原选择集公理构造内部序数枚举，证明最早隶属选择的稠密性与唯一性；`preserves_zfc_l` 给出完整 ZFC 保持。 |
| [Internal/Extension/Instance](Internal/Extension/Instance.lean) | 实际二元布尔条件及其主泛型滤子；`two_extension_zfc_l` 直接实例化完整保持定理。 |
| [Internal/Extension/Generic](Internal/Extension/Generic.lean) | 从地模型对象枚举构造遇到全部内部稠密集的滤子，并自动给出小呈现。 |
| [Closed/Basic](Closed/Basic.lean)／[Applications/Collapse/Basic](Applications/Collapse/Basic.lean) | 原模型内的可数递降链、可数稠密交、可数部分函数条件集及其实际可数闭性。 |
| [Closed/NoNewReals](Closed/NoNewReals.lean)／[Closed/NoNewFunctions](Closed/NoNewFunctions.lean)／[Closed/NoNewCountable](Closed/NoNewCountable.lean)／[Internal/Ground/Transfer](Internal/Ground/Transfer.lean) | 可数闭力迫不增加实数、取值于任意旧集合的内部 ω 函数或旧集合的内部可数子集；返回实际旧原像及旧可数性。规范嵌入保持成员、函数图、单射、序数和 ω。 |
| [Applications/Collapse/Generic](Applications/Collapse/Generic.lean)／[Applications/Continuum/CH](Applications/Continuum/CH.lean) | 构造实际泛型满射名称，核验原 ZFC＋CH 理论，装配可数地模型和实际模型存在入口。 |
| `SetTheory.Card.Finite`／`PartialFunction`／`PartialFunctionCCC` | 内部有限集合的删除归纳、有限部分函数添值与合并，以及任意坐标集和可数值集上的内部可数链条件。 |
| `SetTheory.Fiber`／`Card.CountableUnion` | 可定义纤维自动组成集合函数；小集合族的并单射到 κ×κ，供可数覆盖与基数保持共同使用。 |
| [CCC/Basic](CCC/Basic.lean)／[CCC/Bounds](CCC/Bounds.lean) | 有限部分函数偏序自动装配 CCC；可定义碰撞的否定条件控制可能原像，反射基数上界并保持每个旧无限基数。 |
| [Internal/Functions/Generic](Internal/Functions/Generic.lean)／[Applications/Cohen/Coordinates](Applications/Cohen/Coordinates.lean) | 塌缩与 Cohen 共用泛型函数名称；新鲜自然数列、两行分离及旧集合对角稠密集。 |
| [Applications/Cohen/Add](Applications/Cohen/Add.lean)／[Applications/Continuum/NotCH](Applications/Continuum/NotCH.lean)／[Applications/Continuum/Independence](Applications/Continuum/Independence.lean) | 按 κ 添加互异新实数、ZFC＋¬CH 模型及原 ZFC 的 CH 独立性；均允许外部非良基地模型。 |

分离比较定义为

\[
p\leq^*q\quad\Longleftrightarrow\quad
\forall r\;(r\mathrel{\parallel}p\Rightarrow r\mathrel{\parallel}q).
\]

`sep_le_iff_l` 给出它与“每个 `r ≤ p` 都与 `q` 相容”的等价。`Sep_l` 对双向
`≤*` 取商，商顺序直接用 `Quotient.lift₂` 定义。原条件域可以不反对称、不分离。

## 调用

先固定 `R : PO_pre P`，即可调用 `R.sep_order_l`、`R.sep_map_l` 及
`R.sep_separative_l`。实例不要求调用者先提供不存在的模型或布尔完备化：

- `tree_order_l Bool` 已给出无限二元条件树；`binary_atomless_l` 和
  `tree_length_dense_l false n` 是直接可用的数学证书。
- 对仓库已有的布尔代数，例如 `Boolean.prop_algebra.toBA_alg`，
  `positive_order_l` 直接构造其非零条件。普通布尔代数即可，无需 `CB_alg`。
- `PO_dense.dense_preimage_l e hD hO` 将目标中的稠密开集拉回源预序；
  `e` 可以直接取任意实际预序的 `sep_map_l` 或 `ro_dense_l`。
- `R.ro_algebra_l : Boolean.CB_alg R.RO_l` 只消费原预序。
  `R.ro_condition_l p` 直接给出非零布尔条件，
  `R.ro_principal_le_iff_l p U` 将其小于 `U` 化为 `U.mem p`。
- `cohen_algebra_l` 可直接传给已有 `Boolean.name_model` 和
  `Boolean.bv_models_zfc`；使用这些语义端点时另导入 `YesMetaZFC.Model.Boolean`。

## 正则开代数的构造

伪补与正则化直接定义为谓词运算：

\[
\neg_R D(p)\;\Longleftrightarrow\;\forall q\leq p\;\neg D(q),
\qquad j(D)=\neg_R\neg_R D.
\]

`RO_l` 携带向下封闭及 `j(U) ⊆ U` 的证明；反向包含由向下封闭自动得到。
交是谓词合取，剩余是 `∀ q ≤ p, U(q) → V(q)`，上确界是集合并的正则化。
幂等性、正则封闭性、剩余律与双重否定律均已证明，不把代数律当作额外参数。

`ro_reg_dense_iff_l` 在 Prop 内证明 `j(D)(p)` 等价于
`∀ q ≤ p, ∃ r ≤ q, D(r)`，接回已有 `Dense_below_l`。
正则化仅在输入向下封闭时保证扩张；任意谓词的正则开闭包应先取 `down_l`。
上确界的集合并及规范映射的主向下集都已经向下封闭。

规范映射不要求原预序分离：`ro_principal_order_l` 精确得到原分离预序。
仅 `ro_order_iff_l` 消费分离性；`PO_ord.ro_injective_l` 再消费反对称性。
`ro_nontrivial_l` 证明代数非平凡恰等价于原条件域非空，空预序仍有合法的平凡完备代数。

## 语义与可信边界

求值完全遵循

\[
\tau^U=\{\sigma^U\mid(\sigma,b)\in\tau,\ b\in U\}.
\]

`val_graph_l` 保留原节点，把成员关系限制为原成员边与标签被接受的合取，
良基性由原图继承。`val_mem_l` 证明上述递归式，`val_check_l` 证明规范名称还原。
输入与输出的节点层均为 `Type u`，布尔值可独立处于 `Type v`。

对布尔族 `f`，实际见证稠密集为

\[
D_f=\{p>0\mid p\leq\neg\bigvee_i f_i\ \lor\ \exists i\;p\leq f_i\}.
\]

其稠密性由 `p ∧ fᵢ` 的非零性分情况证明。原子真值的前提只列出名称成员和
等号展开中实际出现的这些集合；不假设滤子保持任意无限上确界，也不把真值
定理塞入结构字段。`name_family_generic_l` 通过四重有限初段与
Rasiowa–Sikorski 证明这些前提可同时实现；`cohen_node_enum_l` 给出实际实例的枚举。

完整真值通过原公式结构归纳证明：联结词消费超滤子的有限运算性质，全称和存在
分别消费反例与见证稠密集；目标量词见证由求值满射回拉。`fm_dense_l` 在二元
联结词处取稠密开集的交，在量词处用已有 `NatPairing` 遍历名称与正文要求。
全部公式及有限赋值的可数性复用现有 `SyntaxNatCoding` 和 `Model.FirstOrder.Valuation`。
这里使用语法编码的单射性，没有调用 Henkin 完备性或构造另一套公式语言。

常用调用顺序如下，其中 `r` 枚举旧实数的成员谓词，`D` 为额外稠密族，
`hD` 是其逐项稠密性证明，`p` 是任意非零 Cohen 条件：

```lean
obtain ⟨U, hU, hp, hd, hn, ht⟩ := cohen_full_extension_l r D hD p
let ℳ := ext_model_l (cohen_names_l r) U.mem
-- cohen_ext_old_l r U n：第 n 个旧实数属于 ℳ。
-- cohen_ext_new_l r U：Cohen 名称的实际求值属于 ℳ。
-- hn n：该求值不同于第 n 个旧实数。
-- ht φ ρ：原公式 φ 在赋值 ρ 下的布尔真值被 U 接受，当且仅当 ℳ 中相应公式成立。
have hbase := cohen_zfc_base_l r U
-- hbase 给出原外延性、空集、基础及无穷公理，不是全部 ZFC。
```

`cohen_names_l r` 由空名称、Cohen 名称、ω 的规范名称及旧实数规范名称生成，
**不是 ZFC 地模型的全部内部名称域**。此有限生成相对域只核验了四条基础公理；
完整公理保持使用下述地模型全部内部名称域。
完整真值对应的左侧是这个相对名称域的布尔解释，不能直接替换成全名称宇宙的
`Boolean.bv_models_zfc`。正式内部名称接口见下一节。`val_surjective_l` 已证明全部宿主名称的
求值像就是全部宿主 `SG_set`，因此不能用全宿主名称域替代地模型相对化。

## 内部名称

声明位于 `YesMetaZFC.Model.Forcing.Internal`。对于地模型隶属结构 `M`、
模型内条件集 `B` 和模型对象 `τ`，定义为

\[
\operatorname{Name}_M(B,\tau)\iff
\exists S\in M\;\bigl[\tau\in^M S\ \land\
\forall\sigma\in^M S\;\forall p\in^M\sigma\;
\exists\rho,b\in M\;(p=\langle\rho,b\rangle\land\rho\in^M S\land b\in^M B)\bigr].
\]

这里 `S` 是模型对象，不是宿主提供的名称谓词。`name_sat_l` 证明其与 `name_m`
完全对应。`name_unfold_l` 证明它等价于通常的递归定义：每个成员都是标签在 `B`
中的子名称对。反向证明先在模型内收集支撑，再用 `supp_m` 的分离实例去掉无效
支撑，最后取并并添加新根。`Name_ops_d` 只保留所用的配对、并集和两条明确模式；
`name_ops_l M hZF` 从已给定的 ZF 模型证明自动生成这些能力。

名称编码选用 Kuratowski 对，以得到 `ρ ∈ {ρ} ∈ ⟨ρ,b⟩ ∈ σ` 的实际下降路径。
这是本层明确指定的 `OrderedPairConvention`，不改变项目其余层的平坦对约定。
一阶名称定义本身不要求模型外部良基；解码到外部良基图时才消费 `WellFounded M.mem`。
不会从 `M ⊨ Foundation` 推出外部良基性。

`Setlike_d.{m,n} M` 要求模型内每个集合存在 `Type n` 中的小呈现。解码的节点是
支撑与条件呈现的乘积加一个根，始终留在 `Type n`，输出属于 `SG_set.{n}`。
`decode_exists_l` 不导出呈现选择函数；`val_exists_unique_l` 证明实际解释存在唯一，
`Internal.val_mem_l` 给出直接使用模型内带权成员的求值递归式。
`name_domain_l` 把这些呈现接入已有 `Name_domain_l`，无需另填子名称封闭性证书。

已有实际实例，不要求调用者虚设模型构造能力：

- `sg_setlike_l`、`sg_name_ops_l` 和 `sg_name_domain_l` 来自原小图模型的实际集合操作。
- `encode_name_l` 把任意已有布尔名称编码成真正的内部集合；无限节点域也由小图并合
  形成同层的内部支撑。`sg_check_exists_l` 通过下述通用内部递归给出每个旧集合的规范名称。
- `cohen_code_injective_l` 证明正则开条件的集合编码单射；`cohen_boolean_l` 核验编码
  载体和序关系的内部布尔代数律。`sup_exists_l` 构造模型内集合族的上确界，不要求
  使用者把内部代数声明成宿主完备代数。

```lean
have ht := Internal.cohen_internal_name_spec_l
obtain ⟨G, hG⟩ := Internal.sg_decode_l ht
-- G 使用原 Type 0 小节点；hG 证明它精确呈现模型内的 Cohen 名称。
have hv := Internal.cohen_internal_val_l U.mem
-- U 是原 Cohen 布尔滤子；其成员谓词沿单射编码自动送到模型对象。
```

上面的 `sg_*` 是实际完整小图地模型的实例，不声称它可数，也不声称由前面的
可数稠密族构造所得滤子对整个小图地模型泛型。下面的内部真值及保持定理要求
`Generic_d`：滤子遇到地模型中每个在其接受条件下稠密的集合。

## 内部规范名称递归

`Check_d M b x τ` 用模型内的部分递归图定义规范名称，其纸面方程为

\[
\check{x}_b=\{\langle\check{y}_b,b\rangle:y\in^M x\}.
\]

取 `b` 为布尔顶值即可得到通常的规范名称。构造本身不消费布尔代数律。
`check_sat_l` 核验实际公式 `check_m`；`check_mem_l` 给出上式，
`check_unique_l`、`check_injective_l` 和 `check_mem_iff_l` 分别证明唯一性、
单射性和隶属保持。递归图的值域直接构成内部名称支撑。

存在性先证明任意两个部分递归图相容，再在模型内收集前驱图、取并、替换出新值，
最后添加输入输出对。`Check_ops_d` 的收集与替换字段由明确的一阶公式实现，
`check_ops_l M hZF` 和 `sg_check_ops_l` 均是已构造的实际实例。

归纳使用 `SetTheory.Mem_ind_d`，它只对实际一阶公式成立。
`MembershipInduction` 复用内部序数递归，沿模型自己的 ω 形成传递包络，
再以分离和基础公理证明成员归纳。因此规范名称存在性不要求外部良基性，
也不要求模型内部的 ω 是标准自然数。

```lean
obtain ⟨τ, hτ, hname, hunique⟩ := Internal.zf_check_l M hZF hb x
-- hb : M.mem b B；hτ : Internal.Check_d M b x τ。
-- hname : Internal.Name_d M B τ；hunique 给出同一 x 的名称唯一性。
```

外部解释时，`Ground_rep_d` 独立呈现地模型的无权成员图。
`ground_decode_l` 从内部传递包络和小呈现构造该图，节点层级保持不变；
`ground_rep_eq_l` 保证呈现无关性。`check_val_l` 以规范名称关系作双模拟，
证明接受 `b` 的任何谓词都把规范名称还原为该地模型对象。

`zf_check_val_l M hZF hM hL hb x` 一次取得规范名称、地模型对象的小图解释，
以及对所有 `U b` 成立的求值还原。这里只在小图解释阶段要求 `hM` 外部良基、
`hL` 为相应节点层级的 set-like 证书，不从内部基础公理推断这些条件。

原 `sg_check_exists_l` 已迁移为同一内部递归的实例：参数为 `hb : b ∈ B` 和 `x`，
结果同时包含规范性、内部名称性、唯一性及对所有接受 `b` 的谓词的求值还原。
`sg_check_ext_l hb U hU x` 直接证明旧对象属于内部名称的解释扩张。
本层只返回存在与唯一性定理，没有定义全局不可计算的规范名称选择函数。

## 内部真值与完整 ZFC 保持

`Eq_force_d` 以模型内带条件双模拟为证书。在闭支撑 `S` 上，利用模型内
`B × S × S` 的幂集收集所有双模拟，再取并得到最大关系；限制到另一个闭支撑
保持该关系，因此力迫定义不依赖支撑。`Mem_force_d` 是匹配隶属见证的稠密闭包。
两个谓词都有实际 Project 公式。`InternalEquivalence` 在模型内三元组集合上构造
对角、逆关系和复合双模拟，证明等号力迫的等价性及隶属替换；不使用外部良基归纳。

`InternalQuotient` 定义 `Name_quot_l M B R z U`：内部名称按
`∃ p, U p ∧ Eq_force_d M B R z p s t` 取商。`Qval_d` 是名称到商类的解释关系，
`qmem_l` 是被接受的隶属力迫在商上的像；替换定理保证它与任意代表元一致。
`extension_l M hZF B R z U` 是这个商上的实际集合论结构。若地模型载体为 `Type u`，
扩张载体同样为 `Type u`。小图解码及 `InternalAtomicTruth` 保留为外部良基情形的
图表示设施，内部真值与公理保持直接在商上证明。

`force_code_m` 递归翻译原公式，否定为非零加强下不可实现，全称量词只遍历内部名称。
`forcing_truth_l` 证明
`(∃ p, U p ∧ Forces_d M B R z φ ρ p) ↔ Formula.satisfies η φ`，
适用于任意自由变量闭合的原 Project 公式及相应有限参数赋值；
`Env_val_d` 表示名称赋值 `ρ` 解释为扩张赋值 `η`，`lift_env_l` 给出任意 `η` 的提升。
`Cond_order_d` 只要求预序和零元以下无非零条件，布尔代数由 `cond_order_l` 自动接入。

分离在源名称支撑与条件集的积上按力迫正文分离；收集在模型内统一收集可能见证。
幂集先把每个扩张子集正规化成模型内 `S × B` 的子集名称，再用模型自己的幂集收集。
选择公理使用 `ZFC.ordinal_enum_l`：从原选择集公理和 Hartogs 定理取得支撑的内部
序数枚举，最早可能隶属的指标产生可定义稠密集，保证选值存在且与名称呈现无关。
基础公理使用 `entry_ind_l`，它把实际公式加强到两层成员，从原内部成员归纳得到
名称条目归纳。`entry_min_l` 在模型内集合中找到条目极小元；泛型性遇到极小可能
成员的稠密集，从而证明 `internal_foundation_l`。这不把内部基础公理当成外部良基性。

```lean
have hExt := Internal.preserves_zfc_l O hZFC hU
-- O : Internal.Cond_order_d M B R z
-- hU : Internal.Generic_d M B R z U
-- 结论是 extension_l M (ZFC.models_zf_l hZFC) B R z U 满足原 ZFC，包括全部模式。
have hConcrete := Internal.two_extension_zfc_l
-- 小图地模型与二元布尔主泛型的完整实际实例，无额外模型存在前提。
```

`preserves_zf_l O hZF hU` 只消费地模型 ZF；选择公理仅在 `preserves_zfc_l` 中使用。
这两个保持接口均不要求可数性、外部良基性或小图呈现。任意可数地模型的完整
泛型存在由 `internal_generic_l` 提供；对未给枚举的模型，保持定理消费给定的
`Generic_d` 证书。Cohen 相对名称域尚未接成完整内部 Cohen 扩张。

## ZFC＋CH 的实际力迫模型

`SetTheory.ZFC_CH 𝒞` 是原 ZFC 加上实际 Project 句子 `ch_sentence_l 𝒞`。
该句子取模型自己的 ω、其幂集及 Hartogs 序数 κ，要求 `|P(ω)| ≤ κ`；
`ch_sat_l` 核验语义。`ZFC.continuum_bound_l` 用 Cantor 定理证明：若一个序数的
所有真初段可数且足以覆盖实数，它就是所需的第一不可数基数。

构造的条件是 κ 到地模型实数集的可数部分函数，按反向包含增强。
`coll_set_l` 用内部幂集与分离得到条件集，`collapse_closed_l` 构造序关系并证明
模型内可数闭性。`SetTheory.ZFC.dependent_choice_l` 和 `countable_union_l`
分别提供真正内部的递降链及可数并；`ZF.omega_cardinal_l` 自动证明 ω 的基数性。

`no_new_reals_l` 对每个自然数同时判定规范名称隶属，再通过内部可数稠密交与泛型性
取得一个全判定条件。地模型按这个条件分离出旧实数，证明其规范名称与给定实数
解释相同。`collapse_surjection_l` 则把被泛型滤子接受的条件中的有序对收集成
实际关系名称：指定坐标稠密集保证全定义，指定值稠密集保证满射。
`check_force_reflect_l` 对原对象作内部公式归纳，证明规范名称在泛型商中的单射性。
`check_map_l` 因而给出任意地模型的成员满覆盖嵌入。`image_omega_l` 在扩张中对
旧 ω 与任意归纳集的差集取基础公理极小元，证明旧内部 ω 仍是扩张的 ω；
这里没有排除非标准自然数。`ch_forcing_l M hZFC` 对任意地模型给出实际塌缩偏序，
并证明其每个地模型泛型商满足 ZFC＋CH。
这条路线与 [Isabelle/ZF 的 CH 塌缩构造](https://isa-afp.org/browser_info/current/AFP/Independence_CH/CH.html)
使用的可数部分函数塌缩一致。

模型存在的地模型由 `SetTheory.countable_ground_l` 实际提供：对原小图 ZFC 模型
逐层加入原公式的有限参数见证，复用 `Substructure_m.tarski_vaught_m` 得到可数
初等子模型；其隶属关系继承小图模型的外部良基性。公式查询编码与原力迫调度
已统一迁到 `Model.SetTheory.CountableSyntax`，不重复建立语法。

```lean
obtain ⟨N, hN⟩ := Internal.ch_model_l
-- hN : N.Models (SetTheory.ZFC_CH Internal.kpair_convention_l)

obtain ⟨B, R, U, hO, hU, hCH⟩ := Internal.ch_extension_l M hZFC e he
-- e : Nat → M.Domain，he : Function.Surjective e；允许外部非良基与非标准 ω。
-- B、R 是模型内条件集与序关系，U 是实际地模型泛型滤子。
```

`Closed_d` 只对地模型内部的 ω 序列断言存在下界。地模型在外部可数，并不把其
所有外部可数序列变成模型内集合。模型、枚举、见证选择和泛型滤子只通过 Prop
存在定理返回，没有全局不可计算的模型实例。

## 任意添加量与 CH 独立性

`cohen_forcing_l M hZFC κ` 自动构造 `Add(ω,κ)`：条件是模型内 κ×ω 到二元集的
有限部分函数，增强方向为反向包含。κ 可为任意模型内指标集；取旧无限基数时，
它在扩张中仍是同一个基数。有限性由向某个内部 n∈ω 的集合编码单射见证，
允许内部有限集合在外部看来无限。

可数链条件通过对内部有限大小界归纳证明。固定一个非空条件，每个反链成员
必在它的某个坐标上取值，这些坐标和值形成可数覆盖；每个覆盖片删去共同条目，
大小界降低。可数链条件只断言模型内反链可数。一般 Cohen 偏序的该性质亦见
[AFP 的 Cohen／Δ-system 形式化](https://isa-afp.org/entries/Delta_System_Lemma.html)。

`Cohen_result_d` 是已经构造出的装配结果，包含原 ZFC 模型性、规范地模型嵌入、
内部 ω 保持、每个旧无限基数保持，以及扩张内到 P(ω) 的集合编码单射实数族。
族中每一行都与每个地模型旧集合不同。κ 计数的是添加的 Cohen 坐标，接口保证
至少 κ 个互异新实数；它不将连续统自动声明为恰好 κ，后者还需要基数算术上界
与名称计数证明。

精确值的一项标准充分条件是地模型内 κ 为无限基数且 `κ^ω = κ`，参见
[Kubiś 讲义 Lemma 14.2](https://users.math.cas.cz/~kubis/pdfs/forcing_notes1999.pdf)。
当前装配不要求该条件，也尚未实现对应的名称计数上界；已实现的参数化结论为上述
单射新实数族，足以自动装配 ¬CH 与 CH 独立性。

```lean
obtain ⟨ω, B, R, U, hω, O, hU, hccc, hAdd⟩ :=
  Internal.cohen_extension_l M hZFC κ c hc
-- κ : M.Domain；c : Nat → M.Domain，hc : Function.Surjective c。
-- hAdd : Internal.Cohen_result_d O hZFC hU ω κ。

obtain ⟨B, R, U, O, hU, hnCH⟩ := Internal.not_ch_extension_l M hZFC c hc
-- hnCH : (Internal.extension_l M ... B R B U).Models
--   (SetTheory.ZFC_not_CH Internal.kpair_convention_l)。

have hIndependent := Internal.ch_independent_l
have hConsistent := Internal.ch_consistency_l
```

`cohen_not_ch_l` 只要求添加量在地模型中不能单射到其 ω₁，不要求 GCH 或先调整
地模型的连续统。`not_ch_forcing_l` 自动取两次 Hartogs 得到 ω₂，并装配所有所需
证书。`ch_extensions_l M hZFC c hc` 从同一个可数地模型返回 CH 的两侧模型；
`not_ch_model_l` 使用已有实际地模型实例，无额外模型存在前提。

`ch_independent_l` 的结论是原 Project `Derives ZFC` 对 `ch_sentence_l` 与
`not_ch_sentence_l` 的双侧不可证。这里的 `Derives` 定义为原纯隶属一阶核的推导，
`Model.SetTheory.ProjectSoundness` 保留对象域与成员关系接入原可靠性定理。
`ch_consistency_l` 同时给出两个扩充理论的一致性。对任意大小的地模型，力迫保持
接口消费给定泛型；可数性只在自动构造泛型的 `*_extension_l` 入口使用。

## 支撑迭代

共同后继步见 [迭代设施清单](ITERATION.md)：`two_step_l` 从任意名称预序构造实际
内部二步条件集，`two_step_factors_l`、`two_step_compose_l` 与 `two_step_recover_l`
完成两阶段泛型的双向分解和精确恢复。内部混合与 `maximum_l` 给出全局见证名称，
`forces_zf_l` 与 `forces_zfc_l` 分别在相应地模型的全部正条件上核验原理论公理。
`forces_of_generics_l` 在 ZF 强度下消费实际原模型公式和对全部泛型成立的构造，
已用于规范名称配对及二步名称性。`cohen_step_l` 从任意
添加量名称统一装配 Cohen 后继、顶名称和实际阶段完全嵌入，对全部泛型保留 CCC、
基数保持与新实数族。`reg_embed_max_l`、`reg_embed_comp_l` 给出极大反链保持与
模型内嵌入复合。有限支撑、可数支撑的极限构造及给定原公式规则的完整内部
超限递归存在性均已完成；有限支撑 CCC 保持也已接入整个递归，可数支撑
properness 保持也已通过实际交集 club 完成。本层继续保留
任意外部非良基地模型的适用范围。

`stage_nmap_l` 从实际阶段图自动构造唯一的目标名称。`stage_nmap_comp_l` 核验两次
搬运与复合图的一致，`stage_nmap_id_l` 证明删除零标签后的恒等搬运仍与原名称
被迫相等。等号、隶属及其否定现已在阶段像上精确对应；`reg_generic_l` 自动回拉
目标泛型，`stage_extension_l` 给出解释交换且成员满覆盖的实际单射。
`two_step_name_l` 已构造二步名称的唯一转换，并验证其在第一扩张中的第二阶段
名称性及精确条目解释；`two_step_valuation_l` 进一步装配原二步名称的双重求值，
核验总性、唯一性和组合滤子下的成员递归。`curry_forces_eq_l` 以内部条目归纳
证明二步等号向嵌套等号传输，`curry_forces_eq_iff_l` 通过原模型内的实际双模拟
补齐反射方向。任意第二阶段名称现可在原模型内摊平，且双重值精确还原。
`two_step_iso_l` 自动返回单次二步扩张与双重扩张间的成员结构双射，并保留逐名称
求值证书；原部分映射接口已迁移到此入口。
`row_zero_l`、`row_successor_l` 已构造共同的部分函数坐标条件；省略顶名称坐标后，
旧条件按原对象完全嵌入下一阶段，顶不变且前缀精确恢复。有限／可数支撑均在
限制、单坐标追加和前缀替换下保持。后继同时返回 `Row_link_d`：限制投影保序，
旧前缀的加强能保留原尾部，产生同时低于原条件和新前缀的条件；阶段链接已有
恒等和复合定理。`row_cohen_successor_l` 给出添加量名称参数化的真实实例。
`Row_system_d` 进一步以实际模型内序列编码全部阶段；`row_system_successor_l` 和
`row_system_cohen_l` 自动延长所有旧投影。`row_limit_l` 从阶段序列实际构造有限／
可数支撑极限及各阶段的完全嵌入，`row_system_limit_l` 把极限写回序列以继续后继。
零系统直接调用统一极限处理空序列。`row_iteration_l` 进一步从实际原公式规则
构造任意指定内部长度的完整迭代；`row_iteration_unique_l`、`row_iteration_step_l`
给出字面唯一性与精确前缀方程，`cohen_iteration_l` 提供一键实际实例。
规则允许读取全部历史，递归轨迹的合法性由实际原公式作内部超限归纳证明。
构造与有限支撑直接并刻画只用 ZF。`row_limit_union_l` 精确刻画非空阶段系统中
条件与序关系的直接并。`two_step_ccc_l` 证明任意被迫 CCC 名称的二步保持；
`row_limit_ccc_l` 以内部有限尾支撑归纳证明非零极限保持，两者使用 ZFC。
`row_iteration_ccc_exists_l` 一次返回整个有限支撑迭代及全部阶段 CCC，
`cohen_iteration_ccc_l` 只需内部长度与添加量，自动验证现有 Cohen 原公式规则。
`ccc_proper_l` 已从内部可数闭包实际构造主条件 club；`proper_mstr_l` 自动装配
含指定可数种子的主加强，`cohen_names_proper_l` 给出任意添加量名称的全局 properness
力迫证书。`row_fusion_l` 取实际可数共尾前缀族的并，得到唯一极限条件并精确保留
全部前缀；`row_fusion_reconstruct_l` 自动生成实例并还原原条件。
`ng_elementary_hull_l` 已自动构造同一个 N 在所有接受主条件的泛型中的完整内部
`N[G]≺X[G]`。`ng_hchi_hull_l` 已将环境精确识别为扩张的 `H(eχ)`；
`ng_next_master_l` 从被迫 proper 的后继自动构造 club 名称及同一 N[G] 中的主加强。
`two_step_master_l` 已完成二步主条件合成，`two_step_master_first_l` 给出首坐标投影；
`two_step_master_second_l` 证明第二坐标的 N[G] 主性力迫，`two_step_master_decompose_l`
自动构造规范 N[G] 名称并给出完整双向分解。
`two_step_master_extension_l` 在任意地模型中自动取得含指定种子的实际二步主加强。
`ng_family_hull_l` 一次选择同一个 N，统一支持其所有成员阶段的 H(χ) 泛型初等提升。
`ng_family_forcing_l` 已把共同提升构造成内部原公式的力迫证书；
`ng_family_ground_l` 同时构造 N 内统一规范名称图，支持旧阶段条件的精确回拉。
`row_step_proper_name_l` 对随泛型变化的商条件名称构造保持指定主前缀的 proper
后继主加强，`row_step_proper_l` 是其实际旧条件特例。`row_dense_name_l` 在任意
阶段间于原主前缀上选择进入 N 内指定稠密集的商加强名称。`row_step_pil_l` 已
构造相邻后继的内部 `Row_pil_d`，`row_pil_value_l` 自动给出真正的
`τ∈G∩check(N)` 力迫；`row_pil_comp_l` 复合已证明区间，`row_pil_dense_l` 同时
满足指定 N 稠密集并保留原名称的实际尾部比较。滤子名称、名称的原样搬运、
有界公式和旧关系力迫的跨阶段保持均已实现。商名称的前缀投影、进入新商偏序及
实际尾部加强复合也已按 ZF 强度证明。`row_model_sequence_l` 构造共尾于
`sup(N∩β)` 的内部阶段列和 N 内全部稠密集的枚举，并给出原 N 条件的支撑界。
`row_iteration_pr_prepare_l` 进一步从实际 proper 后继规则及可数种子，一次构造
统一辅助名称图、共同 N、全阶段提升与该 N 全部成员后继的迭代引理；
`cohen_rule_pr_l` 已接入任意添加量的现有 Cohen 规则。
该入口还由内部 ω 归纳自动给出全部内部有限区间的迭代引理，包含外部非标准阶段。
`row_cut_step_l` 已证明变动前缀对原名称的限制比较保持；共尾融合保留此比较，
结合已验证支撑界可以恢复完整尾部加强。
`row_pr_thread_l` 已从实际转移生成内部 ω 主前缀序列；`row_pr_coherent_l` 证明全部
前缀一致性。`row_pr_omega_thread_l` 从共同 N 与真实 proper 后继图自动完成首个
内部极限的序列装配，包含初值、共尾列与全部稠密集枚举。类上选择的秩界由实际
反射闭包构造，不要求外部良基性或标准 ω。
`row_pr_bound_l` 现已证明全部早期名称的后期比较；`row_pr_master_fusion_l` 从实际
递归图及支撑界自动构造主融合，比较和给定融合的主性只需 ZF。
`row_iteration_pr_omega_l` 已从 proper 规则、实际可数支撑迭代及种子自动取得内部 ω
终点的完整区间迭代引理。`row_iteration_pr_l` 进一步以实际原公式超限归纳完成
任意内部终点的区间装配；`row_iteration_pr_exists_l` 同时构造迭代，
`cohen_iteration_pil_l` 直接接受添加量与内部长度，提供参数化 Cohen 实例。
`ng_trace_forcing_l` 固定三张实际闭包图构造交集 club，每个成员的同一见证带有
完整内部提升证书。`row_iteration_proper_l` 据此证明所有阶段的 `Proper_d`；
`row_iteration_proper_exists_l` 一次构造整个 proper 迭代，`cohen_iteration_proper_l`
给出任意添加量与内部长度的直接实例，详见 [迭代设施清单](ITERATION.md)。
`proper_countable_l` 自动给出全部旧集合的可数性双向对应，`proper_omega_one_l`
精确保留第一不可数序数。`row_iteration_preserves_l` 将 ZFC、内部 ω、ω₁ 与
旧可数性保持装配到全部阶段；`cohen_iteration_preserves_l` 一次构造参数化实例。
同一规范嵌入还返回 `proper_set_cover_l`：旧集合在扩张中的每个新可数子集，
均有地模型内部可数的旧子集覆盖。覆盖见证通过实际原公式的稠密性由原泛型选出。
`proper_cf_omega_l` 进一步证明 `cf(eα)=eω ↔ cf(α)=ω`；
`proper_countable_bounded_l` 对旧共尾度大于 ω 的任意旧序数 α 返回新可数子集的
严格旧界。这两项也由上述全部阶段的装配入口返回。严格 ω 共尾列在 ZF 内由
可数共尾集实际构造，详见 [可数共尾性保持](ITERATION.md#proper-扩张的可数覆盖ω₁-与可数共尾性保持)。
后继已统一使用最小支撑乘积的幂集作为混合闭名称库；`Row_next_d`、`Row_limit_d` 及各自
原公式给出确定的构造规格。存在性由装配入口返回，唯一性由 `row_next_unique_l`、
`row_limit_unique_l` 在外延性下证明；二步关系显式保存有序对图性质。
`name_pool_represent_l` 在 ZF 下给出同条件的库内等值代表；一般有界见证由
`name_pool_maximum_l` 在 ZFC 下选择。`row_next_witness_l` 返回前缀精确不变的
实际后继条件，`row_next_lower_name_l` 保持指定前缀并提升第二坐标加强。
此处不把给定名称后的构造唯一性扩张为全局名称选择。
内部累积层级及其覆盖定理进一步给出最早层的唯一候选集合。`norm_name_exists_l`
从全局力迫等号类构造唯一规范名称，同时返回规范固定点及全部正条件上的等号
证书；全局等价的输入得到相同规范名称。此层只需 ZF，最大值及所有 Cohen 名称
入口已直接返回这些规范固定点；一般最大值原理仍使用 ZFC。
`unique_maximum_l` 则从实际存在与唯一性公式的力迫证书，在 ZF 内混合全部局部
见证并返回唯一规范名称。Cohen 关系规格现已包含完整图性质，条件、关系及顶
唯一性只需外延性；名称和两个坐标装配入口均已改用 ZF 的唯一见证构造。
`Cohen_names_d`、`cohen_names_m` 给出完整规范三元组的原公式规格，并已证明字面
唯一性。`Row_cohen_d` 与 `row_cohen_m` 把名称装配和坐标后继合为一个确定构造，
`row_cohen_unique_l` 在 ZF 下唯一确定后继条件集及序关系；两个坐标系统入口
直接返回该证书，未要求调用者另行选择名称代表。
第二阶段关系的规范化由 `preord_order_l` 自动完成；
`forces_order_l` 与 `generic_order_l` 核验全部公式力迫和泛型性在规范化前后相同。

## 审计

`python scripts/check_forcing.py` 先以 `lake --wfail build` 构建，再审计实际生产
声明。正则开载体与运算、规范映射、图求值、相对扩张载体、自然数子集名称、
Cohen 名称和节点枚举均严格排除 `Classical.choice`。
像稠密、正向稠密量词对应及部分相容性反射证书允许 Prop 内经典反证；
`ro_dense_l` 的映射函数固定为已审计的 `ro_condition_l`，没有选取见证函数。
Rasiowa–Sikorski 和 Tarski 扩张只在 Prop 存在证明内部使用选择；输出仍是存在
定理，没有定义全局不可计算滤子。完整公式枚举同样只在 Prop 内取得。
核心切片继续仅允许 `propext`、`Quot.sound` 与 Prop 证明中的 `Classical.choice`。
直接引用原公理的 `ZFCBase`／`CohenTheory` 单独审计，只额外继承四条原公理定义
中已经存在的 `native_decide` 自由闭合证书。`InternalClosure`、`InternalCheckModel`
及内部原子真值、全公式真值和 ZF 保持消费原 ZF 时，单独允许原七条固定公理的
既有证书；`SetTheory.Choice` 与 `InternalChoice` 另成切片，只多允许原选择公理
已有的句法闭合证书。这些依赖不开放给核心切片。
复用的 `Ord.Recursion` 与 `Card.Aleph.Hartogs` 一并审计；序列限制及后继唯一性
直接调用相应数学定理，排除了这些步骤原自动化生成的原生计算公理依赖。
内部名称定义、解码图、编码图、条件集、序关系和 Cohen 编码数据也都严格排除
`Classical.choice`。旧列表编码的单射性证书使用经典证明，保留在 Prop 内，
没有封装进本层实际编码函数。
小图规范名称递归的收集只在 Prop 存在证明中使用选择；递归核心、实际公式、
地模型图构造及求值还原证书继续严格排除 `Classical.choice`。
无 `sorry`、新增公理、`noncomputable` 或常驻 smoke 模块。
CH 切片另检查内部依赖选择、ω 基数性、可数并、可数初等子模型及完整塌缩扩张；
只继承原八条 ZFC 句法闭合证书。复用序数引理中的若干原生计算步骤已换成直接证明。
Cohen／独立性切片覆盖内部有限归纳、CCC、无限基数保持、参数化新实数族、¬CH 模型
和原推导核的独立性端点，使用相同的八条既有证书边界；条件与公式数据严格排除经典选择。
迭代切片另审计内部力迫规则、混合、最大值、初等反射、名称预序的二步装配、
泛型双向分解与全局 Cohen 后继实际实例；
继续使用固定既有证书边界，所有条件、公式与投影定义严格排除经典选择。
ZF 反模型、全局泛型判据、规范名称配对、二步名称及等号力迫、关系规范化、名称摊平及扩张同构
另按端点检查原七条 ZF 证书上界，不允许继承原选择公理的句法证书。
坐标追加、限制、前缀拼接、支撑保持、偏序重编码、通用坐标后继和投影复合
也按该 ZF 边界审计；二元可数并与可数积另纳入原 ZF 切片。
模型内阶段序列、支撑极限集合界、极限投影和完全嵌入也已纳入逐端点 ZF 审计。
最小闭支撑与混合闭名称库在原 ZF 边界内审计；固定条件的库内代表、二步与
后继加强均另查 ZF 端点。后继、极限构造式及唯一性端点严格排除经典选择。
累积层级、覆盖、最早层候选集合及名称规范化在同一原七条 ZF 证书边界内审计；
迁入 Project 公共层的谓词实例化在无原公理的核心切片审计。
Cohen 名称、坐标后继和系统后继已按原七条 ZF 证书上界逐端点审计；含 CCC 的
完整 Cohen 结果仍保留原 ZFC，未扩大既有证书集合。
有限支撑直接并、尾部合并、索引名称构造与可数性反射新增 ZF 端点检查。
二步、极限及完整有限支撑 CCC 保持与参数化 Cohen 实例已进入迭代切片；
可数覆盖、名称和规则的原公式数据均通过无经典选择检查。
`N[G]` 的名称、求值图、内部可数性及主条件下的指定公式见证提升按原七条 ZF
证书审计；自动构造承载这些实际见证池的内部初等 N 另允许原选择公理证书。
名称和见证数据严格排除经典选择。有限名称列提升、内部公式码绝对性及
`ng_elementary_l` 的全内部初等提升仍按原七条 ZF 证书审计；实际选择图和
`ng_elementary_hull_l` 的自动装配使用 ZFC，边界见 [ITERATION](ITERATION.md)。
全部 N 参数下的池闭性调用独立的 [Lévy 反射层](../SetTheory/LevyReflection.lean)；
其通用证明与原子解码均在模型论目录，力迫层只保留实际池公式及其消费者。
H(χ) 对应的内部秩、传递闭包和集合存在性只用 ZF；小名称降阶、正则性保持及
自动装配使用 ZFC。内部可数模型捕获 club 的证明保留实际 ω 序列，所有新数据定义
继续排除经典选择；完整 proper 迭代引理及保持接口的准确范围见 [ITERATION](ITERATION.md)。
带指标的确定递归、严格 ω 共尾列与可数共尾集刻画按原七条 ZF 证书审计；
旧序数反射与共尾集传输另检查无原公理依赖，proper 可数共尾性装配使用 ZFC。

可数闭二步与坐标后继的入口为 [TwoStepClosed](TwoStep/Closed.lean) 和
[IterationClosedSuccessor](Iteration/Closed/Successor.lean)：下界精确保留给定共同前缀。
[CollapseClosed](Applications/Collapse/Closed.lean) 实际构造任意名称参数的可数闭塌缩后继、
两组集合参数的可数闭二步塌缩，以及保留原阶段链接和支撑的坐标后继。
`row_cl_induction_l` 已通过实际极限下界和原公式内部超限归纳完成全部闭区间，
`row_iteration_closed_l` 证明任意内部长度的全部阶段可数闭。
[CollapseIteration](Applications/Collapse/Iteration.lean) 从两个集合参数和内部长度自动构造
确定的塌缩迭代，返回各阶段 ZFC、内部 ω，以及实数、任意旧目标上的内部 ω 函数和可数子集的实际旧原像。
`closed_proper_l` 已从内部可数闭预序构造实际 proper club；闭扩张装配也自动返回
ω₁、旧可数性和 ω 共尾性保持。`collapse_iteration_pil_l` 进一步为任意可数种子
构造同一塌缩迭代的共同 N 及完整 proper 区间引理。
证明结构与调用入口见 [迭代设施清单](ITERATION.md#任意内部长度的可数支撑闭迭代)。
