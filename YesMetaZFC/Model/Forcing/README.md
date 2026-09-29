# 力迫偏序、布尔完备化与名称解释

导入 `YesMetaZFC.Model.Forcing`，声明位于 `YesMetaZFC.Model.Forcing`。
`YesMetaZFC.Model` 已导出此层。任意宿主预序已有实际正则开完备布尔代数和规范
稠密映射。名称求值直接消费现有 `Model.Boolean.BV_graph`，输出实际 `SG_set`。
已有相对名称域的解释扩张、完整一阶真值对应及 Cohen 新实数实例。一次调用
可得到对全部原公式、任意有限参数同时有效的滤子。全部地模型内部名称的扩张另有
完整内部力迫真值定理及原 ZFC 全部公理保持，包括全分离、全收集模式。
`Internal.preserves_zfc_l` 一次返回模型性；内部名称、规范名称递归、原子力迫、
公式翻译和各公理见证均由实际内部集合构造。

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
| `Order` | `Cmp_l` 是存在共同加强，`Inc_l` 是不相容；`Lower_l`、`down_l`、反链、无原子性、分离性及条件以下的限制。 |
| `Density` | 稠密、局部稠密及预稠密；预稠密等价于向下闭包稠密；两个稠密集在其中一个向下封闭时交仍稠密。 |
| `Density` 的映射 | `PO_hom` 只保序，`PO_compat` 另保持不相容，`PO_dense` 再要求像稠密；证明稠密开集回拉及稠密映射复合。相容性反射只要求 `PO_compat`。 |
| `Separative` | 通过相容性定义分离预序与实际商 `Sep_l`，构造 `sep_order_l` 和规范稠密映射 `sep_map_l`；证明商序分离、规范映射保持并反射相容性。 |
| `Boolean` | 任意 `BA_alg B` 的非零部分给出 `positive_order_l`；相容等价于交非零，差 `p ∧ ¬q` 给出分离见证。条件域非空恰要求代数非平凡。 |
| `Tree` | `List A` 按延长排序；相容恰为前缀可比，任意有限长度的条件稠密；二元树的两个孩子形成反链，整棵树无原子。 |
| `RegularOpen` | `RO_l` 是向下且双重伪补稳定的谓词；`ro_algebra_l` 实际装配交、剩余、双重否定及任意上确界，直接返回原 `CB_alg`。 |
| `Completion` | `ro_principal_l p` 正则化主向下集；`ro_map_l` 保序且保持不相容，`ro_dense_l` 的像稠密。布尔比较恢复 `Sep_le_l`，非零交恢复 `Cmp_l`；分离时反射原顺序，反对称时进一步单射。 |
| `Cohen` | `cohen_algebra_l` 是二元序列树的实际完备布尔代数；`cohen_nontrivial_l` 和 `cohen_atomless_l` 分别给出非平凡性与无原子性。 |
| `Generic` | 条件滤子、主滤子、递降序列滤子；`generic_countable_l` 从任意起始条件构造遇到指定可数稠密族的滤子。 |
| `BooleanGeneric` | 条件滤子转布尔真滤子；显式上确界见证稠密集 `sup_dense_l` 及其稠密性；只有遇到相应稠密集才导出无限析取／合取的真值对应。 |
| `Valuation` | `val_graph_l` 删除未接受的边，`val_l` 取双模拟商；成员递归式、规范名称 `check_graph_l` 及还原定理。数据无需滤子、完备性或代表元选择。 |
| `Truth` | `Name_generic_l` 列出四类具体稠密集；`val_eq_iff_l`、`val_mem_iff_l` 沿图良基归纳证明原子真值对应。可数节点已有泛型滤子存在端点。 |
| `NameGeneric` | `name_family_generic_l` 同时处理可数名称族所有节点对，并允许额外可数稠密要求；有限初段调度直接产生同一个滤子。 |
| `Extension` | `name_span_l` 生成子名称封闭域；`ext_structure_l` 是该域的实际求值像，已有传递性、外延性、良基性、规范名称包含及原子语义接口。 |
| `RealName` | 任意权重序列给出可数的自然数子集名称；求值逐位读取权重。复用原 ω 图，并提供显式节点枚举。 |
| `CohenReal` | `cohen_extension_l` 构造同一滤子：遇到给定稠密族、避开给定可数旧实数族，并满足整个 `cohen_names_l` 名称域的原子真值要求。 |
| `Domain` | 相对名称布尔结构 `domain_str_l` 与原纯语言扩张 `ext_model_l`；求值映射直接满射到解释像，项和环境使用原 `Fn_map` 接口。 |
| `Formula` | `val_formula_iff_l` 对原十一种公式构造证明真值对应；量词只遍历指定名称域，保留原 bound/free 上下文。 |
| `FormulaGeneric` | `fm_dense_l` 由公式及赋值计算量词稠密族，并证明稠密性和向下封闭性；没有让调用者假设量词真值引理。 |
| `FormulaEnumeration` | 复用 `SyntaxNatCoding` 的单射编码及原异质赋值列，证明全部有限参数公式实例可枚举；枚举选择只存在于 Prop 证明中。 |
| `ZFCBase` | 直接核验原外延性、空集、基础公理；当 ω 在实际解释像中时，核验原无穷公理。 |
| `CohenTheory` | `cohen_full_extension_l` 一次生成满足全部公式真值、额外稠密族和新实数要求的同一滤子；`cohen_zfc_base_l` 自动给出四条原公理。 |
| `InternalPair` | 名称的 Kuratowski 有序对编码及原 `OrderedPairConvention` 实例；坐标单射、编码唯一性和三步成员下降。 |
| `InternalNames` | `Internal.Name_d` 的全部量词遍历模型对象；`name_m` 是同一条件的原 Project 公式，已证明语义对应与子名称、标签闭包。 |
| `InternalClosure` | 用模型内部两条明确的分离／收集模式构造支撑，证明 `name_unfold_l`；内部子集和带权二元名称只要求配对与并集。 |
| `InternalGraph` | 从内部支撑和条件集的小呈现解码；`Rep_d` 精确保留并覆盖带权成员，`rep_val_eq_l` 与 `val_exists_unique_l` 保证求值与呈现选择无关。 |
| `InternalRealization` | 原布尔名称实际编码为小图模型中的集合、条件集及支撑；`encode_pred_val_l` 给出求值往返，`sg_check_exists_l` 给出该模型内的规范名称。 |
| `InternalBoolean` | 以集合编码载体和序关系，实现原 `BooleanZF.Boolean_d`；模型内集合族的上确界直接构造。关系编码无需序公理，上确界只消费 `Sup_order`。 |
| `InternalCohen` | Cohen 正则开条件有单射的集合编码；`cohen_boolean_l` 是实际内部布尔代数实例，`cohen_internal_name_l` 是实际模型对象。 |
| `InternalAtomicSyntax`／`InternalAtomicClosure`／`InternalAtomic` | 内部带条件双模拟及其最大关系；证明支撑无关性、等号递归方程及隶属力迫的一阶可定义性。 |
| `InternalConditions`／`InternalDefinability`／`InternalAtomicTruth` | 条件预序、模型内稠密集泛型性、实际见证和反例稠密集；证明原子真值对应。 |
| `InternalFormula`／`InternalLogic`／`InternalTruth` | 原 Project 公式的内部力迫翻译、正则性和完整真值定理；量词遍历全部内部名称。 |
| `InternalNameConstruction`／`InternalSeparation`／`InternalCollection`／`InternalPower` | 有界加权名称构造、任意有限参数的全分离和收集、内部幂集名称。 |
| `InternalZFOperations`／`InternalZF` | 配对、并集、无穷及其余原 ZF 公理装配；`preserves_zf_l` 自动构造名称域非空证书。 |
| `SetTheory.Choice`／`InternalSelection`／`InternalChoice` | 从原选择集公理构造内部序数枚举，证明最早隶属选择的稠密性与唯一性；`preserves_zfc_l` 给出完整 ZFC 保持。 |
| `InternalGenericInstance` | 实际二元布尔条件及其主泛型滤子；`two_extension_zfc_l` 直接实例化完整保持定理。 |

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
两个谓词都有实际 Project 公式，原子真值沿名称图的良基关系证明。

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

```lean
have hExt := Internal.preserves_zfc_l O hZFC hU hM hL
-- O : Internal.Cond_order_d M B R z
-- hU : Internal.Generic_d M B R z U
-- hM : WellFounded M.mem；hL : Internal.Setlike_d M
-- 结论是实际 extension_l 的原 SetTheory.ZFC 模型性，包括全部模式。
have hConcrete := Internal.two_extension_zfc_l
-- 小图地模型与二元布尔主泛型的完整实际实例，无额外模型存在前提。
```

`preserves_zf_l O hZF hU hM hL` 只消费地模型 ZF；选择公理仅在 `preserves_zfc_l`
中使用。外部良基性与小呈现是实际小图解释的前提。尚未提供可数地模型上的
无原子内部泛型存在端点，也未将 Cohen 相对名称域升级为完整内部 Cohen 扩张。

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
