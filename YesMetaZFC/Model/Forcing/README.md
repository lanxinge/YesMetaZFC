# 力迫偏序、布尔完备化与名称解释

导入 `YesMetaZFC.Model.Forcing`，声明位于 `YesMetaZFC.Model.Forcing`。
`YesMetaZFC.Model` 已导出此层。任意宿主预序已有实际正则开完备布尔代数和规范
稠密映射。名称求值直接消费现有 `Model.Boolean.BV_graph`，输出实际 `SG_set`。
已有相对名称域的解释扩张、原子真值及 Cohen 新实数实例；内部地模型的
名称域刻画、全公式力迫定理及 `M[G] ⊨ ZFC` 保持证明尚未实现。

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

常用调用顺序如下，其中 `r` 枚举旧实数的成员谓词，`D` 为额外稠密族，
`hD` 是其逐项稠密性证明，`p` 是任意非零 Cohen 条件：

```lean
obtain ⟨U, hU, hp, hd, hn, hg⟩ := cohen_extension_l r D hD p
let ℳ := ext_structure_l (cohen_names_l r) U.mem
-- cohen_ext_old_l r U n：第 n 个旧实数属于 ℳ。
-- cohen_ext_new_l r U：Cohen 名称的实际求值属于 ℳ。
-- hn n：该求值不同于第 n 个旧实数。
-- ext_atomic_l 消费 hg G H hG hH，得到 ℳ 内的等号及隶属真值对应。
```

`cohen_names_l r` 是旧实数规范名称与 Cohen 名称的子名称封闭域，**不是 ZFC
地模型的全部内部名称域**。当前定理并未证明这个相对扩张满足配对、幂集、替换等
全部公理，也没有把可数旧实数族称为 ZFC 地模型。下一层仍需实现内部地模型与名称
之间的对应，以及量词真值和公理保持。`val_surjective_l` 已证明全部宿主名称的
求值像就是全部宿主 `SG_set`，因此不能用全宿主名称域替代地模型相对化。

`python scripts/check_forcing.py` 先以 `lake --wfail build` 构建，再审计实际生产
声明。正则开载体与运算、规范映射、图求值、相对扩张载体、自然数子集名称、
Cohen 名称和节点枚举均严格排除 `Classical.choice`。
像稠密、正向稠密量词对应及部分相容性反射证书允许 Prop 内经典反证；
`ro_dense_l` 的映射函数固定为已审计的 `ro_condition_l`，没有选取见证函数。
Rasiowa–Sikorski 和 Tarski 扩张只在 Prop 存在证明内部使用选择；输出仍是存在
定理，没有定义全局不可计算滤子。无 `sorry`、新增公理、`noncomputable` 或常驻 smoke 模块。
