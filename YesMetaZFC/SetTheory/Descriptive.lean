import YesMetaZFC.SetTheory.Descriptive.Completion
import YesMetaZFC.SetTheory.Descriptive.Borel
import YesMetaZFC.SetTheory.Descriptive.Projective

/-! # 内部描述集合论：空间、Borel、解析与射影层

`Descriptive.baire_cantor_l` 在任意 ZF 模型内实际构造 Baire、Cantor、全部有限
前缀及其拓扑。`ds_countable_basis_l` 返回实际可数基；`ds_separate_l`、
`ds_cyl_clopen_l`、`ds_no_isolated_l` 分别给出分离、开闭基与无孤立点。
`cantor_subspace_l`、`cantor_closed_l`、`cantor_empty_interior_l` 刻画两空间的关系，
`cantor_power_l` 给出 Cantor 与内部自然数幂集之间的实际双射存在性。

`ds_metric_graph_l` 构造取值为 (0,1) 或 (1,2ⁿ) 的规范有理数距离图，
`ds_dist_zero_l`、`Dist_d.symm_l`、`ds_ultrametric_l` 核验超度量性质；
`ds_metric_open_l` 精确识别其球拓扑。`ds_metric_complete_l` 为内部距离柯西列
构造唯一极限。`cantor_compact_l` 证明任意内部开覆盖具有内部有限子覆盖，
`baire_noncompact_cover_l` 返回 Baire 的具体反例覆盖。
`baire_cantor_complete_compact_l` 一次构造空间及完备、紧致／非紧致终点。

`Tree_d`、`Branch_d`、`Body_d` 给出内部前缀树、分支与树体；树体闭且每个闭集
由其可延伸前缀树表示，这部分只需 KP。`Bcode_d` 是内部良基的带标签树码，
`bsem_exists_unique_l` 构造唯一整树求值，`bden_exists_unique_l` 构造唯一解释集合。
`bcode_basic_l`、`bcode_compl_l`、`bcode_union_l` 实现基本柱集、补和内部可数并码；
`bjoin_m` 是唯一拼接操作的原公式。`bcode_open_l`、`tree_body_borel_l` 给出开集
和闭树体的码，`borel_restrict_l` 实现对子空间的限制。
`baire_cantor_borel_l` 提供两个空间的实际实例和开集／闭树体有码性的统一入口。
`Cl_d` 与树体存在双向等价；`closed_ktree_l` 构造唯一规范前缀树，
`ktree_pruned_l` 证明该树没有死节点。

`rp_graph_l`、`rp_open_l` 构造 Baire 配对双射并核验乘积矩形基；`An_d` 采用
Borel 关系的内部 Baire 投影，`Coan_d` 为其补。解析码解释唯一；可数并和余解析
补族的可数交已构造。`borel_an_l` 给出 Borel 的实际解析表示，闭树投影也已接通。
`borel_closed_proj_l` 将 Borel 求值转换为闭证书关系；`an_closed_l` 和
`an_tree_iff_l` 完成解析集的闭集／闭树投影正规形。`an_prefix_iff_l` 给出
存在内部实数见证、每个内部长度都有树内成对前缀的判据；`anrel_prefix_iff_l`
给出其子空间相对化版本。证书使用最小子编号，不引入可数选择。
`Ps_d`、`Pp_d`、`Pd_d` 是以 Borel 为零层的粗体射影点类；`ps_succ_l` 给出
后继投影方程，`ps_one_l`、`pp_one_l` 识别第一层，`borel_pd_one_l` 给出
Borel ⊆ Δ¹₁。三类均已证明内部层号下的单调性。
`Pcode_d` 把层号、极性和 Borel 码打包；`pden_exists_unique_l` 给出唯一解释。
`phier_exists_unique_l` 构造全部内部层的唯一函数图，`dst_projective_l` 自动给出
空间、配对、层次及 Baire/Cantor 的射影集合族。`Tr_d`、`Rclass_d` 提供子空间迹。

所有点、有限长度、开集及开集族都在模型内部解释。Baire、Cantor、柱集、
开集、拓扑、距离、柯西、极限和紧致性均有原公式及语义对应，可使用既有分离
与相对化接口。树、Borel 码、求值、解释及码操作也有原公式。构造只用 ZF，
不增加对象选择公理；可数并接收内部码族。射影层号取模型自己的 ω，而非外部 Nat。
尚未实现 Borel 秩、分离／完美集定理、Δ¹₁ ⊆ Borel 和射影层次严格性。
-/
