import YesMetaZFC.SetTheory.Descriptive.Completion
import YesMetaZFC.SetTheory.Descriptive.Borel

/-! # 内部描述集合论：空间、前缀树与 Borel 码

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

所有点、有限长度、开集及开集族都在模型内部解释。Baire、Cantor、柱集、
开集、拓扑、距离、柯西、极限和紧致性均有原公式及语义对应，可使用既有分离
与相对化接口。树、Borel 码、求值、解释及码操作也有原公式。构造只用 ZF，
不增加对象选择公理；可数并接收内部码族。Borel 秩与射影集层次尚未实现。
-/
