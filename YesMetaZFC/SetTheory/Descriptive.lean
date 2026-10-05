import YesMetaZFC.SetTheory.Descriptive.Completion
import YesMetaZFC.SetTheory.Descriptive.Borel
import YesMetaZFC.SetTheory.Descriptive.Projective
import YesMetaZFC.SetTheory.Descriptive.BorelRank
import YesMetaZFC.SetTheory.Descriptive.Determinacy
import YesMetaZFC.SetTheory.Descriptive.TreeBounded

/-! # 内部描述集合论：空间、Borel、解析、射影层与博弈

`Gm_win_d` 用内部有限局面、内部策略图和 ω 长对局定义双方获胜；
`AD_d` 量化全部内部收益子集。`Axioms.ad_axiom` 是语义对应已核验的原句子。

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
后继投影方程，`ps_one_l`、`pp_one_l` 识别第一层，`pd_one_borel_l` 给出
Δ¹₁=Borel。三类均已证明内部层号下的单调性。
`Pcode_d` 把层号、极性和 Borel 码打包；`pden_exists_unique_l` 给出唯一解释。
`phier_exists_unique_l` 构造全部内部层的唯一函数图，`dst_projective_l` 自动给出
空间、配对、层次及 Baire/Cantor 的射影集合族。`Tr_d`、`Rclass_d` 提供子空间迹。
`Pedit_d` 唯一改写补码和交替量词码；`pc_project_l`、`pc_all_l` 合并同极性的
相邻量词，保持正层 Σ、Π 的层号。`pc_raise_l` 保持极性并升层。
`Bpull_d` 只在原叶后增加一层柱集并；`Ppull_d` 迭代 f↦f×id，把此唯一替换
提升到任意内部射影层。`pc_pull_l` 返回同层连续逆像码与实际解释。
`pc_binary_l`、`pd_binary_l` 在 ZF 中构造各层二元并交。
`Pf_d`、`Fd_d` 分别表示实际码族及其解释函数图；`pf_countable_l` 和
`pd_countable_l` 构造 Σ、Π、Δ 同层可数并交。输入按内部自然数部分编号，允许空族。
一般可数族使用内部实数可数选择；`pf_countable_with_l` 进一步只要求当前指标集
上的选择。`dst_countable_l` 从原 ZFC 模型构造此条件及全部空间实例。
`Pjoin_d` 给出并交运算的原公式；`Prden_d`、`pf_relative_countable_l` 给出
子空间解释及并交相容性。`ps_standard_l`、`pp_standard_l`、`pd_standard_l`
把标准数码 Num_d k n 处的内部层识别为 k 个交替实数量词的 Borel 正规形。

`tree_wf_iff_l` 证明无内部实数分支等价于反向子边内部良基。
`an_separation_l` 沿同步乘积树构造 Borel 分离码；`suslin_l` 证明解析且余解析
当且仅当 Borel。`suslin_relative_l` 只要求子空间解析；`prden_suslin_l` 将
同一相对集合的 Σ¹₁、Π¹₁ 两码转成相对子空间的 Borel 码。
`universal_closed_l` 构造通用闭集；`universal_ps_l`、`universal_pp_l` 构造全部
正内部层的通用集。`projective_nonselfdual_l` 返回 Σ\Π、Π\Σ 的实际对角见证；
`projective_strict_l` 证明 Σ、Π 每个后继层严格增长，`pd_strict_l` 证明 Δ 从
第一层以后严格增长，Δ₀=Δ₁=Borel。`dst_suslin_l` 从 ZF 模型直接给出实例。

`Brank_d` 构造码树上满足 sup(子秩+1) 的唯一实际秩函数；`Bcr_d` 取根秩。
`Bsig_d`、`Bpi_d` 是标准超限 Borel 层级，第一层为开／闭，第二个 Σ 层为 Fσ。
`Bsr_d` 取集合所属 Σ⁰α ∪ Π⁰α 的最小正阶数。`bsr_exists_l` 证明有码集合
有唯一内部可数秩；补集保秩、子空间限制不增秩，任意内部子空间的码解释也有秩。
`dst_borel_rank_l` 自动给出 Baire、Cantor 及两种秩的实际接口。
`an_perfect_l`、`borel_perfect_l` 证明解析／内部有码 Borel 集可数或含非空完美
子集，输出实际闭且无孤立点的集合。分裂导集的稳定性及融合只用 ZF，
不假定 ω₁ 正则或可数选择；`dst_perfect_l` 自动构造所需实例。

所有点、有限长度、开集及开集族都在模型内部解释。Baire、Cantor、柱集、
开集、拓扑、距离、柯西、极限和紧致性均有原公式及语义对应，可使用既有分离
与相对化接口。树、Borel 码、求值、解释及码操作也有原公式。空间、正规形、
连续逆像、有限布尔运算、分离、Suslin 定理、通用集与层次严格性只用 ZF；
一般射影可数并交的选择条件在接口中单独列出。
射影层号取模型自己的 ω，标准层比较不缩小内部量词或见证的范围。
超限 Borel 层号与码树秩取模型自己的序数，不要求外部良基。
尚未实现统一化与决定性；未断言 ZF 中无统一码族的集合式 Borel 类都满足完美集定理。
-/
