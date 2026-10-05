import YesMetaZFC.Model.SetTheory.Internal.ElementaryClub
import YesMetaZFC.Model.SetTheory.Internal.ElementaryTrace
import YesMetaZFC.Model.SetTheory.Internal.SourceElementary
import YesMetaZFC.Model.SetTheory.Internal.Membership
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.SetTheory.Internal.CanonicalSatisfaction
import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Internal.PredicateSource
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower
import YesMetaZFC.Model.SetTheory.Internal.SeparationHull
import YesMetaZFC.Model.SetTheory.Internal.UniformizationHull
import YesMetaZFC.Model.SetTheory.Internal.SourceField
import YesMetaZFC.Model.SetTheory.Internal.SourceReindex
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem
import YesMetaZFC.Model.SetTheory.Internal.RelationCollapse
import YesMetaZFC.Model.SetTheory.Internal.SourceSequences
import YesMetaZFC.Model.SetTheory.Internal.SourceCollapse
import YesMetaZFC.Model.SetTheory.Internal.SourceOmegaBound
import YesMetaZFC.Model.SetTheory.Internal.SourceBranch
import YesMetaZFC.Model.SetTheory.Internal.SourceHierarchy

/-! # 集合结构、公式码与满足关系的地模型内部编码

`Spred_emb_d` 编码带集合谓词的初等嵌入，量化全部内部公式码；
`spred_exists_l`、`spred_identity_l` 在 ZF 内构造谓词结构码及实际恒等嵌入。
`smap_source_l` 沿实际嵌入复合内部赋值；`spred_source_l` 恢复原隶属语言的
完整初等性，`spred_delta_l` 在传递载体上直接传输背景中的原 Δ₀ 公式。
`rp_model_exists_l` 对有共同细化的实际集合族与非空合法代表函数族，在 ZF 中构造等价类集合、
投影和商关系的内部结构码；`rp_kernel_l` 识别投影核，商关系与代表元无关。
`rp_family_model_l` 先在指定候选集合内分离合法函数；大基数层的 `ed_source_model_l`
已实例化为源模型内部函数与相对派生超滤的商。
对全部背景内部函数的代表族，`rp_satisfies_l` 在 ZFC 下给出全部内部代码的 Łoś 方程；
`rp_los_assignment_l` 自动构造商赋值和代码集。源模型版本 `rs_satisfies_l` 另从实际
源内真值集和对角见证在 ZF 中证明完整内部 Łoś，消费 `Sc_theory_d` 的实际全内部模式。
正则 H(χ) 在 ZFC 中提供初始实例；`Sc_theory_d.map_l` 在 ZF 中传到任意传递初等后继。
`rs_los_assignment_l` 从真实 ω→G 代表赋值自动构造所需空间与商赋值。
`di_elementary_limit_l` 对任意完整初等定向系统证明极限的完整初等性；
`wc_smaps_l` 构造良基外延结构的传递坍塌及完整内部同构；大基数层已接入迭代后继和枝极限。
常值初等嵌入及源内坐标拉回的分量初等映射现已构造，并核验恒等、复合与常值交换律。

`smdl_membership_l` 构造任意非空内部集合的隶属结构码；`scode_exists_l` 收集全部
内部有限公式码；`smdl_satisfaction_l` 构造统一满足关系集合。`smdl_table_l` 一次
返回指定公式的赋值空间、唯一真值表及真值集。各构造仅需 ZF，不依赖外部良基性。
`smodels_theory_l` 给出编码理论及实际模型性实例；`source_compile_l` 把原 Project
AST 编译成内部码并证明对全部编码结构的语义对应，`source_satisfaction_l` 自动
装配有限参数赋值。`scode_numbering_l` 返回全部内部公式码到内部 ω 的单射图，
使用固定的规范编码图；`sc_num_tables_l` 同时返回合法自然数码集与双向图，
`source_nat_satisfaction_l` 将原公式直接接入自然数码上的统一满足关系。
`source_finite_compile_l` 一次生成内部有限参数列，并对全部载体与候选值证明同一码的语义。
`ssk_hull_l` 在 ZFC 中一次构造真实的
内部司寇伦选择图与任意可数种子的最小可数闭包，并给出所有内部有限参数下的
见证闭性。固定运算图的闭包存在、最小性与单步可数性分别保留 ZF 强度。
`selem_hull_l` 进一步一次构造内部可数初等子模型，初等性量化全部内部公式码
及全部内部赋值。有限支撑与完整内部 Tarski–Vaught 等价仅需 ZF；初等关系可
复合并保持内部编码理论的模型性。`selem_source_l`、`selem_witness_l` 通过同一编译码
把完整内部初等性接回原生产公式；力迫层用它反射见证池中的实际名称。
`smap_of_iso_l` 用实际原公式内部归纳证明同构保持全部内部码；`mc_smaps_l`
据此给出 Mostowski 正逆图的完整初等证书。`selem_collapse_l` 在 ZF 中自动构造
传递坍塌及其到原传递结构的初等嵌入；`selem_hull_collapse_l` 再在 ZFC 中从可数种子
同时构造壳与可数传递模型。`Smap_d.models_l` 沿嵌入回拉任意已证明的内部编码理论。
`sfm_close_l` 用原公式内部归纳构造非标准程序的全称闭包；`Smap_d.valid_l` 保持
全部赋值上的有效性，`Smap_d.models_forward_l` 据此正向传输同一个内部编码理论。
`Smap_d.omega_l` 固定背景 ω；`sc_sequences_forward_l` 保持全部字母表的实际有限序列空间，
包括目标中的新参数和全部背景内部有限图。
`sc_h_collapse_l` 实际证明正则 Hχ 中任意相对良基关系的塌缩闭包；
`Sc_collapse_d.map_l` 传输整条存在句子，覆盖后继模型中新出现的关系。
`Sc_collapse_d.wf_absolute_l` 反映良基性；`sc_branch_absolute_l` 把外部下降链换为源内下降链。
可数枝闭包由实际正则 Hχ 和初等传输提供。`Sc_hierarchy_d` 则单独由极限 Vδ 提供，
并传到初等后继的全部新序数；相对层的传递性与唯一性只用 ZF。
`smap_omega_bound_l` 双向保持模型内的不可数共尾性；实际正则基数由 `sc_regular_bound_l` 给出实例。
`sfm_sep_l` 直接构造任意内部程序的分离实例代码，支撑外新变量不会捕获旧参数。
`smap_separation_l` 在目标容纳像集合的全部子集时，回拉源中的实际分离集；
`v_separation_hull_l` 从极限 V 层及可数种子自动构造具有全内部码分离的可数传递模型。
`sfm_total_l` 与 `sfm_collect_l` 构造全内部公式的收集实例；正则 H(χ) 中的实际小见证集
沿 `smap_collection_l` 回到源。`sfm_uniform_l` 构造统一函数图的内部代码，
`smap_uniform_l` 回拉实际源内函数。`h_uniform_hull_l` 从可数种子自动构造同一个具有
全内部码分离、收集与统一化的可数传递模型；统一化的两个实参使用不同坐标。
`pe_compile_l` 对任意内部程序构造逐点解释码及旧根到新根的实际函数图；
原子读取代表函数值，存在量词使用源内常值代表，内部归纳具有实际原公式。
`sc_pe_trace_l` 从真实代表函数赋值构造源中的真值逆像；逐点赋值也实际构造。
`sc_diagonal_l` 把源内部函数族的逐点对角延拓到整个定义域；`sc_pe_witness_l`
由此取得源中统一代表。`rs_los_l` 在实际原公式上完成全部内部行的 Łoś 归纳。
`selem_club_hull_l` 在任意指定内部 club 中构造这样的初等模型，供 proper 主条件装配使用。
`selem_trace_club_l` 以固定司寇伦图的最小闭包在任意子集上实际构造交集 club。
`ssk_mem_s` 在实际集合隶属结构上统一表达全部内部码的司寇伦见证，供泛型初等提升使用。
`Hsub_d` 将内部可数初等 H(χ) 子模型表示为原公式，供力迫证书和内部递归使用。
-/
