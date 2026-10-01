# 公理验证与不完备性接口指路表

验证对象是原 `intrinsic_proof_theory`、`intrinsic_zfc_theory` 及纯语言中的
`PureModel.theory`。裸 ZFC 的 Rosser、原编码表示的 D1–D3、Löb 与哥二实例已完成；
独立性与哥二的不可证性接口保留裸 ZFC 一致性参数；
[原生小图模型](../YesMetaZFC/Model/SmallGraph/ZFC.lean) 的 `SmallGraph.zfc_consistent`
另在 Lean 元层通过实际模型给出该一致性证明。纯定义构造见 [ELIMINATION.md](ELIMINATION.md)，
证书与检查器见 [NAT_DECODING.md](NAT_DECODING.md)。
[布尔名称模型](../YesMetaZFC/Model/Boolean/ZFC.lean) 的 `bv_models_zfc` 已覆盖任意完备布尔
代数；`Boolean.zfc_consistent` 另由实际命题布尔代数和原推导核可靠性给出一致性。
原支撑理论的无参数及任意有限参数 Tarski 真不可定义性也已完成；语义终点覆盖
任意原模型及每一组参数赋值。`PureTarskiSource` 另已给出保留源编码的裸 ZFC 版本；
其合同按源公式索引。`PureTarski` 现已完成只量化纯公式、使用最终纯公式自身编码的版本。

## 模型、公理与推导

| 要使用的结果 | 接口与源码 | 精确范围 |
| --- | --- | --- |
| 原生小图模型与裸 ZFC 一致性 | [SmallGraph/ZFC](../YesMetaZFC/Model/SmallGraph/ZFC.lean)：`sg_model`、`sg_project_zfc`、`sg_models_zfc`、`zfc_consistent` | 小图双模拟商直接构造；原公理及全部有限参数分离、收集模式已经核验，无模型存在或一致性前提；载体固定为 `Type (u+1)` |
| 标准布尔值 ZFC 模型 | [Boolean/ZFC](../YesMetaZFC/Model/Boolean/ZFC.lean)：`project_zfc`、`bv_models_zfc`、`zfc_consistent` | 任意 `B : Type u` 及实际 `CB_alg B`；名称节点同层，载体固定在 `Type (u+1)`；原公理与所有有限参数模式逐句核验 |
| 任意地模型的内部泛型商 | [Forcing/InternalQuotient](../YesMetaZFC/Model/Forcing/Internal/Extension/Quotient.lean)、[InternalChoice](../YesMetaZFC/Model/Forcing/Internal/Extension/Choice.lean) | 外部非良基、内部 ω 非标准的地模型也满足完整真值及原 ZFC 保持；商载体与地模型同 universe，基础公理通过内部公式归纳证明 |
| ZFC＋CH 的实际力迫模型 | [Forcing/CH](../YesMetaZFC/Model/Forcing/Applications/Continuum/CH.lean)：`ch_forcing_l`、`ch_extension_l`、`ch_model_l` | 对任意地模型构造可数部分函数塌缩，证明每个泛型商满足原 ZFC＋CH；可数地模型自动取得泛型，实际无模型存在前提的实例载体在 `Type 1` |
| 参数化 Cohen 添加与 ZFC＋¬CH | [Forcing/CohenAdd](../YesMetaZFC/Model/Forcing/Applications/Cohen/Add.lean)、[NotCH](../YesMetaZFC/Model/Forcing/Applications/Continuum/NotCH.lean) | 对任意模型内指标集 κ 构造 κ 条互异新实数，保持旧无限基数；添加量超过旧 ω₁ 即否定 CH，自动入口默认取 ω₂ |
| 原 ZFC 的 CH 独立性 | [Forcing/CHIndependence](../YesMetaZFC/Model/Forcing/Applications/Continuum/Independence.lean)：`ch_independent_l`、`ch_consistency_l` | 原 Project Derives 即原纯隶属推导核中的 CH 双侧不可证；两侧一致性由实际模型与既有六规则可靠性给出，不添加新理论或替代 CH 句子 |
| 有限基覆盖原支撑理论 | [FiniteAxiomModels](../YesMetaZFC/Model/ZFC/FiniteAxiomModels.lean) 中 `FiniteAxiomBasis.models_iff`；[ReducedAxioms](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedAxioms.lean) 的 `derives_iff` | 108 个具体闭句与 11 个参数分离模板，共 119 条；与原无限参数理论推导等价，不是公理集合相等 |
| 完整支撑模型 | [PureSupportModels](../YesMetaZFC/Model/ZFC/Pure/PureSupportModels.lean) 的 `support_models` | 同一规范扩张满足整个原支撑理论 |
| 原 ZFC 像及实际纯翻译 | [PureZFCModels](../YesMetaZFC/Model/ZFC/Pure/PureZFCModels.lean) 的 `models`、`translated_models` | 不弱化原公理或 guard |
| 模型扩张与约化 | [PureZFCModels](../YesMetaZFC/Model/ZFC/Pure/PureZFCModels.lean) 的 `expands`、`reduct_models`、`reduction` | 约化适用于任意原模型，不仅规范扩张 |
| 公平调度与正向推导传输 | [PureRosserSchedule](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserSchedule.lean) 的 `source`、`target`；[PureRosser](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosser.lean) 的 `translate_derives` | 使用 Henkin 强完备性传输源闭句推导；一般反向句法保守性不在此结论中 |
| 纯句子嵌入与双向推导 | [PureSentenceTransfer](../YesMetaZFC/Model/ZFC/Pure/PureSentenceTransfer.lean) 的 `embed_m`、`translate_embed_m`、`derives_iff_m` | 对任意纯句子成立；任意源句子的反向往返 `embed_translate_m` 仍须提供其实际 `Agreement` |
| 实际纯固定点 | [PureRosser](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosser.lean) 的 `sentence`、`comparison`、`fixed_point` | 当前源 Rosser 及源 quotation 的实际纯翻译，不是纯语言 quotation 上重新对角化 |
| 任意原模型上的句子对应 | [PureRosserComplete](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) 中 `PureRosser.agreement` | `Agreement` 已有证明；[PureRosser](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosser.lean) 的 `truth_iff` 只涉及规范扩张，不能单独代替它 |
| 裸 ZFC 双侧不可证性 | [PureRosserComplete](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) 中 `PureRosser.independent` | 仅由裸 ZFC 一致性推出当前句子及其否定均不可推导 |
| 裸 ZFC 的 Löb 与第二不完备 | [PureLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLoeb.lean)、[PureSecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSecondIncompleteness.lean) | 全部句子使用纯签名，理论为 `PureModel.theory`；可证明性使用纯嵌入后的原 quotation 和检查器 |

小图层新增的 38 个关键接口已审计。`sg_model` 仅依赖 `propext`；集合存在性及
一致性证明使用已有 `propext`、`Quot.sound`、`Classical.choice`。`zfc_consistent`
还继承原八条固定公理的 `sentence!` 自由闭合性 `native_decide` 依赖：外延、空集、配对、
并集、幂集、无穷、基础及选择各一处。没有新增公理常量、`sorryAx` 或原生验证依赖。
当前全部 1,594 个独立模块及扫描工具严格构建通过；代码范围及载体边界见
[模型论指南](../YesMetaZFC/Model/README.md)。

布尔层新增 50 个关键依赖入口并交叉复核 8 个小图入口。`name_structure`、名称等号的
递归定义、图并合、混合和 ω 数据均无公理依赖；一般布尔值六规则可靠性以及名称的
等词、分离、幂集、无穷、基础证明仅涉及 `propext`、`Quot.sound`。最大值、收集、选择及
ZFC 终点仍依赖 `Classical.choice`；原八处句法闭合性原生依赖与小图终点相同。
未新增 `sorryAx`、自定义公理或原生计算可信依赖。严格不使用元层选择的两类 ZF 模型
尚未实现，具体依赖与全小图基础公理的排中律边界见模型论指南。

集合结构的内部编码由 `scripts/check_internal_models.py` 单独审计，ZF 基础覆盖
65 个模块、1170 条实际声明；司寇伦、club 闭包、遗传小集合、初等模型装配与
类上依赖选择另覆盖 13 个模块、50 条声明。结构码、变量赋值、
非标准有限指令码、递归真值表、统一满足关系及编码理论模型性均有实际原公式。
ZF 基础的存在性只消费原七条既有句法证书；数据与
定义端点严格排除 `Classical.choice`。`smdl_table_l` 给出唯一真值表及精确成员真值，
`smdl_satisfaction_l` 将全部满足对收集成内部集合；没有新增公理或不可计算数据。
`source_compile_l`、`source_satisfaction_l` 已完成原 Project AST 的编译及任意有限
参数下的精确语义对应，不要求解码结构外延。`ZF.countable_fseq_l` 通过内部 ω 递归
构造全部有限序列的统一编号；`scode_numbering_l` 据此给出包含非标准公式的内部
单射。两项只需 ZF。
`ssk_hull_l` 从原 ZFC 自动构造整张内部司寇伦选择图及任意可数种子的最小可数闭包，
并证明所有内部有限参数下的存在见证闭性；假公式的零元运算确保空种子的闭包也非空。
选择图、有限参数延拓、闭包及见证闭性均有实际原公式。通用闭包存在性、最小性、
有限参数阶段截取与单步可数性仍逐声明保持 ZF 边界；自动选择与完整装配允许原选择
公理证书，其余端点另作 ZF 上界核验。
`sbound_exists_l`、`ssat_agree_l` 在原公式归纳中证明内部有限坐标界及支撑一致性；
`ssk_full_l` 把司寇伦见证闭性提升到全部内部赋值。`selem_iff_tv_l` 给出完整内部
Tarski–Vaught 双向等价，`Selem_d` 与 `selem_m` 量化全部内部公式码和 ω→N 赋值，
并有自反性、复合及内部编码理论保持。`selem_hull_l` 在 ZFC 中自动构造任意内部
可数种子的实际内部可数初等子模型，允许地模型外部非良基与非标准 ω。
上述语义证明保留 ZF 强度，只有最后的自动选择装配使用 ZFC。
`selem_source_l` 与 `selem_witness_l` 用同一个实际编译码把内部初等性接回原生产
公式；传递环境中的有序对图绝对性再把实际关系见证取回 N。
`ZFC.fc_club_hull_l` 交替执行一次有限元闭包和给定 club 的扩张，再取内部 ω 链的
并；有限参数截取保证并集闭合。`selem_club_hull_l` 消费实际司寇伦图，故在指定
club 内得到包含可数种子的内部初等模型，所有新接口均有实际构造实例。
原生多排序 AST 接口仍待完成。

通用 Lévy 有限公式反射位于 `Model/SetTheory/LevyReflection`。`ZF.lr_finite_l`
实际构造包含任意指定集合的累积层，统一反射有限原公式族的全部层内参数；
`ZF.lr_reflect_l` 自动处理单公式的量词子公式。见证界由实际赋值空间上的收集
构造，最早累积层给出唯一增长步，内部 ω 递归与累积层族之并完成存在性。
`lr_model_l` 对应到实际内部隶属结构。该层只继承原七条 ZF 证书，全部语法和
结构数据排除经典选择；没有新增反射公理或不可计算实例。公式族是给定的有限
生产 AST，未宣称对全部非标准内部公式码或全宇宙的一次统一反射。

`ng_set_l` 构造扩张内的实际 N[G]，`ng_surjection_l` 构造从地名称集合规范像到
N[G] 的内部求值满射图；`ng_countable_l` 用最小原像编号证明可数性保持，均只需 ZF。
`ng_witness_data_l` 在泛型之前实际构造给定公式的见证池和判定稠密集。
`Ng_witness_d.generic_l` 由主条件在 N 内遇到判定集，再用内部初等性反射见证名称。
`ng_witness_hull_l` 从 properness 自动构造含这些数据的内部可数初等 N 及主加强 q，
接受 q 后同时装配可数 N[G] 和指定公式的见证提升；此自动模型选择层使用 ZFC。
完整池方程及其存在式已有实际原公式。`ng_witness_reflect_l` 消费上述有限反射，
使同一个 N 对指定原公式的所有 N 名称参数都包含真实见证池和判定集。
`image_fseq_l` 与 `image_scode_l` 已核验规范像保留全部内部有限列和公式码；
`ng_fseq_name_l` 对实际求值满射提升参数列，覆盖非标准内部长度。
`ng_operations_l` 构造统一满足关系的判定图和见证选择图，`fc_club_refine_l`
将两种闭性与 proper club 相交。`ng_elementary_hull_l` 自动构造同一个内部初等 N
和主加强，对全部接受该加强的泛型给出完整内部 `N[G]≺X[G]`，两边均有精确
名称成员方程，且 X[G] 传递、N[G] 内部可数。有限列与语法码保持、名称装配及
`ng_elementary_l` 的提升端点限制在原七条 ZF 证书；选择图和自动装配允许原选择
公理证书。数据定义严格排除经典选择。
`h_generic_l` 已通过内部小名称降阶证明地 H(χ) 与扩张 H(eχ) 的双向对应，并保持 χ 正则；
`ng_hchi_hull_l` 自动装配 N[G]≺H(eχ)。实际 club 的内部捕获及 `pr_base_master_l`
支持固定 N 中的主加强，`ng_next_master_l` 进一步自动取得各泛型中 N[G] 的后继主加强。
`two_step_master_l` 已完成真实二步主条件合成，首坐标投影仅用 ZF；
`two_step_master_extension_l` 自动给出任意地模型中含指定种子的二步主加强。
`two_step_master_second_l` 用 N 内实际二步判定集及固定首阶段泛型证明反向第二坐标
主性；`two_step_master_decompose_l` 自动构造 N[G] 名称及完整双向分解。稠密原像
与命中存在性只需 ZF；取回 N 内判定集使用已有的 ZFC 遗传小原子绝对性。
`ng_family_hull_l` 从实际阶段图自动构造共同 N，对其全部成员阶段统一提升
N[G]≺H(eχ)，共同选择图及各阶段切片均有实际集合构造。`ng_family_forcing_l`
已将其升级为内部原公式 `Hlift_d` 的真实力迫证书；`ng_family_ground_l` 自动加入
统一规范名称图，`ng_ground_trace_l` 核验 N[G] 中旧条件的精确回拉。
`row_step_proper_name_l` 已完成后继商条件名称的固定前缀主加强，旧入口
`row_step_proper_l` 直接由规范名称特例推出。真实商名称、库内混合、稠密投影及
`row_dense_force_l` 均只用 ZF；`row_dense_name_l` 再用 ZFC 最大值原理，在任意
阶段间选择进入指定稠密集的商加强名称。任意内部长度的完整区间迭代引理和
实际交集 club 已共同给出最终 `Proper_d` 保持。
`row_step_pil_l` 已给出相邻后继的内部 `Row_pil_d`，`row_pil_value_l` 构造
`τ∈G∩check(N)` 力迫结论；实际滤子
名称、恒等标签的名称固定、有界力迫及旧关系力迫传输只用 ZF。通用
`delta0_image_l` 及环境映射在无原公理、无经典选择边界内单独审计；关系条目
绝对性不要求旧集合全由有序对组成，也不要求源模型外延性。
实际链接的拼接最大下界性质已在全部构造器中证明；名称前缀投影、换段后的
商成员力迫及两段实际尾部加强复合均通过 ZF 审计。`row_model_sequence_l` 已
构造共尾阶段与全部 N 稠密集的两张内部 ω 图，并证明原 N 条件的支撑界。
共尾序列的最小上界构造、内部初等序数迹及稠密集枚举只需 ZF；
变动主前缀条件序列和融合主性均已有实际构造。
固定尾部比较的稠密闭性已在恒等、复合、后继与极限链接中逐一证明；
`row_quot_lower_mono_l` 据此从被迫的名称序关系恢复实际尾部加强的单调性。
`row_pil_comp_l` 只用 ZF 复合已证明区间；`row_pil_dense_l` 使用 ZFC 稠密名称
选择，同时保持主前缀与原名称比较。内部区间命题、恒等实例均单独审计。
`row_pr_family_l` 已通过对象收集与选择实际构造全部后继共用的辅助图。
`row_iteration_pr_prepare_l` 从原公式 proper 规则与可数种子统一返回共同 N、
全阶段提升、规范名称图，以及全部成员后继的内部迭代引理；
`cohen_rule_pr_l` 已验证现有 Cohen 原公式规则的实际适用性。
`row_pil_nat_l` 已以 ZF 的原公式归纳覆盖全部内部有限区间，并直接接入共同模型
装配出口。`row_cut_step_l` 证明前缀延长保留对旧名称限制的真实序比较；
`row_cut_fusion_l` 与 `row_cut_total_l` 在共尾融合及已证明支撑界下恢复完整尾部比较。
`class_indexed_choice_l` 用实际反射见证闭包将可定义类选择降到集合选择，保持
非标准内部 ω 的适用性。`row_pr_thread_l` 实际构造变动主前缀与稠密名称的内部
函数图，`row_pr_coherent_l` 在 ZF 下证明任意两指标之间的精确限制关系。
`row_pr_omega_thread_l` 已由真实 proper 后继图自动构造首个内部极限的全部这些
数据。`row_pr_bound_l` 已将任意早期名称的比较保持到全部后期；`row_pr_tail_l`
构造实际共尾尾段，`row_pr_total_l` 恢复旧偏序的完整尾部比较，均只需 ZF。
`row_pr_master_l` 用规范名称成员反射与拼接最大下界证明融合主性；其 ZF 边界
单独核验。实际主融合的存在使用 ZFC，返回原递归图的全部精确前缀。
`row_iteration_pr_omega_l` 已自动完成内部 ω 终点的完整区间迭代引理，覆盖外部
非标准自然数起点。`row_pr_limit_thread_l` 已保留 γ=sup(N∩β) 完成一般内部极限
的自动序列构造；`row_pr_limit_l` 读取原迭代在 γ 处的真实支撑极限。
`row_pr_induction_l` 用原公式分离反例集，完成所有内部序数上的区间归纳。
`row_iteration_pr_l` 自动取得共同 N 的全部区间，`row_iteration_pr_exists_l` 同时
构造迭代；`cohen_iteration_pil_l` 直接消费现有参数化 Cohen 规则。后继前驱的
内部初等闭包及真实极限规格提取另按 ZF 边界审计。
`fc_trace_club_l` 通过唯一最小闭包及内部递增链的并证明真实交集 club；
`fc_family_l` 合并实际可数运算图族，只需 ZF。`ng_trace_forcing_l` 同时闭合
司寇伦、判定及选择图，每个成员均带指定 N 的真实内部提升。
`row_iteration_proper_l` 由零前缀区间构造主加强，核验全部阶段的 `Proper_d`；
`row_iteration_proper_exists_l`、`cohen_iteration_proper_l` 提供自动构造及参数化实例。
`proper_name_cover_l` 通过实际 N[G] 的原像闭性及旧条件精确回拉构造旧可数覆盖，
原公式的稠密性保证覆盖见证由指定的原泛型接受。`proper_set_cover_l` 覆盖旧集合
的新可数子集；旧集合的 `proper_injection_reflect_l` 已直接迁移到该通用证明。
`proper_countable_l` 自动取得全部旧集合可数性的双向对应与新子集的旧覆盖，
`proper_omega_one_l` 精确保留旧 ω 的 Hartogs 序数。`row_iteration_preserves_l` 与
`cohen_iteration_preserves_l` 一次返回所有阶段泛型扩张的 ZFC、ω、ω₁、旧可数性保持及新可数子集覆盖。
`proper_cf_omega_l` 精确反射并保持共尾度为 ω 的旧序数；旧共尾度大于 ω 时，
`proper_countable_bounded_l` 返回每个新可数子集的严格旧界，两项均已接入同一装配。
ZF 的 `indexed_iteration_l` 为实际确定函数图构造带指标内部 ω 序列，旧依赖选择
接口已迁移为先单值化、再确定递归。`cc_strict_cofinal_l` 取最小共同上界，实际
构造可数共尾集中的严格 ω 共尾列；`cf_omega_countable_l` 给出精确等价刻画。
共尾序列的值域外延性及长度极限性改为直接内核证明，相关模块按原七条 ZF
证书审计，不增加原生 DAG 编译证书。旧序数反射与共尾集传输另按无原公理上界检查。
单射名称证书已迁入通用 `InternalInjection`，其整个模块按 ZF 边界审计，CCC
和 proper 证明均直接调用该模块。

`two_step_chain_bound_l` 已构造精确保留共同首坐标的整链下界，`two_step_closed_l`
由首阶段闭性与被迫后继闭性证明实际二步偏序可数闭。名称序列、其坐标读取与
内部 ω 的规范名称力迫只需 ZF；统一下界名称的最大值选择使用 ZFC。
`row_next_chain_bound_l`、`row_next_closed_l` 在原 `Row_next_d` 的实际双射表示上
回拉、送回下降链，保留原偏序与精确前缀。`collapse_names_l` 由真实可数部分函数
构造给出全部后继名称及闭性力迫；`collapse_pair_closed_l` 从两组集合参数实际
生成可数闭二步塌缩，`row_collapse_closed_l` 自动追加闭坐标后继及阶段链接。
`row_cl_limit_l` 已从真实下降链的可数支撑并完成任意内部极限：有界分支原样
回到较早阶段，共尾分支实际构造严格 ω 共尾指标及相容下界前缀，并以原极限
序关系验证整链下界。`row_cl_induction_l` 对原公式分离反例集，内部超限归纳
统一全部区间；`row_iteration_closed_l` 从零前缀得到全部阶段的可数闭性。
规则仅提供实际名称、旧 ω 名称与被迫闭性，没有将阶段保持结论设为回调。
规范塌缩名称三元组的字面唯一性在 ZF 内证明，`collapse_rule_l` 因而提供确定
原公式规则。`collapse_iteration_preserves_l` 从两个集合参数和内部序数长度
构造整个可数支撑迭代，并返回全部阶段 ZFC、内部 ω、实数、任意旧目标上的内部 ω
函数及旧集合可数子集的实际旧原像。`closed_fn_dense_l` 先由内部稠密交及替换收集
整张旧函数图，再由原泛型遇到该原公式稠密集；`no_new_countable_l` 反射枚举及其
实际值域，同时返回旧子集的内部可数性。
`closed_proper_l` 通过真实二参数见证闭 club 和模型内 ω 下降链证明可数闭预序
的 properness；不需要额外的排除值序公理。`collapse_rule_pr_l` 将该结论提升为
原塌缩后继的实际 proper 力迫，`collapse_iteration_pil_l` 对任意可数种子给出共同
N 与完整区间引理。闭扩张及全阶段保持装配同时复用 proper 层的 ω₁、旧可数性、
ω 共尾性和严格旧序数界证明，保留原来的同一规范嵌入。

力迫源码按[功能目录与构造脉络](../YesMetaZFC/Model/Forcing/INDEX.md)组织；目录职责与
公理审计切片分别维护。数学声明保持原命名空间，审计先检查全部力迫源文件均已登记。

力迫层的 `scripts/check_forcing.py` 审计 403 个生产模块、6727 条声明，包括名称泛型商、
内部基础公理、完整真值、任意地模型的 ZFC 保持、CH 塌缩、参数化 Cohen 添加、
CCC 基数保持、¬CH 模型及原推导核中的 CH 独立性。商载体、解释关系与隶属定义无
经典选择依赖。两侧模型只继承 `propext`、`Quot.sound`、Prop 内选择及原八条固定
公理的句法闭合证书；CH 与 ¬CH 句子的闭合性直接证明，没有新增原生计算公理。
迭代切片的 220 个模块、2929 条声明包含内部力迫规则、等号替换、有界见证、混合与
最大值、任意外延结构的有限参数初等反射，以及分别处于 ZF、ZFC 强度的原公理
全局力迫证书，还有内部二步构造、泛型双向
分解、统一顶名称、阶段完全嵌入、极大反链保持和嵌入复合。名称搬运的内部递归图
已完成存在、唯一性、严格复合，以及恒等阶段删除零标签后的等号力迫。Cohen 后继
由任意添加量名称全局装配。原子等号、隶属及其否定已在阶段像上精确对应；
目标泛型自动回拉为源泛型，并构造名称解释交换的成员满覆盖单射。条件、公式、
商赋值、嵌入及搬运规格数据无经典选择依赖。
二步名称的内部递归转换已有存在唯一性证明；统一名称配对、第一次求值的精确
成员及条目方程、转换后的第二阶段名称性均已核验，原 ZF 配对保持已迁移到统一
构造。带实际原模型公式条件的全局泛型判据，进一步给出配对、有序对与第二阶段
名称性的首阶段力迫证书。双重求值已装配为原二步名称上的函数，满足总性、唯一性
与组合滤子下的精确成员递归；条件域内关系不变则全部名称力迫和泛型性均不变。
这些 ZF 端点另行核验七条既有 ZF 句法证书的上界，不能继承选择公理的证书；
本次逐端点检查覆盖 169 个入口，并检查所有审计名称实际存在。
二步等号经实际公式的内部条目归纳传至嵌套等号，反向则在原模型闭支撑上分离
实际双模拟，并用有限参数泛型反射取得匹配见证。因此双重求值已在单次二步商类上
给出成员满覆盖单射。固定深度内部条目归纳已构造任意第二阶段名称的摊平，并
核验全局还原力迫及双重值还原。`two_step_iso_l` 已进一步给出单次二步扩张与
双重扩张间保持并反射成员的双射；原部分映射接口直接迁移到同构层。
坐标条件层已构造模型内零阶段和任意名称后继：省略顶名称坐标后，旧条件按
原对象完全嵌入下一阶段，顶不变，旧前缀精确恢复；有限与可数支撑的限制、
追加和前缀拼接保持均只需 ZF。后继已返回实际限制投影的单调性，以及保留原
尾部时任意旧前缀加强的提升；阶段链接的恒等与复合也已证明。
`row_cohen_successor_l` 消费已验证的全局 Cohen 名称装配，
提供添加量名称参数化的实际坐标后继。条件序的原公式已移到二步公共层，阶段
编码不依赖可数反射模块；声明及所有消费者已统一迁移。
实际模型内阶段序列已有零系统、名称后继及参数化 Cohen 后继。支撑极限通过
阶段条件图条目的集合界和原公式分离实际构造，全部阶段的限制投影与完全嵌入
同时装配；把极限写回序列后可继续后继。系统追加只需 KP，通用极限层只需 ZF。
后继名称库已统一迁移到最小支撑乘积的内部幂集；二步关系增加有序对图的定义字段。给定
具体名称后，二步条件集与关系、坐标后继及极限对象均有唯一性证明。后继与极限
的原公式规格直接由生产构造返回；定义和唯一性另核验不含经典选择。
混合闭合与固定条件的库内等值代表只需 ZF；有界存在式的统一见证选择使用 ZFC。
`row_next_witness_l` 返回精确固定前缀的实际后继条件；给定第二坐标加强名称时，
`row_next_lower_name_l` 已在 ZF 内提升为实际后继加强。这些接口已接入真实后继库。
累积层级由实际内部超限递归构造；覆盖全部对象的定理通过原公式成员归纳与
收集证明。最早层见证集合给出全局力迫等号类的规范名称，存在、唯一性、全局
等号及幂等性均在原 ZF 切片核验。最大值和所有 Cohen 名称入口已传播规范固定点；
一般最大值的 ZFC 强度不变。通用谓词实例化已迁入 Project 公共层并在核心切片
重新审计，旧力迫命名空间声明已移除。
有界局部见证池现在由一般最大值与唯一见证构造共同消费。唯一性使用实际原
公式，经名称实例化与蕴涵消去转为等号力迫；整个池可以在原 ZF 内混合成唯一
规范名称。Cohen 规格补上完整有序对图性质后，条件集、关系及顶均唯一，名称
装配与两个坐标系统消费者已降低到 ZF，并新增逐端点依赖上界检查。
完整规范三元组与整个 Cohen 坐标后继现在都有原公式规格和字面唯一性；构造
接口已统一返回这些证书。新增公式和满足关系严格排除经典选择，两个唯一性
端点另核验原七条 ZF 证书上界。
完整内部递归现以实际 `row_op_s` 和 `row_invariant_s` 实现：历史双投影由原
替换模式构造，投影与限制交换；原公式的内部序数归纳排除无效历史分支。
`row_iteration_l`、唯一性、前缀方程和一键 Cohen 实例均在 ZF 端点上界内审计。
规则、算子、归纳公式和整个迭代的公式数据严格排除经典选择。
公共 `TermVector.ofFn` 已改用有限列表生成同序数组，读取及闭合性证明复用
构造性的列表引理，消除了原数组读取证明间接带入的元层选择。该语法模块及
四个参数向量端点已纳入核心审计，全部原消费者同步重建。
有限支撑直接并刻画、任意名称二步 CCC、非零极限 CCC 及完整内部迭代保持均已证明。
极限证明使用原公式的阶段归纳与有限尾支撑归纳；后继证明实际构造反链索引名称和
第二坐标单射图，再由首阶段 CCC 计数。`row_iteration_ccc_exists_l` 与
`cohen_iteration_ccc_l` 已接成通用及参数化实际入口。直接并、尾部合并、索引名称
构造和相关泛型反射保持原 ZF 依赖上界；完整 CCC 定理使用 ZFC。
新增公式及接口数据不使用经典选择。内部可数多值闭包、club、主条件原公式、
CCC properness 实例及参数化 Cohen 名称的全局 properness 证书已经实现。
可数支撑共尾前缀的实际并、唯一性、限制与条件重构也已证明；它们不假设支撑或
指标在模型外部可数。可数支撑的完整 properness 保持及二步主条件双向分解均已完成，边界见
[迭代设施清单](../YesMetaZFC/Model/Forcing/ITERATION.md)。

## 任意原模型的内部证明码对应

下列接口连接任意原模型与其纯约化的规范重扩张。自然数指模型内部 ω，
允许非标准元素；局部规则比较同一候选集合轨迹，不对内部 ω 作外部归纳。

| 需要保持的内容 | 接口与源码 | 使用条件 |
| --- | --- | --- |
| 标准数码与 quotation | [PureSourceNumerals](../YesMetaZFC/Model/ZFC/Pure/PureSourceNumerals.lean) 的 `numeral_agrees`、`quotation_agrees`、`proof_numeral_agrees` | 只凭标准码结果不能推出全部内部自然数对应 |
| 当前证明码域 | [ReducedNaturalProofPresentation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedNaturalProofPresentation.lean) 的 `presentation`、`natural_of_satisfied` | `code ∈ ω` 包装保留检查器、标准码正负表示及完备性；旧后继码域见 [RosserDomainBoundary](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/RosserDomainBoundary.lean) |
| 同一内部 ω 及顺序 | [PureSourceInfinity](../YesMetaZFC/Model/ZFC/Pure/PureSourceInfinity.lean) 的 `omega_agrees`、`member_natural`、`natural_compare` | 来自原归纳定义与最小性，不添加标准性假设 |
| 合法映射与求值 | [PureSourceMappings](../YesMetaZFC/Model/ZFC/Pure/PureSourceMappings.lean) 的 `ordered_agrees`、`mapping_project`、`application_agrees` | 求值保持限于原定义域；不宣称非法输入总值对应或映射谓词无条件反向等价 |
| 内部加、乘、幂 | [PureSourceArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureSourceArithmetic.lean) 的 `addition_agrees`、`multiplication_agrees`、`exponentiation_agrees` | 使用实际有限递推图及内部唯一性，覆盖所有内部自然数输入 |
| 配数、字段与根编码 | [PureSourceCoding](../YesMetaZFC/Model/ZFC/Pure/PureSourceCoding.lean) 的 `pairing_agrees`、`fields_agrees`、`node_agrees`；[PureNaturalRosserAgreement](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNaturalRosserAgreement.lean) 的 `root_agrees` | 实际编码保持；根值不是待填前提 |
| 幂集界与集合轨迹 | [PureSourceBounds](../YesMetaZFC/Model/ZFC/Pure/PureSourceBounds.lean) 的 `power_agrees`、`trace_bound_agrees`、`trace_row_natural`；[PureNaturalRosserAgreement](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNaturalRosserAgreement.lean) 的 `proof_trace` | 保留实际 `P(ω)` 界和轨迹行的自然数证据 |
| 有界见证与局部规则 | [ObjectHornSemantics](../YesMetaZFC/Automation/ObjectHornSemantics.lean)；[PureSourceHorn](../YesMetaZFC/Model/ZFC/Pure/PureSourceHorn.lean) 的 `condition_agrees`、`localTest` | 递归前提读取同一候选集合；不假定其外部有限 |
| 自然数参数的公式组合 | [PureSourceFormula](../YesMetaZFC/Model/ZFC/Pure/PureSourceFormula.lean) 的 `instantiate`、`quantify` | 保留自然数环境、逐变量相等和实际见证界 |
| 公理检查 | [PureSourceSchemas](../YesMetaZFC/Model/ZFC/Pure/PureSourceSchemas.lean) 的 `axiomTest` | 固定公理表及分离、收集、替换模式的实际中间码连接 |
| 节点、行与完整证明图 | [PureSourceLocalTests](../YesMetaZFC/Model/ZFC/Pure/PureSourceLocalTests.lean) 的 `currentNode`、`currentRow`、`row_agrees`、`proof_agreement` | 任意固定结论、全部内部自然数证明码；提供 Rosser 所需的两项 ProofAgreement |
| 图对应推出句子对应 | [PureNaturalRosserAgreement](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureNaturalRosserAgreement.lean) 的 `proof_agreement_of_rows`、`agreement_of_natural_proofs` | 局部行与两侧图对应均已有上述实际实例，最终由 `PureRosser.agreement` 装配 |

旧后继码域包含 ω 自身，不能由根项属于 ω 推断原输入属于 ω。
这一边界既不是 `Agreement` 的反例，也不是其不可证明性结论；当前自然数包装和
上表的内部对应已经完成实际实例。

## Δ₀ 的适用范围

| 结果 | 入口 | 边界 |
| --- | --- | --- |
| 支撑语言的 Δ₀ 等价代表 | [ReducedRosser](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedRosser.lean) 的 `predicate_delta0`、`delta0Sentence_delta0`、`delta0Sentence_independent` | 语言含 ω、幂集及编码函数；不自动成为纯隶属或一阶算术 Δ₀ |
| 无参数纯闭 Δ₀ 可决定 | [FunctionFreeDelta0](../YesMetaZFC/Automation/FunctionFreeDelta0.lean) 的 `closed_decided` | 纯 ℒ 只有二元 ∈，没有常元、函数或零元关系 |
| 当前纯闭句非 Δ₀ | [PureRosserDelta0](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `sentence_not_delta0`、`comparison_not_delta0` | 无条件的语法分类；不能再列为正向分类待办 |
| 排除闭 Δ₀ 等价代表 | [PureRosserDelta0](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `no_closed_delta0_equivalent` | 假定裸 ZFC 一致，排除可证明等价的无参数纯 Δ₀ 闭句 |
| 三参数纯 Δ₀ 矩阵 | [PureRosserDelta0](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `matrix_delta0`、`parameters_exists`、`parameters_unique`、`sentence_iff_matrix`、`representation_derives` | 参数为内部 ω 与两侧内部证明码集合；参数定义本身未分类为 Δ₀ |

矩阵为 $\delta(w,A,B)=\neg\exists p\in w\,(p\in A\land\forall q\in p\,q\notin B)$。
实际推导为 `ZFC ⊢ R ↔ ∃w,A,B (Def(w,A,B) ∧ δ(w,A,B))`；
`representation_not_delta0` 明确包含参数定义的整个存在闭句非 Δ₀。
这些参数通过纯分离得到，不意味着原证明谓词已获得纯 Δ₀ 定义；
`∃p∈ω` 也不能直接当作一阶算术的有界量词。

## 公理与证明索引

下表保持有限基原顺序。覆盖由 `FiniteAxiomBasis.models_iff` 和正式推导保证，
不由表格计数推断；项与项列求值的合取按原基计一条。

| 编号 | 原基公理或模板 | 验证定理 |
| --- | --- | --- |
| 1 | `(empty_predicate (free := [])).separation_axiom` | `PureSupportSeparation.separation_axiom (empty_predicate (free := []))`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 2 | `membership_relation_predicate.separation_axiom` | `PureSupportSeparation.separation_axiom membership_relation_predicate`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 3 | `Nonlogical.BasicSetTheory.infinity_axiom` | `PureFinalInfinity.infinity`；[PureFinalInfinity](../YesMetaZFC/Model/ZFC/Pure/PureFinalInfinity.lean) |
| 4 | `term_value_definition_axiom ∧ₘ term_list_value_definition_axiom` | `And.intro (PureFinalSyntax.term_value) (PureFinalSyntax.term_list_value)`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 5 | `binary_union_definition_axiom` | `PureFinalBasic.binary_union`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 6 | `bounded_subset_definition_axiom` | `PureFinalRelations.bounded_subset`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 7 | `cardinality_leq_definition_axiom` | `PureFinalRelations.cardinality_leq`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 8 | `cardinality_strict_less_definition_axiom` | `PureFinalRelations.cardinality_strict_less`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 9 | `cartesian_product_definition_axiom` | `PureFinalCollections.cartesian_product`；[PureFinalCollections](../YesMetaZFC/Model/ZFC/Pure/PureFinalCollections.lean) |
| 10 | `domain_definition_axiom` | `PureFinalMappings.domain`；[PureFinalMappings](../YesMetaZFC/Model/ZFC/Pure/PureFinalMappings.lean) |
| 11 | `empty_set_definition_axiom` | `PureFinalBasic.empty_set`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 12 | `equality_axiom_schema_definition_axiom` | `(PureFinalSyntax.schema_axioms).2.2`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 13 | `extensionality_axiom` | `PureFinalBasic.extensionality_axiom`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 14 | `finite_hierarchy_definition_axiom` | `PureFinalConstructions.finite_hierarchy`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 15 | `finite_sequence_concatenation_definition_axiom` | `PureFinalConstructions.finite_sequence_concatenation`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 16 | `finite_sequence_flatten_definition_axiom` | `PureFinalConstructions.finite_sequence_flatten`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 17 | `finite_sequence_space_definition_axiom` | `PureFinalConstructions.finite_sequence_space`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 18 | `finite_subset_collection_definition_axiom` | `PureFinalConstructions.finite_subset_collection`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 19 | `finite_subset_collection_separation_axiom` | `PureFinalSeparation.finite_subset_collection`；[PureFinalSeparation](../YesMetaZFC/Model/ZFC/Pure/PureFinalSeparation.lean) |
| 20 | `finite_universe_definition_axiom` | `PureFinalConstructions.finite_universe`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 21 | `free_variable_occurs_definition_axiom` | `PureFinalSyntax.free_variable_occurs`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 22 | `function_application_definition_axiom` | `PureFinalMappings.application`；[PureFinalMappings](../YesMetaZFC/Model/ZFC/Pure/PureFinalMappings.lean) |
| 23 | `godel_pairing_definition_axiom` | `PureFinalConstructions.godel_pairing`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 24 | `hereditarily_finite_definition_axiom` | `PureFinalRelations.hereditarily_finite`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 25 | `identity_definition_axiom` | `PureFinalCollections.identity`；[PureFinalCollections](../YesMetaZFC/Model/ZFC/Pure/PureFinalCollections.lean) |
| 26 | `image_definition_axiom` | `PureFinalOperations.image`；[PureFinalOperations](../YesMetaZFC/Model/ZFC/Pure/PureFinalOperations.lean) |
| 27 | `index_order_definition_axiom` | `PureFinalConstructions.index_order`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 28 | `inductive_core_definition_axiom` | `PureFinalInfinity.inductive_core`；[PureFinalInfinity](../YesMetaZFC/Model/ZFC/Pure/PureFinalInfinity.lean) |
| 29 | `is_bijection_definition_axiom` | `PureFinalRelations.is_bijection`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 30 | `is_countable_definition_axiom` | `PureFinalRelations.is_countable`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 31 | `is_countably_infinite_definition_axiom` | `PureFinalRelations.is_countably_infinite`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 32 | `is_dedekind_finite_definition_axiom` | `PureFinalRelations.is_dedekind_finite`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 33 | `is_equinumerous_definition_axiom` | `PureFinalRelations.is_equinumerous`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 34 | `is_equivalence_relation_definition_axiom` | `PureFinalRelations.is_equivalence_relation`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 35 | `is_finite_definition_axiom` | `PureFinalRelations.is_finite`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 36 | `is_function_definition_axiom` | `PureFinalMappings.is_function`；[PureFinalMappings](../YesMetaZFC/Model/ZFC/Pure/PureFinalMappings.lean) |
| 37 | `is_inductive_set_definition_axiom` | `PureFinalRelations.is_inductive_set`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 38 | `is_infinite_definition_axiom` | `PureFinalRelations.is_infinite`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 39 | `is_injective_definition_axiom` | `PureFinalRelations.is_injective`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 40 | `is_linear_order_definition_axiom` | `PureFinalRelations.is_linear_order`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 41 | `is_mapping_definition_axiom` | `PureFinalMappings.is_mapping`；[PureFinalMappings](../YesMetaZFC/Model/ZFC/Pure/PureFinalMappings.lean) |
| 42 | `is_natural_discrete_linear_order_definition_axiom` | `PureFinalRelations.is_natural_discrete_linear_order`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 43 | `is_order_embeddable_definition_axiom` | `PureFinalRelations.is_order_embeddable`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 44 | `is_order_embedding_definition_axiom` | `PureFinalRelations.is_order_embedding`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 45 | `is_order_isomorphic_definition_axiom` | `PureFinalRelations.is_order_isomorphic`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 46 | `is_order_isomorphism_definition_axiom` | `PureFinalRelations.is_order_isomorphism`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 47 | `is_ordered_pair_definition_axiom` | `PureFinalPairs.is_ordered_pair`；[PureFinalPairs](../YesMetaZFC/Model/ZFC/Pure/PureFinalPairs.lean) |
| 48 | `is_relation_definition_axiom` | `PureFinalPairs.is_relation`；[PureFinalPairs](../YesMetaZFC/Model/ZFC/Pure/PureFinalPairs.lean) |
| 49 | `is_surjective_definition_axiom` | `PureFinalRelations.is_surjective`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 50 | `is_transitive_set_definition_axiom` | `PureFinalRelations.is_transitive_set`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 51 | `is_uncountable_definition_axiom` | `PureFinalRelations.is_uncountable`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 52 | `left_projection_definition_axiom` | `PureFinalPairs.left_projection`；[PureFinalPairs](../YesMetaZFC/Model/ZFC/Pure/PureFinalPairs.lean) |
| 53 | `logical_axiom_code_definition_axiom` | `PureFinalSyntax.logical_axioms`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 54 | `mapping_collection_definition_axiom` | `PureFinalCollections.mapping_collection`；[PureFinalCollections](../YesMetaZFC/Model/ZFC/Pure/PureFinalCollections.lean) |
| 55 | `maximum_natural_order_definition_axiom` | `PureFinalExtrema.maximum_natural_order`；[PureFinalExtrema](../YesMetaZFC/Model/ZFC/Pure/PureFinalExtrema.lean) |
| 56 | `membership_irreflexive_axiom` | `PureFinalBasic.irreflexivity`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 57 | `membership_relation_definition_axiom` | `PureFinalOperations.membership_relation`；[PureFinalOperations](../YesMetaZFC/Model/ZFC/Pure/PureFinalOperations.lean) |
| 58 | `minimum_difference_definition_axiom` | `PureFinalConstructions.minimum_difference`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 59 | `minimum_linear_order_definition_axiom` | `PureFinalExtrema.minimum_linear_order`；[PureFinalExtrema](../YesMetaZFC/Model/ZFC/Pure/PureFinalExtrema.lean) |
| 60 | `minimum_natural_order_definition_axiom` | `PureFinalExtrema.minimum_natural_order`；[PureFinalExtrema](../YesMetaZFC/Model/ZFC/Pure/PureFinalExtrema.lean) |
| 61 | `modus_ponens_definition_axiom` | `PureFinalSyntax.modus_ponens`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 62 | `natural_addition_definition_axiom` | `PureFinalConstructions.natural_addition`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 63 | `natural_addition_upper_bound_axiom` | `PureFinalArithmetic.addition_upper_axiom`；[PureFinalArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureFinalArithmetic.lean) |
| 64 | `natural_difference_definition_axiom` | `PureFinalConstructions.natural_difference`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 65 | `natural_exponent_product_index_bound_axiom` | `PureFinalArithmetic.exponent_product_axiom`；[PureFinalArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureFinalArithmetic.lean) |
| 66 | `natural_exponentiation_definition_axiom` | `PureFinalConstructions.natural_exponentiation`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 67 | `natural_exponentiation_index_bound_axiom` | `PureFinalArithmetic.exponent_axiom`；[PureFinalArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureFinalArithmetic.lean) |
| 68 | `natural_godel_pairing_coordinate_bound_axiom` | `PureFinalArithmetic.pairing_axiom`；[PureFinalArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureFinalArithmetic.lean) |
| 69 | `natural_le_lt_transitivity_axiom` | `PureFinalArithmetic.transitivity_axiom`；[PureFinalArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureFinalArithmetic.lean) |
| 70 | `natural_multiplication_definition_axiom` | `PureFinalConstructions.natural_multiplication`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 71 | `natural_order_type_definition_axiom` | `PureFinalConstructions.natural_order_type`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 72 | `natural_positive_left_addition_strict_bound_axiom` | `PureFinalArithmetic.positive_addition_axiom`；[PureFinalArithmetic](../YesMetaZFC/Model/ZFC/Pure/PureFinalArithmetic.lean) |
| 73 | `natural_subset_type_definition_axiom` | `PureFinalConstructions.natural_subset_type`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 74 | `nonempty_finite_sequence_space_definition_axiom` | `PureFinalConstructions.nonempty_finite_sequence_space`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 75 | `nonempty_finite_sequence_space_separation_axiom` | `PureFinalSeparation.nonempty_sequence_space`；[PureFinalSeparation](../YesMetaZFC/Model/ZFC/Pure/PureFinalSeparation.lean) |
| 76 | `omega_definition_axiom` | `PureFinalInfinity.omega`；[PureFinalInfinity](../YesMetaZFC/Model/ZFC/Pure/PureFinalInfinity.lean) |
| 77 | `omega_pair_less_definition_axiom` | `PureFinalRelations.omega_pair_less`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 78 | `omega_recursive_sequence_definition_axiom` | `PureFinalConstructions.omega_recursive_sequence`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 79 | `ordered_pair_definition_axiom` | `PureFinalPairs.ordered_pair`；[PureFinalPairs](../YesMetaZFC/Model/ZFC/Pure/PureFinalPairs.lean) |
| 80 | `ordered_pair_reverse_definition_axiom` | `PureFinalPairs.reverse`；[PureFinalPairs](../YesMetaZFC/Model/ZFC/Pure/PureFinalPairs.lean) |
| 81 | `pair_definition_axiom` | `PureFinalBasic.pairing`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 82 | `pairing_axiom` | `PureFinalBasic.pairing_exists`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 83 | `power_set_axiom` | `PureFinalBasic.power_exists_axiom`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 84 | `power_set_bijection_definition_axiom` | `PureFinalConstructions.power_set_bijection`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 85 | `power_set_definition_axiom` | `PureFinalBasic.power_definition`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 86 | `propositional_axiom_schema_definition_axiom` | `(PureFinalSyntax.schema_axioms).1`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 87 | `quantifier_axiom_schema_definition_axiom` | `(PureFinalSyntax.schema_axioms).2.1`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 88 | `range_definition_axiom` | `PureFinalMappings.range`；[PureFinalMappings](../YesMetaZFC/Model/ZFC/Pure/PureFinalMappings.lean) |
| 89 | `recursive_sequence_space_definition_axiom` | `PureFinalConstructions.recursive_sequence_space`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 90 | `related_nonlogical_symbol_set_definition_axiom` | `PureFinalSyntax.nonlogical_symbols`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 91 | `related_syntax_definition_axiom` | `PureFinalSyntax.related_syntax`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 92 | `relation_composition_definition_axiom` | `PureFinalOperations.composition`；[PureFinalOperations](../YesMetaZFC/Model/ZFC/Pure/PureFinalOperations.lean) |
| 93 | `relation_converse_definition_axiom` | `PureFinalOperations.converse`；[PureFinalOperations](../YesMetaZFC/Model/ZFC/Pure/PureFinalOperations.lean) |
| 94 | `relation_image_separation_axiom` | `PureFinalSeparation.relation_image`；[PureFinalSeparation](../YesMetaZFC/Model/ZFC/Pure/PureFinalSeparation.lean) |
| 95 | `restriction_definition_axiom` | `PureFinalCollections.restriction`；[PureFinalCollections](../YesMetaZFC/Model/ZFC/Pure/PureFinalCollections.lean) |
| 96 | `right_projection_definition_axiom` | `PureFinalPairs.right_projection`；[PureFinalPairs](../YesMetaZFC/Model/ZFC/Pure/PureFinalPairs.lean) |
| 97 | `singleton_definition_axiom` | `PureFinalBasic.singleton`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 98 | `structural_syntax_definition_axiom` | `PureFinalSyntax.structural_syntax`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 99 | `structure_definition_axiom` | `PureFinalSyntax.structure_axiom`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 100 | `subset_definition_axiom` | `PureFinalBasic.subset`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 101 | `successor_definition_axiom` | `PureFinalBasic.successor`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 102 | `symmetric_difference_definition_axiom` | `PureFinalOperations.symmetric_difference`；[PureFinalOperations](../YesMetaZFC/Model/ZFC/Pure/PureFinalOperations.lean) |
| 103 | `syntax_transform_definition_axiom` | `PureFinalSyntax.syntax_transform`；[PureFinalSyntax](../YesMetaZFC/Model/ZFC/Pure/PureFinalSyntax.lean) |
| 104 | `transitive_closure_definition_axiom` | `PureFinalConstructions.transitive_closure`；[PureFinalConstructions](../YesMetaZFC/Model/ZFC/Pure/PureFinalConstructions.lean) |
| 105 | `unbounded_subset_definition_axiom` | `PureFinalRelations.unbounded_subset`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 106 | `union_axiom` | `PureFinalBasic.union_exists_axiom`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 107 | `union_definition_axiom` | `PureFinalBasic.union_definition`；[PureFinalBasic](../YesMetaZFC/Model/ZFC/Pure/PureFinalBasic.lean) |
| 108 | `well_order_definition_axiom` | `PureFinalRelations.well_order`；[PureFinalRelations](../YesMetaZFC/Model/ZFC/Pure/PureFinalRelations.lean) |
| 109 | `SupportAssembly.closedTemplate .cartesianProduct` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 110 | `SupportAssembly.closedTemplate .composition` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 111 | `SupportAssembly.closedTemplate .converse` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 112 | `SupportAssembly.closedTemplate .domain` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 113 | `SupportAssembly.closedTemplate .identity` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 114 | `SupportAssembly.closedTemplate .indexOrder` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 115 | `SupportAssembly.closedTemplate .inductiveCore` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 116 | `SupportAssembly.closedTemplate .mappingCollection` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 117 | `SupportAssembly.closedTemplate .powerSetBijection` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 118 | `SupportAssembly.closedTemplate .range` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |
| 119 | `SupportAssembly.closedTemplate .symmetricDifference` | `PureSupportSeparation.parameter_template`；[PureSupportSeparation](../YesMetaZFC/Model/ZFC/Pure/PureSupportSeparation.lean) |

## 可导性、内部反射与不完备性核验

在既有 D1、D2 接口之上，已完成
内部数码总性与唯一性、固定 AST 的非标准自由代入、模式 2 点实例化连接、
任意内部上下文下的数码语法，以及内部结论码上的节点装配、MP 和数码存在引入。
现已补上任意有限参数定理的非标准数码特化、自然数 guard 反射、零测试
正负反射、任意两个内部自然数的数码相等／不等与严格／非严格序反射，
以及加、乘、幂、Gödel 配对与复合编码项的数码求值。
编码项入口覆盖字段列、节点、Horn 表达式、参数化 AST 码项和既定 quotation。
原子判断及命题联结词的正负反射已完成；自然数有界全称／存在也有正负反射，
界可为已求值的复合项。固定有限轨迹骨架的逐行内部证明可经 `finite_verification`
接回原验证矩阵。数码递归图已完成任意内部轨迹的正负反射，并接入复合项；
投影图也完成了全部七条规则的内部正反射；一般语法图的项、参数列和全部公式
构造子已完成内部正反射。原四种语法变换、schema 各递归图、传输包解码以及
完整 schema／公理行查询现已完成正反射。原 27 类逻辑公理、6 类证明节点、
实际局部行查询也已完成正反射，并接入原检查步骤。完整 checked 轨迹的任意内部
根行反射现已完成，原验证矩阵与完整证明矩阵均已反射。
公共入口为 [InternalNumeralProof](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralProof.lean)
和 [ReducedProofReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofReflection.lean)。
`InternalNumeralReflection.natural`、`natural_derives`、`zero`、`nonzero` 均已证明，
`equal`、`unequal`、`unequal_derives`、`order`、`weak_order`、`order_derives`
及 `arithmetic_evaluation_derives` 也已证明，没有相应反射前提。
`ReducedProvability.matrix_of_verification` 用自然数反射补齐
原矩阵的 guard；`verification_reflection` 填入原检查器正文反射，
`ReducedProvability.introspection` 已给出无附加反射假设的 D3 普通推导。
归纳消费最终解释的纯公式，未假定内部自然数或轨迹在外部标准、有限或良基。

当前源码包含原理论及裸 ZFC 的 Löb、第二不完备定理，原支撑理论的 Tarski 实例，
以及保留源编码和最终纯公式自身编码的裸 ZFC 带参数 Tarski 实例。
`lake --wfail build` 完成 947 个任务。
`bash scripts/check-all.sh` 检查全部 950 个 Lean 模块，完成 952 个全源构建任务及
320 个扫描工具任务，零错误、零警告。
这些核验在恢复环境中实际运行；没有运行远端 CI。

最新 `#print axioms` 检查覆盖 530 个入口，包括 D1–D3、Löb、哥二、Rosser、原理论及纯语言表示的 Tarski 终点。
上一状态的 440 个入口依赖集合逐项不变；90 个新增核验入口覆盖通用语义外壳、表达式迭代、
最小输出、纯 AST 编解码、数码求值、自身编码图、固定点及纯 Tarski。
全部新增依赖均未超出保存的 Rosser 32 项可信基，没有新可信依赖或 `sorryAx`：

| 核验入口 | 依赖数量及比较 |
| --- | --- |
| `DerivabilityConditions_m.imp_m`、`iff_m` | 各 0 项 |
| `DerivabilityConditions_m.loeb_axiom_m`、`loeb_m` | 各 1 项，仅 `propext` |
| `ObjectLoeb.reflection_apply_m`、`fixed_point_m` | 分别为 2 项、3 项，仅既有 Lean 基础依赖 |
| `ReducedProvability.loeb_fixed_point_m` | 11 项，包含于既有 Rosser 可信基 |
| `ReducedProvability.derivability_m`、`loeb_axiom_m`、`loeb_m` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `DerivabilityConditions_m.second_incompleteness_internal_m`、`second_incompleteness_m` | 各 1 项，仅 `propext` |
| `ReducedProvability.second_incompleteness_internal_m`、`second_incompleteness_m` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `PureSentenceTransfer.translate_embed_m`、`derives_iff_m` | 各 31 项，均包含于既有 Rosser 可信基 |
| `PureProvability.checked_iff_m`、`source_canonical_m`、`source_roundtrip_m` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `PureProvability.necessitation_m`、`distribution_m`、`introspection_m`、`derivability_m` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `PureProvability.loeb_fixed_point_m`、`loeb_axiom_m`、`loeb_m` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `PureProvability.consistency_translation_m` | 11 项，包含于既有 Rosser 可信基 |
| `PureProvability.second_incompleteness_internal_m`、`second_incompleteness_m` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `Tarski.liar_refutes_m`、`biconditional_unprovable_m`、`not_truth_schema_m` | 各 1 项，仅 `propext` |
| `Tarski.not_defines_truth_m`、`ObjectTarski.liar_fixed_point_m` | 各 3 项，仅既有 Lean 基础依赖 |
| `ReducedTarski.liar_fixed_point_m`、`liar_refutes_m`、`biconditional_unprovable_m` | 各 10 项，均包含于既有 Rosser 可信基 |
| `ReducedTarski.undefinable_syntax_m`、`undefinable_semantics_m` | 各 10 项，均包含于既有 Rosser 可信基 |
| `ObjectNumeralSyntax.value_encode_m` | 0 项 |
| `ObjectParameterDiagonal.fixed_point_m`、`ObjectTarski.Parameters.liar_fixed_point_m` | 各 3 项，仅既有 Lean 基础依赖 |
| `Tarski.not_defines_satisfaction_m` | 3 项，仅既有 Lean 基础依赖 |
| `ReducedTarski.Parameters.liar_fixed_point_m`、`liar_refutes_closed_m`、`liar_fails_at_m` | 各 10 项，均包含于既有 Rosser 可信基 |
| `ReducedTarski.Parameters.undefinable_syntax_m`、`undefinable_at_m`、`undefinable_parameters_m` | 各 10 项，均包含于既有 Rosser 可信基 |
| `SemanticTransfer.derives_open_m`、`consistent_open_m` | 各 3 项，仅既有 Lean 基础依赖 |
| `PureOpenTransfer.embed_canonical_m`、`translate_embed_m`、`derives_iff_m` | 各 31 项，均包含于既有 Rosser 可信基 |
| `PureTarskiSource.predicate_satisfies_m`、`liar_fixed_point_m`、`liar_refutes_closed_m` | 各 31 项，均包含于既有 Rosser 可信基 |
| `PureTarskiSource.undefinable_syntax_m`、`undefinable_at_m`、`undefinable_parameters_m`、`undefinable_source_at_m` | 各 31 项，均包含于既有 Rosser 可信基 |
| `PureQuotation.self_code_m`、`code_injective_m`、`decode_tree_m` | 各 3 项，仅既有 Lean 基础依赖 |
| `PureDiagonalGraph.source_satisfies_m` | 10 项，均包含于既有 Rosser 可信基 |
| `PureQuotation.numeral_satisfies_m`、`PureDiagonalGraph.satisfies_m`、`PureFixedPoint.fixed_point_m` | 各 31 项，均包含于既有 Rosser 可信基 |
| `PureTarski.liar_fixed_point_m`、`liar_refutes_closed_m`、`undefinable_syntax_m`、`undefinable_parameters_m` | 各 31 项，均包含于既有 Rosser 可信基 |
| `ObjectCodeInstantiation.formula_values_congr` | 1 项，为既有 Rosser 32 项依赖的子集 |
| `PureSourceTraceComposition.witness_agrees`；`PureSourceNumeralSyntax.graph_transform` | 各 31 项，均包含于同一既有可信基 |
| `PureSourceInstantiation.formula_mapped_transform`、`numeral_point`、`numeral_wellFormed` | 各 31 项，均包含于同一既有可信基 |
| `InternalNumeralProof.forall_elimination`、`specialize_values`、`specialize_finite`、`specialize`、`values_modus_ponens` | 各 32 项，与此前 Rosser 依赖集合相同 |
| `InternalNumeralReflection.equal`、`successor_inequality`、`unequalAll_agrees`、`unequal`、`unequal_derives` | 各 32 项，与此前 Rosser 依赖集合相同 |
| `InternalNumeralReflection.natural`；`ReducedProvability.matrix_of_verification` | 重新核验后仍为同一组 32 项依赖；后者仍须提供检查器正文证明 |
| `ReducedProvability.distribution`、`PureRosser.independent` | 重新核验后仍为同一组 32 项依赖 |
| `PureSourceArithmetic.at_zero`、`at_successor`；`InternalNumeralReflection.source_complete` | 前两项各 31 项，开放完备性入口 10 项，均为既有可信基的子集 |
| `InternalNumeralReflection.orderAll_agrees`、`order`、`weak_order`、`order_derives` | 各 32 项，与此前 Rosser 依赖集合相同 |
| `InternalNumeralReflection.evaluationAll_agrees`、`evaluation_induction`、`evaluation_zero`、`evaluation_successor` | 各 32 项，与此前 Rosser 依赖集合相同 |
| `InternalNumeralReflection.addition_evaluation`、`multiplication_evaluation`、`exponentiation_evaluation`、`arithmetic_evaluation_derives` | 各 32 项，与此前 Rosser 依赖集合相同 |
| `ObjectCodeInstantiation.term_mapped`、`term_weakenFree`；`InternalNumeralReflection.composition_derives` | 分别为 0、1、10 项，均包含于既有可信基 |
| `InternalNumeralReflection.binary_term_evaluation`、`arithmetic_term_evaluation`；配对多项式求值、`pairing_evaluation`、`pairing_evaluation_derives` | 各 32 项，与此前 Rosser 依赖集合相同 |
| 字段列、节点、Horn 表达式、参数化项／参数列／公式、quotation 树与 `quotation_evaluation` | 八个入口各 32 项，与此前 Rosser 依赖集合相同 |
| `ObjectCodeInstantiation.term_weakenBound`、`formula_renamed`、`formula_weakenFree` | 分别为 1、2、2 项，均包含于既有可信基 |
| 原子同余、全称零点／后继／反例的源推导 | 四个入口各 10 项；内部原子反射、逻辑组合、量词见证及实际有界反射均为原 32 项依赖 |
| `bounded_bundle_parameters`、`bounded_bundle`、`bundleAt_agrees` | 各 32 项；`parameterValues_agrees` 为 31 项，均包含于既有可信基 |
| `finite_trace_derives`、`verificationMatrix_trace` | 分别为 9、11 项，均包含于既有可信基 |
| `allOf_values`、`natural_term_proof`、`finite_trace_values`、`checked_trace_values`、`finite_verification` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `term_embedBoundClosed`；`formula_mapped_of_depth`、`formula_substituteFree`、`binary_template` | 前者 1 项，其余各 2 项；自由重命名改为复用该遍历后，旧入口依赖集合不变 |
| 数码图 `template_apply`；`predicate_terms_code`、`predicate_names_code` | 各 2 项，均包含于既有可信基 |
| `predicate_transport_derives`；`predicate_transport`、`nextTerm_evaluation` | 分别为 10、32、32 项，均包含于既有可信基 |
| `numeral_trace_zero_derives`、`numeral_trace_step_derives`、`numeral_trace_reject_derives` | 各 31 项，均包含于既有可信基 |
| `numeral_trace_zero`、`numeral_trace_step`、`numeralTraceAt_agrees`、`numeral_trace_positive`、`numeral_trace_positive_derives`、`numeral_trace_negative`、`numeral_trace_reflection` | 七个入口各 32 项，与既有 Rosser 依赖集合相同 |
| Horn `template_apply`、`horn_satisfies`；`hornAt_satisfies`、`projectionGet_satisfies` | 前两项各 2 项，后两项各 11 项，均包含于既有可信基 |
| `rule_cases`、`node_head_injective`、`horn_rule_derives` | 各 31 项，均包含于既有可信基 |
| `horn_term_transfer`、`horn_rule_terms`、`horn_rule_values`、`hornProv_agrees` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `projectionGet_agrees`、`projection_get_step`、`projection_get_positive`、`projection_positive`、`projection_term_positive`、`projection_positive_derives` | 六个入口各 32 项，与既有 Rosser 依赖集合相同 |
| `ObjectSyntaxReflection.Row.map_tag`、`map_fields`、`map_input`；`PureSourceSyntaxRank.value_map` | 四个入口均为 0 项依赖 |
| `ObjectSyntaxReflection.Row.input_mem`、`PureSourceSyntaxRank.input_natural` | 各 1 项，均包含于既有可信基 |
| `ObjectSyntaxReflection.ranked`、`head_variables` | 各 2 项，纯规则形状及变量出现证明 |
| `PureSourceSyntaxRank.value_natural`、`map_natural` | 各 10 项，均包含于既有可信基 |
| `PureSourceInduction.strong_induction`；`PureSourceSyntaxRank.rank_unique`、`below_value`、`rule_ranked` | 四个入口各 31 项，均包含于既有可信基 |
| `syntaxAt_satisfies` | 11 项，实际同时归纳公式的语义接口 |
| `syntaxAt_agrees`、`syntax_step`、`syntax_at_positive`、`syntax_positive`、`syntax_term_positive`、`syntax_positive_derives` | 六个入口各 32 项，与既有 Rosser 依赖集合相同 |
| 分层规则 `transform_valid`、`iteration_valid`、`project_valid`；schema 三项 `*_valid` 和 packet `shapes` | 各 2 项，由内核核验原固定规则表 |
| `rule_intro_bounds`、`rule_cases_bounds`；`affine_bounds` | 分别为 10、31、31 项，均包含于既有可信基 |
| `rankedAt_satisfies`；`rankedAt_agrees`、`horn_ranked_positive`、`horn_valid_positive` | 语义接口为 11 项，其余各 32 项，均包含于既有可信基 |
| `transform_positive_derives`；`InternalPositiveFormula.boundedExists`、`positive_derives` | 各 32 项，与既有 Rosser 依赖集合相同 |
| `axiom_query_positive`、`axiom_query_named`、`axiom_query_positive_derives` | 各 32 项，实际一元公理行查询的内部与普通推导终点 |
| `InternalPositiveFormula.localMatrix`、`localRule`、`localTest` | 三个公共局部规则组合入口，各 32 项 |
| `InternalProofQueryReflection.logical`、`query`、`node`、`row`、`currentNode`、`currentRow` | 六个原局部查询反射入口，各 32 项 |
| `logical_term_positive`、`node_term_positive`、`row_term_positive`、`row_named_positive` 及三项 `*_positive_derives` | 七个复合项、数码及普通推导终点，各 32 项 |
| `checked_step_values`、`proof_step_values`、`finite_verification_of_links` | 三个实际步骤／矩阵装配入口，各 32 项；仍显式保留连边证明输入 |

| checked `template_apply`、`proof_valid`、`step_satisfies`、`checked_satisfies` | 四个入口各 2 项，由原公式语义及内核规则核验给出 |
| checked `rule_cases_bounds`、`checked_step_agrees` | 各 31 项，均包含于既有可信基 |
| checked `rule_intro_bounds`、`checked_rule_bounded_derives` | 各 10 项，内部集合构造及源规则推导 |
| `checkedAt_satisfies`、`checkedRankedAt_satisfies` | 各 11 项，原反射公式的语义接口 |
| `checked_term_transfer`、`checked_rule_bounded_terms`、`checked_rule_bounded_values`、`checkedProv_agrees`、`checkedRankedAt_agrees`、`checked_valid_positive` | 六个入口各 32 项，与既有 Rosser 依赖集合相同 |
| `proof_trace_positive`、`proof_trace_values`、`proofTrace`、`proof_trace_positive_derives` | 四个任意内部原证明树轨迹终点，各 32 项 |
| `verificationRoot_evaluation`、`verification_reflection`、`proof_matrix_reflection`、`ReducedProvability.introspection` | 四个原矩阵／D3 终点，各 32 项；无新增可信依赖 |


此前数码、节点装配、模式 2 变换与逻辑公理入口的审计也未超出上述可信基。
新增源码无 `sorry`、`admit`、自定义公理或原生验证调用；这里保留原有原生
支撑依赖，不声称整个仓库没有原生依赖。

数码的 `graph_term` 使用带 bound/free 参数的实际对象公式归纳，旧闭项接口
作为零上下文特例保留。自由代入和点实例化共用 `formula_mapped_transform` 的
AST 遍历；公式语法构造统一于 `PureSourceFormulaConstruction`，逻辑层复用它。
`InternalNumeralProof.exists_introduction` 只消费数码图和实例内部证明，自动填入
正文、项、实例语法及实际模式 2 变换。`codeProof_agreement` 还将最终阶段对应
推广到非标准结论码。新增 `ObjectNumeralReflection.atNumber` 由实际数码图、
参数化 AST 码项和原可证明性图组成，归纳前已证明其与最终规范扩张逐值一致。
自然数反射的后继步骤使用源无穷公理定理的内部特化及 MP，零测试的负分支
只反演数码图的根行。AST 的自然性、求值与模型传输复用关系保持遍历。
变换遍历现在允许两端都含内部数码，自由槽位相等只须覆盖实际上下文。
`graph_transform` 对任意内部深度证明数码不变，`specialize_values` 以同一全称
消去构造递归消费有限自由上下文；`specialize_finite` 不约束上下文外的槽位。
二元不等反射的归纳性质是 `ObjectNumeralComparison.unequalAll`，全称覆盖
第二个内部自然数和两个数码，零与后继分支均构造实际证明码。
序关系的归纳性质为 `ObjectNumeralOrder.atRight`，后继使用隶属后继的析取刻画。
算术的 `ObjectNumeralEvaluation.atRight` 同时量化两个操作数及运算结果的数码，
`evaluationAll_agrees` 先验证自然数封闭性与最终阶段对应，再用 `evaluation_induction`。
加法、乘法、幂依次提供实际后继证明；源递推由既有纯序数算术规格传回。
受限数码量词和联结词语义共用 `ObjectNumeralQuantifiers`／`InternalNumeralQuantifiers`，
避免展开整个验证器；所有数码实例仍交给原 `ProvableCode`。
复合项的 `binary_term_evaluation` 通过源同余推导组合子项等式与运算等式，
`term_mapped` 统一证明槽位代入与项码构造交换。配对的两分支消费序关系
正负反射和复合算术求值；节点、字段列及 Horn 表达式沿原编码构造组合，
参数化 AST 码项复用 `ObjectCodeInstantiation` 的既有关系保持遍历。
`quotation_evaluation` 直接覆盖原结构树。此处项骨架固定于元层，输入值、
数码与内部证明不要求外部标准；并未声称任意内部 AST 的统一解释器已完成。
D1、D2 与 Rosser 的公开结论保持；当前证明图、quotation、
公理和 Rosser 终点源码未改动。

`bounded_bundle` 的归纳性质是 `ObjectBoundedReflection.bundleAt`：内部区间上
所有数码实例的可证明性，蕴含有界全称实例的可证明性。性质只含实际数码图、
原证明图及固定 AST 码项；`bundleAt_agrees`、`parameterValues_agrees` 完成最终阶段对应，
没有把任意外部谓词当作可分离公式。反例方向及存在双重否定对偶保留原量词 AST。

`numeral_trace_positive` 的归纳性质是 `ObjectNumeralTraceReflection.atInput`，
包含原数码图、数码实例编码与原证明谓词。`numeralTraceAt_agrees` 完成最终阶段对应，
后继步从任意原内部轨迹反演前驱，并用 `numeral_trace_step` 构造下一图实例的证明。
`numeral_trace_negative` 使用已证明的总性与唯一性及不等式反射，不枚举拒绝轨迹。
`predicate_transport` 通过含量词模板同余和项求值，把两种反射传到复合项。
这些结论没有标准性、外部有限性或额外反射假设。

`projection_get_positive` 按内部索引归纳，性质为 `ObjectHornReflection.getAt`；
`projectionGet_agrees` 证明最终阶段对应。`rule_cases` 只读取原内部轨迹根行，
`horn_rule_values` 统一生成参数命名、守卫证明及前提／结论的数码传输。
`projection_positive` 据此覆盖原 `ObjectProjection.rules` 的全部七条规则，
`projection_term_positive` 接入复合行项，`projection_positive_derives` 给出源理论统一闭句。
不要求规范树／列表外壳，未假定内部索引或轨迹外部标准、有限或良基。
本入口只证明投影图正反射，不登记一般负反射。

`syntax_positive` 覆盖原 `ObjectFormulaSyntax.rules` 的任意内部根行。
[PureSourceSyntaxRank](../YesMetaZFC/Model/ZFC/Pure/PureSourceSyntaxRank.lean) 的 `rule_ranked` 从实际规则表证明子输入严格小于头输入；
`rank_unique` 用编码单射性恢复输入秩，量词下增长的 bound 长度不影响下降。
归纳正文为 `ObjectSyntaxReflection.atInput`，同时量化内部上下文和参数个数；
`syntaxAt_agrees` 证明最终阶段对应，`PureSourceInduction.strong_induction` 通过
较小输入的有界全称公式实现内部强归纳。规则装配复用 `horn_rule_values`。
`syntax_term_positive` 支持复合行项，`syntax_positive_derives` 给出统一闭句推导。
本入口证明一般语法图正反射，不登记一般负反射。

[InternalTransformReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalTransformReflection.lean) 用 `horn_valid_positive` 覆盖原 28 条变换规则。
查表先按表尾下降，再对语法输入下降；元层有限阶段与内部输入强归纳分开。
[InternalSchemaGraphs](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaGraphs.lean) 覆盖正文、重命名、表生成、闭合和 quotation 转换。
[InternalPacketReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPacketReflection.lean) 覆盖原传输包十条规则；token 的递归输入下降
由原 radix 128 仿射图的正尾增长界推出，不依赖外部数值解码。
原规则量化的隐含中间参数通过 `rule_cases_bounds`／`horn_rule_bounded_values`
保留实际边界，未加入“所有变量必须出现在头部”的额外条件。

[InternalSchemaReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaReflection.lean) 将上述图和固定表组合为原 schema 的完整有界查询。
[InternalPositiveQuantifiers](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPositiveQuantifiers.lean) 只用正向见证引入，复用规范 binder 打开与替换，
不假设各图具有负反射。[InternalSchemaQueries](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaQueries.lean) 的 `axiom_query_positive`
支持已求值复合项，`axiom_query_positive_derives` 是实际 `ReducedAxiomNumber.localTest`
成立时数码实例可证明性的普通闭句推导。输入、见证、数码及原集合轨迹都允许非标准。

[InternalLocalDecisionReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalLocalDecisionReflection.lean) 对任意原局部规则表统一处理头等式、全部子查询
与有界存在块；没有逐条复制 27 类逻辑公理的证明。
[InternalProofQueries](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofQueries.lean) 消费已完成的一般语法、变换、投影及实际公理查询，
得到六类节点及原零码／零标签／其他标签行封装的正反射。
[InternalProofRowReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofRowReflection.lean) 将其导出为复合项、任意内部数码及统一普通推导入口。
[InternalCheckedStepReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedStepReflection.lean) 的 `proof_step_values` 消去实际检查步骤中的
局部证明输入，只保留原 Horn 连边证明和局部真值；轨迹项不要求是自然数。
`finite_verification_of_links` 把同一装配接回原 `verificationMatrix`，仍显式要求有限骨架及连边证明。

[PureSourceCheckedConstruction](../YesMetaZFC/Model/ZFC/Pure/PureSourceCheckedConstruction.lean) 在根行反演时同时取得原 Horn 规则、参数界、守卫、局部真值及前提见证。
各前提保留同一原内部集合轨迹；构造时用公共集合 `collect` / `insert` 合并并插入头行。
[InternalCheckedReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedReflection.lean) 将实际局部查询正反射与前提数码证明组合，得到原规则结论的数码证明。

[InternalCheckedRanking](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedRanking.lean) 的 `checked_valid_positive` 对实际
`ObjectCheckedReflection.atPhase` 公式作内部强归纳，`checkedRankedAt_agrees` 核验最终阶段对应。
[ObjectCheckedReflection](../YesMetaZFC/Automation/ObjectCheckedReflection.lean) 的 `proof_valid` 以 Lean 内核核验原十二条规则：
节点阶段沿子证明编码下降，根阶段进入节点阶段。[InternalProofTraceReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofTraceReflection.lean)
的 `proof_trace_positive` 已填入原行查询正反射和对应合同，覆盖任意内部根行与轨迹。

[InternalVerificationReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalVerificationReflection.lean) 的 `verification_reflection` 通过
`verificationMatrix_trace` 精确接回原检查器正文，`proof_matrix_reflection` 补齐自然数 guard。
`proofMatrix_exists` 保持原普通可证明性句子；[ReducedIntrospection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedIntrospection.lean) 的
`ReducedProvability.introspection` 因而给出 $T\vdash\Box\varphi\to\Box\Box\varphi$。
这些入口不要求外部有限骨架、逐条连边证明、额外反射、一致性或标准模型假设。

[Loeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Loeb.lean) 将 D1–D3
封装为 `DerivabilityConditions_m`。给定固定点 $\psi\leftrightarrow(\Box\psi\to\varphi)$，
先由 D2、D3 得到 $\Box\psi\to\Box\varphi$，再推出
$(\Box\varphi\to\varphi)\to\psi$；D1、D2 提升后一推导，给出内部 Löb 公式。
[ReducedLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedLoeb.lean)
实际构造 `loebSentence_m` 并证明 `loeb_fixed_point_m`，因此 `loeb_axiom_m` 无额外固定点或
反射前提；`loeb_m` 将 $T\vdash\Box\varphi\to\varphi$ 转为 $T\vdash\varphi$。
这里 $T$ 与 $\Box$ 仍是原 `intrinsic_zfc_theory` 与 `ReducedProvability.provable`。

[ReducedSecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedSecondIncompleteness.lean)
复用 $\varphi=\bot$ 的固定点，保持已有 $\mathrm{Con}(T)=\neg\Box\bot$。
`second_incompleteness_internal_m` 证明 $T\vdash\mathrm{Con}(T)\to\neg\Box\mathrm{Con}(T)$；
`second_incompleteness_m` 只假定 `Derives.Consistent T []`，便排除 $T\vdash\mathrm{Con}(T)$。
通用证明见 [SecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SecondIncompleteness.lean)：
若有一致性句子的推导，否定消去将它转成 $\Box\bot\to\bot$，Löb 规则随即推出矛盾。

## 裸 ZFC 的语言、可证明性与固定点传输

令 $Z=\texttt{PureModel.theory}$，$e=\texttt{PureSentenceTransfer.embed_m}$，
$\tau=\texttt{PureRosser.translate}$。[PureSentenceTransfer](../YesMetaZFC/Model/ZFC/Pure/PureSentenceTransfer.lean)
使用模型扩张后的约化等于原纯模型，证明 $Z\vdash\tau(e(\varphi))\leftrightarrow\varphi$；
结合原模型约化和强完备性，得到 $T\vdash e(\varphi)\iff Z\vdash\varphi$。
对于任意源句子 $\psi$，$T\vdash\psi\leftrightarrow e(\tau(\psi))$ 仍需其任意模型对应。

[PureProvability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureProvability.lean)
定义 $\Box_Z\varphi=\tau(\Box_T e(\varphi))$。`checked_iff_m` 证明原检查器接受某个
$e(\varphi)$ 的证书当且仅当 $Z\vdash\varphi$，因此这个纯算子确实表示裸 ZFC 的推导。
`source_canonical_m` 使用已完成的全部内部证明码对应和 quotation 对应，
使 $\Box_T\psi$ 在任意原模型及其规范重扩张中同真。
D1、D2 直接经嵌入和翻译传输；D3 还用
$T\vdash\Box_T e(\varphi)\leftrightarrow e(\Box_Z\varphi)$ 的正向推导提升可证明性，
接上原 D3，得到 $Z\vdash\Box_Z\varphi\to\Box_Z\Box_Z\varphi$。

[PureLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLoeb.lean)
从原固定点 $\psi\leftrightarrow(\Box_T\psi\to e(\varphi))$ 出发，
通过右侧的实际对应证明 $\psi$ 的任意模型对应；再把
$\psi\leftrightarrow e(\tau(\psi))$ 提升到可证明性层，得到
$Z\vdash\tau(\psi)\leftrightarrow(\Box_Z\tau(\psi)\to\varphi)$。
`loeb_axiom_m` 和 `loeb_m` 因而使用纯算子的实际固定点，未留下固定点或反射假设。

[PureSecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSecondIncompleteness.lean)
令 $\mathrm{Con}_Z=\neg\Box_Z\bot$，证明内部公式
$Z\vdash\mathrm{Con}_Z\to\neg\Box_Z\mathrm{Con}_Z$；只由裸 ZFC 一致便推出
$Z\nvdash\mathrm{Con}_Z$。`consistency_translation_m` 还确认 $\mathrm{Con}_Z=\tau(\mathrm{Con}_T)$。
这些是纯隶属语言、原始 ZFC 公理下的普通 `Derives` 结论。
编码仍是嵌入句子的原 quotation 与检查器；另选直接编码纯 ZFC 证明树的谓词，
及其与当前算子的内部等价，不属于此处已证内容。

## 原支撑理论的真不可定义性

[Tarski](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Tarski.lean)
将候选闭句算子 $F$ 的两种合同分开：`TruthSchema_m T F` 要求所有
$T\vdash F(\varphi)\leftrightarrow\varphi$；`DefinesTruth_m ℳ F` 要求所有
$\mathcal M\models F(\varphi)\leftrightarrow\varphi$。
`liar_refutes_m` 仅从 $T\vdash L\leftrightarrow\neg F(L)$ 推出
$T\vdash\neg(F(L)\leftrightarrow L)$，其逻辑核心还允许开放公式和任意局部上下文。
一致性排除相应等价式的推导，可靠性排除模型中的全部真值对应。

[ObjectTarskiFixedPoint](../YesMetaZFC/Automation/ObjectTarskiFixedPoint.lean)
对任意 `FormulaTemplate.Unary` 的正文取否定，调用原 `ObjectDiagonal.fixedPoint_spec`。
[ReducedTarski](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedTarski.lean)
以 `ReducedRosser.diagonalSupport` 实例化，令
$F(\varphi)=P(\texttt{IntrinsicQuotation.quote}\ \varphi)$，并实际生成 `liarSentence_m P`。
`liar_fixed_point_m` 与 `liar_refutes_m` 没有额外固定点、一致性或反射前提。
`undefinable_syntax_m` 只假定 `Derives.Consistent intrinsic_zfc_theory []`，排除所有候选一元公式；
`undefinable_semantics_m` 对任意载体宇宙的 $\mathcal M\models\texttt{intrinsic_zfc_theory}$ 成立。

候选只有编码变量这一自由槽位，不携带任意模型参数；真值合同量化宿主 `SetSentence`，
不把非标准内部语法当作宿主有限语法，也不要求模型的内部自然数标准。
既有 `TarskiTruth` 是集合结构满足关系的对象定义规格，不是此全局真谓词。
最终纯公式自身编码的对角化由下述 `PureFixedPoint` 独立完成；
原 `PureLoeb` 的特定算子固定点仍保留其既有编码合同。

### 参数上下文与逐赋值反例

[ObjectParameterDiagonal](../YesMetaZFC/Automation/ObjectParameterDiagonal.lean)
对任意有限 `parameters : SetContext` 和 $P(x,\bar z)$ 实际生成固定点，
将原同时自由代入图的表尾推广为参数变量的恒等替换。对象输出唯一性复用既有最小见证论证。
[ReducedTarskiParameters](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedTarskiParameters.lean)
在同一支撑理论上证明
$T\vdash L_P(\bar z)\leftrightarrow\neg P(\ulcorner L_P\urcorner,\bar z)$，并全称闭合其反驳式。
`undefinable_syntax_m` 只假定原理论在闭上下文中的一致性；开放上下文一致性由闭项代入推出。
`liar_fails_at_m` 与 `undefinable_at_m` 对每个任意模型赋值 `env` 成立；
`undefinable_parameters_m` 同时排除参数上下文、赋值及候选公式的存在。

这里 `DefinesSatisfaction_m env` 要求相同自由上下文中的全部宿主开放公式同真。
任意参数取值不需要能被闭项命名，也不要求模型标准；quotation 只编码实际公式语法。
只定义无参数闭句真值的带参数谓词不满足这个合同的全部要求，不能据此宣称已排除它。
原闭固定点的空参数构造与修改前 AST 已通过通用定义等式核验；原 quotation 随之保持。

### 保留源编码的裸 ZFC 终点

[PureOpenTransfer](../YesMetaZFC/Model/ZFC/Pure/PureOpenTransfer.lean)
将纯候选按同一参数槽嵌入原语言，证明规范扩张中的逐环境真值往返及开放公式双向推导。
纯签名没有闭项，故开放上下文的一致性通过既有模型存在性与模型非空性取得。
[PureTarskiSource](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTarskiSource.lean)
对任意纯候选 $P(x,\bar z)$ 构造源反例 $S_P$ 和纯反例 $L_P=\tau(S_P)$。
`liar_fixed_point_m`、`liar_refutes_closed_m` 的实际推导理论是裸 `PureModel.theory`；
`undefinable_syntax_m` 只假定该裸理论在闭上下文中的一致性。

`predicate_satisfies_m` 证明消元后的候选实例在任意裸模型和任意参数环境中，恰好是原纯
$P$ 在源 quotation 值处的应用。`undefinable_source_at_m` 直接排除
$P(\ulcorner\varphi\urcorner,\bar a)\leftrightarrow\varphi^{\mathcal M^+}(\bar a)$
对全部源开放公式成立；$\mathcal M^+$ 是现有规范扩张。参数个数和取值任意，模型无需标准。
`undefinable_parameters_m` 对所有这些参数上下文和赋值统一排除纯翻译的真值合同。

这里保留原自代入图及原 quotation，没有加入消元编码图或纯语法专用 quotation。
固定点使用的是 $\ulcorner S_P\urcorner$，不是 $\ulcorner\tau(S_P)\urcorner$；
不能把这个已证合同直接换成仅量化纯公式并使用纯公式自身编码的合同。
也没有由规范扩张的正确性推断任意原模型对全部源公式的约化往返。

### 最终纯公式自身编码的裸 ZFC 终点

[PureQuotationFaithful](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureQuotationFaithful.lean) 给出纯 AST 数值编码的单射性，
并证明结构嵌入与现有完整 AST 编解码器的逐节点对应。纯数码公式 $N_n(x)$
在任意裸模型中唯一定义规范扩张内相应的有限数码值；不对内部自然数作标准性假设。

[PureDiagonalGraph](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureDiagonalGraph.lean) 的实际纯图在标准输入 $n$ 处，
对任意对象输出 $a$ 恰好等价于 $a=d(n)$。递推只用两条固定 Horn 规则；
最小见证论证消费标准正负实例，从而排除任意内部伪轨迹产生的错误输出。
`self_code_m` 是最终 $\exists x(N_n(x)\land B)$ 的 AST 编码等式，
[PureFixedPoint](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFixedPoint.lean) 的 `fixed_point_m` 据此在普通裸 ZFC 推导中成立。

[PureTarski](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTarski.lean) 中候选、反例及合同量化的公式全是纯公式，
`quotation_m hℳ φ` 命名 $\varphi$ 自身的完整 AST 码。
`liar_fixed_point_m` 与全称闭合反驳式没有一致性前提；句法不可定义性只假定裸 ZFC 一致。
`undefinable_parameters_m` 对任意裸模型和每组任意有限参数成立，参数无需闭项名称。
合同包含使用这些参数的所有宿主开放公式；不将它改称只判定无参数闭句的带参数合同，
也不声称已构造非标准内部语法的满足关系。

## D1、D2 增量核验

在 `9045935` 基础上新增普通可证明性与内部 MP 构造，入口为
[ReducedDerivability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedDerivability.lean)。
`lake --wfail build` 完成 820 个任务；`bash scripts/check-all.sh` 检查全部
823 个 Lean 模块，完成 825 个全源构建任务及 320 个扫描工具任务，零错误、零警告。
这是恢复环境中的增量内核构建，不声称冷构建或远端 CI 已运行。

新增源码没有 `sorry`、`admit`、自定义公理或原生计算验证调用。
实际 `#print axioms` 核验显示：通用 D1 依赖 `propext`、`Quot.sound`；
源理论 D1 的 11 项依赖是既有 Rosser 终点依赖的子集；D2 和内部 MP 构造的
32 项依赖集合均与 `PureRosser.independent` 相同。这里保留仓库已有的原生
支撑依赖，不把“无新增依赖”表述为“没有原生依赖”。
原有证明图、quotation、公理和 Rosser 终点的源码均未修改。

## Rosser 与既有声明的核验基点

源码基点为 [4ae86c1](https://github.com/lanxinge/YesMetaZFC/commit/4ae86c1b38c756e95d3dee7e8de50a9c60db292b)。
该源码的全源检查完成 808 个构建任务、扫描工具检查完成 320 个任务，零错误、零警告。

公开声明审计保留全部 13,662 项基线声明；13,658 项原始编译类型相同，4 项仅有
相互递归生成的 binder 显示名差别。6,955 项数据定义中，6,953 项原始表达式相同；
`HilbertBaseAxiom.lower` 另经 Lean 证明任意输入的完整返回证书与旧实现相等，
`FirstOrderDerives.try_close` 是已实施的自动化改进。

60 项辅助声明因公共接口复用增加对既有 `propext`、`Quot.sound`、`Classical.choice`
的部分引用；审计范围内全仓公理并集未增加，Rosser 两个终点的类型和完整依赖集合
保持，没有新增对象公理、Lean 公理常量、原生验证依赖或 `sorryAx`。
最终审计覆盖 13,893 项，包括新增及补充纳入项；不把新增覆盖项冒充旧基线。

日常入口：`lake --wfail build`、`bash scripts/check-all.sh`。
本次文档整理沿用该源码核验结果，不声称重新构建或远端 CI 通过。
独立数学待办仍是原递归序列族之并在合法递归器下的 ω 全域性，见
[ELIMINATION.md](ELIMINATION.md)。
