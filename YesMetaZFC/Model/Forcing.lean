import YesMetaZFC.Model.Forcing.Order.Separative
import YesMetaZFC.Model.Forcing.Boolean.Conditions
import YesMetaZFC.Model.Forcing.Order.Tree
import YesMetaZFC.Model.Forcing.Applications.Cohen.Theory
import YesMetaZFC.Model.Forcing.Applications.Cohen.Internal
import YesMetaZFC.Model.Forcing.Internal.Check.Model
import YesMetaZFC.Model.Forcing.Internal.Check.Realization
import YesMetaZFC.Model.Forcing.Internal.Atomic.Truth
import YesMetaZFC.Model.Forcing.Internal.Extension.Choice
import YesMetaZFC.Model.Forcing.Internal.Extension.Instance
import YesMetaZFC.Model.Forcing.Applications.Continuum.CH
import YesMetaZFC.Model.Forcing.Applications.Collapse.Closed
import YesMetaZFC.Model.Forcing.Applications.Collapse.Iteration
import YesMetaZFC.Model.Forcing.Applications.Continuum.Independence
import YesMetaZFC.Model.Forcing.Applications.Cohen.TwoStep
import YesMetaZFC.Model.Forcing.Internal.Maximum.Basic
import YesMetaZFC.Model.Forcing.Internal.Reflection.Countermodel
import YesMetaZFC.Model.Forcing.Stage.Composition
import YesMetaZFC.Model.Forcing.Stage.Names
import YesMetaZFC.Model.Forcing.Stage.Extension
import YesMetaZFC.Model.Forcing.TwoStep.Names.Interpretation
import YesMetaZFC.Model.Forcing.Internal.Names.PairForcing
import YesMetaZFC.Model.Forcing.TwoStep.Names.Forcing
import YesMetaZFC.Model.Forcing.TwoStep.Names.Valuation
import YesMetaZFC.Model.Forcing.TwoStep.Atomic.Witness
import YesMetaZFC.Model.Forcing.TwoStep.Names.Isomorphism
import YesMetaZFC.Model.Forcing.Applications.Cohen.Proper
import YesMetaZFC.Model.Forcing.Iteration.Fusion.Restriction
import YesMetaZFC.Model.Forcing.Iteration.Names.Witness
import YesMetaZFC.Model.Forcing.Proper.Generic.WitnessHull
import YesMetaZFC.Model.Forcing.Proper.Generic.ElementaryHull
import YesMetaZFC.Model.Forcing.Proper.Generic.Successor
import YesMetaZFC.Model.Forcing.TwoStep.Proper.Extension
import YesMetaZFC.Model.Forcing.TwoStep.Proper.Decomposition
import YesMetaZFC.Model.Forcing.Proper.Family.Basic
import YesMetaZFC.Model.Forcing.Iteration.Proper.SuccessorGeneric
import YesMetaZFC.Model.Forcing.Iteration.Names.Bounded
import YesMetaZFC.Model.Forcing.Iteration.Names.QuotientTransfer
import YesMetaZFC.Model.Forcing.Iteration.Proper.Model.Sequence
import YesMetaZFC.Model.Forcing.Iteration.Proper.Dense
import YesMetaZFC.Model.Forcing.Iteration.Proper.Model.Rule
import YesMetaZFC.Model.Forcing.Iteration.Proper.Prefix.Step
import YesMetaZFC.Model.Forcing.Iteration.Proper.Omega
import YesMetaZFC.Model.Forcing.Applications.Cohen.CountableSupport
import YesMetaZFC.Model.Forcing.Iteration.Proper.Prefix.Limit
import YesMetaZFC.Model.Forcing.Iteration.Names.DenseName
import YesMetaZFC.Model.Forcing.Proper.Generic.Ground

/-! # 力迫偏序、名称求值与相对扩张入口

预序、相容性、稠密映射、分离商、正则开完备化及其规范条件映射，
布尔名称的图求值、完整一阶真值、可数族泛型滤子及相对名称域的实际解释扩张。
Cohen 实例同时满足全部公式真值、指定稠密要求和旧实数规避要求。
内部名称泛型商的完整原公式真值和原 ZFC 全部公理及模式由实际内部构造证明，
适用于外部非良基、内部 ω 非标准的任意地模型；商载体保持地模型的 universe。
preserves_zfc_l 一次取得全部保持性，two_extension_zfc_l 给出可直接调用的实际实例。
ch_extension_l 自动构造可数地模型的 CH 塌缩扩张；ch_model_l 给出实际 ZFC＋CH 模型存在。
cohen_extension_l 以地模型指标集 κ 参数化添加量，自动构造互异新实数族并保持旧无限基数。
not_ch_extension_l 自动添加 ω₂ 个 Cohen 实数；ch_independent_l 在原 Derives 核中给出 CH 双侧不可证。
two_step_l 构造任意名称预序的二步条件集；two_step_factors_l 与 two_step_compose_l 完成泛型双向分解。
maximum_l 为原公式构造规范的统一见证名称；forces_zf_l、forces_zfc_l 分别给出全部原 ZF、ZFC 公理证书。
cohen_step_l 从任意添加量名称全局装配实际 Cohen 后继，迭代的极限阶段见 `Forcing/ITERATION.md`。
two_step_embed_l 构造带顶名称的阶段完全嵌入；reg_embed_max_l 与 reg_embed_comp_l 给出极大反链保持和内部复合。
stage_nmap_l 自动构造目标名称；stage_nmap_comp_l 与 stage_nmap_id_l 核验复合及恒等阶段的一致性。
reg_generic_l 自动回拉阶段泛型；stage_extension_l 给出名称解释相容的成员满覆盖单射。
two_step_name_l 统一转换二步名称，并核验其在每个第一泛型扩张中的第二阶段名称性。
curry_forces_name_l 在原 ZF 下给出该第二阶段名称性的全局力迫证书。
two_step_valuation_l 装配原二步名称的双重求值，并核验组合滤子下的精确成员递归。
forces_order_l 核验关系规范化不改变全部名称力迫；two_step_eq_pick_l 保留匹配见证的首阶段泛型坐标。
curry_forces_eq_iff_l 核验二步等号与嵌套等号精确对应；two_step_iso_l 通过名称摊平装配单次二步扩张与双重扩张的同构。
row_zero_l 与 row_successor_l 构造共同坐标格式的零阶段及名称后继，保持原样阶段嵌入、前缀和两类支撑；
row_cohen_successor_l 实现添加量名称参数化的实际 Cohen 坐标后继。
cohen_names_l 与 cohen_names_unique_l 给出完整规范名称三元组的存在与字面唯一性；
Row_cohen_d、row_cohen_m 及 row_cohen_unique_l 进一步唯一确定整个 Cohen 后继偏序。
row_system_zero_l、row_system_successor_l 构造模型内阶段序列的零系统与名称后继；
row_iteration_l 按实际原公式后继规则构造任意内部序数长度的整个支撑迭代；
row_iteration_unique_l 与 row_iteration_step_l 核验唯一性和精确前缀方程，cohen_iteration_l 提供实际一键实例。
row_limit_l 构造有限／可数支撑极限及全部阶段完全嵌入，row_system_limit_l 将极限写回序列。
row_limit_union_l 给出有限支撑极限条件与序的直接并刻画；two_step_ccc_l 保存任意名称后继的 CCC。
row_iteration_ccc_exists_l 一次装配有限支撑迭代及全部阶段 CCC，cohen_iteration_ccc_l 是实际参数化实例。
ccc_proper_l 构造内部主条件 club，proper_mstr_l 自动取得含指定可数种子的主条件；
cohen_names_proper_l 给出参数化 Cohen 后继的全局 properness 力迫证书。
ng_set_l 构造内部集合 N 的真实泛型像，ng_surjection_l 给出扩张内部的求值满射图；
ng_countable_l 在 ZF 下保持其内部可数性。ng_witness_hull_l 从 properness 自动构造内部
可数初等 N 和指定条件的 N 主加强；通用 Lévy 反射保证指定原公式的所有 N 名称参数
共用此 N，泛型接受后将其存在见证提升到 N[G]。
ng_elementary_hull_l 从 properness 及可数种子一次构造传递 X、内部初等 N 及主加强；
同一个 N 在每个接受主加强的泛型中满足全部内部公式码与赋值下的 N[G]≺X[G]。
X[G] 传递而 N[G] 内部可数，非标准有限参数列与公式码均已证明精确回拉。
ng_hchi_hull_l 自动选择不可数正则 χ，并将上述提升的环境精确识别为扩张中的 H(eχ)；
h_generic_l 由内部小名称定理给出 H(χ) 的双向泛型对应。
pr_base_master_l 从实际 proper club 见证在固定的内部初等 N 中选择主加强；
ng_next_master_l 自动构造同一个 N、地阶段主条件及各泛型中的 N[G] 后继主条件选择。
two_step_master_l 合成首阶段主条件与被迫的 N[G] 主条件；two_step_master_first_l 证明首阶段投影，
two_step_master_second_l 证明反向第二坐标主性；two_step_master_decompose_l 自动给出规范名称及完整双向等价。
two_step_master_extension_l 在任意地模型中自动构造包含给定可数种子的实际二步主加强。
ng_family_hull_l 从实际阶段函数图一次选取 H(χ) 与同一个 N，支持其所有成员阶段的全内部初等提升。
ng_family_forcing_l 将共同提升装配为内部原公式 Hlift_d；ng_family_ground_l 同时构造 N 内的统一规范名称图。
ng_ground_trace_l 精确回拉 N[G] 中的旧条件；row_step_proper_l 对 N 内旧条件构造精确保留主前缀的后继主加强。
row_fusion_l 构造可数共尾前缀族的唯一融合，row_fusion_reconstruct_l 从实际条件自动生成前缀并还原。
row_iteration_pr_l 以原公式内部超限归纳完成同一个 N 上的全部区间迭代引理；
row_iteration_pr_exists_l 自动构造指定内部长度的迭代，cohen_iteration_pil_l 给出任意添加量的实际实例。
row_iteration_proper_l 由共同闭包的实际交集 club 完成全部阶段的 properness 保持；
row_iteration_proper_exists_l 自动构造整个 proper 迭代，cohen_iteration_proper_l 同时参数化添加量和内部长度。
proper_countable_reflect_l 反射全部旧集合的可数性，proper_omega_one_l 保持第一不可数序数；
row_iteration_preserves_l 和 cohen_iteration_preserves_l 一次装配各阶段的 ZFC、内部 ω、ω₁ 及旧可数性保持。
同一装配还返回 proper_set_cover_l 的覆盖结论：每个旧集合的新内部可数子集都有实际旧可数覆盖。
proper_cf_omega_l 精确保留共尾度为 ω 的旧序数；proper_countable_bounded_l 为旧共尾度大于 ω
的序数返回新可数子集的严格旧界。两项均已接入上述全部阶段的保持装配。
row_cl_induction_l 完成任意内部长度的可数支撑闭区间归纳，row_iteration_closed_l 给出全部阶段闭性；
collapse_iteration_preserves_l 从两个集合参数和内部长度自动构造塌缩迭代，返回各阶段 ZFC、
实数、任意旧目标上的内部 ω 函数及旧集合可数子集的实际旧原像，包含旧可数性。
closed_proper_l 从预序和内部可数闭性实际构造 proper club；闭扩张的同一嵌入因而
同时保留 ω₁、旧可数性与 ω 共尾性。collapse_rule_pr_l 取得真实后继 proper 证书，
collapse_iteration_pil_l 为任意可数种子返回闭塌缩迭代的共同 N 及完整 proper 区间引理。
名称后继使用最小支撑乘积的幂集作为混合闭库；row_next_unique_l、row_limit_unique_l 保证后继和极限的构造对象唯一，
row_next_m、row_limit_m 给出可供内部递归消费的原公式。
name_pool_represent_l 在 ZF 下取得同条件的库内等值代表，name_pool_maximum_l 在 ZFC 下选择有界见证；
row_next_witness_l 精确保留指定前缀，row_next_lower_name_l 把第二坐标加强名称提升为实际后继加强。
norm_name_exists_l 通过内部累积层级与最早层候选集构造名称的唯一规范代表；
全局被迫相等的输入得到字面相同的规范名称，最大值原理及全部 Cohen 名称入口已经迁移。
unique_maximum_l 在原 ZF 内把被迫存在且唯一的见证装配为唯一规范名称；
Cohen 名称与两个坐标系统入口已降低到 ZF，含 CCC 的完整 Cohen 结果仍使用 ZFC。
内部名称的一阶定义、支撑收集、小图解码、编码往返及 Cohen 内部实例见 Internal 各模块。
内部规范名称递归由 zf_check_l 一次取得；解释还原由 zf_check_val_l 给出。
文献选择、顺序方向、调用方式和尚未实现的语义范围见 `Forcing/README.md`。
-/
