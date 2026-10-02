# 形式化成果奖杯表

本表登记当前源码中的结论；构造和证明细节通过基础设施指南定位。

## 裸 ZFC 成果总览

以下入口均已有实际证明。`ZFC` 指 `PureModel.theory`，推导使用普通 `Derives`；
可证明性算子沿用原检查器的纯语言表示，自身编码固定点直接编码最终纯公式。

| 成果 | 最终入口 | 前提与范围 |
| --- | --- | --- |
| 原生小图 ZFC 模型与一致性 | [SmallGraph/ZFC](../YesMetaZFC/Model/SmallGraph/ZFC.lean)：`sg_models_zfc`、`zfc_consistent` | Lean 元层直接构造良基小图双模拟商；验证原 ZFC 全部公理与模式，无模型存在或一致性前提 |
| 任意地模型的内部泛型商 | [Forcing/InternalChoice](../YesMetaZFC/Model/Forcing/Internal/Extension/Choice.lean)：`preserves_zfc_l`；[InternalTruth](../YesMetaZFC/Model/Forcing/Internal/Forcing/Truth.lean)：`forcing_truth_l` | 允许外部非良基与非标准 ω；内部双模拟、商上的隶属、基础公理及原 ZFC 全部模式均已证明；不要求外部小图呈现 |
| ZFC＋CH 力迫模型 | [Forcing/CH](../YesMetaZFC/Model/Forcing/Applications/Continuum/CH.lean)：`ch_forcing_l`、`ch_extension_l`、`ch_model_l` | 任意地模型的可数闭塌缩保持 CH；对可数地模型自动取得泛型，允许外部非良基。小图模型的可数初等子模型给出无额外模型存在前提的实际实例 |
| 参数化 Cohen 添加与 ¬CH 模型 | [Forcing/CohenAdd](../YesMetaZFC/Model/Forcing/Applications/Cohen/Add.lean)：`cohen_extension_l`；[NotCH](../YesMetaZFC/Model/Forcing/Applications/Continuum/NotCH.lean)：`not_ch_extension_l`、`not_ch_model_l` | 任意模型内添加量 κ，自动产生互异新实数族并保持旧无限基数；默认 ω₂ 实例满足原 ZFC＋¬CH，允许外部非良基地模型 |
| 原 ZFC 的 CH 独立性 | [Forcing/CHIndependence](../YesMetaZFC/Model/Forcing/Applications/Continuum/Independence.lean)：`ch_independent_l`、`ch_consistency_l`、`ch_extensions_l` | 原 Project／纯隶属 Derives 核中的双侧不可证及两侧理论一致性；实际两侧模型已构造，独立性端点无额外模型存在或一致性前提 |
| 内部混合、最大值与全局公理力迫 | [Forcing/InternalMaximum](../YesMetaZFC/Model/Forcing/Internal/Maximum/Basic.lean)：`maximum_l`；[InternalCountermodel](../YesMetaZFC/Model/Forcing/Internal/Reflection/Countermodel.lean)：`forces_zf_l`、`forces_zfc_l` | 任意外部非良基地模型；单一名称实现全部正条件上的存在力迫；ZF 与 ZFC 的原公理和模式分别在自身理论强度下全局被迫使 |
| 二步泛型与阶段完全嵌入 | [Forcing/TwoStepComposition](../YesMetaZFC/Model/Forcing/TwoStep/Generic/Composition.lean)：`two_step_compose_l`；[TwoStepEmbedding](../YesMetaZFC/Model/Forcing/TwoStep/Embedding.lean)：`two_step_embed_l` | 两阶段泛型双向分解与精确恢复；顶名称给出实际阶段嵌入图，并已证明极大反链保持、恒等嵌入和复合；名称解释同构与支撑极限由以下独立入口提供 |
| 全局参数化 Cohen 后继 | [Forcing/CohenIteration](../YesMetaZFC/Model/Forcing/Applications/Cohen/TwoStep.lean)：`cohen_step_l` | 任意添加量名称，一次装配全局条件集、关系、顶名称和阶段嵌入；每个泛型解释具备 CCC、基数保持及指定量新实数族 |
| 阶段名称搬运与复合 | [Forcing/StageNames](../YesMetaZFC/Model/Forcing/Stage/Names.lean)：`stage_nmap_l`、`stage_nmap_comp_l`、`stage_nmap_id_l` | 原 ZF 内实际递归图的存在、唯一性及严格复合；恒等图删除零标签后仍保持等号力迫 |
| 阶段原子力迫与泛型扩张嵌入 | [Forcing/StageAtomic](../YesMetaZFC/Model/Forcing/Stage/Atomic/Basic.lean)：`nmap_eq_l`、`nmap_mem_force_l`；[StageExtension](../YesMetaZFC/Model/Forcing/Stage/Extension.lean)：`stage_extension_l` | 完全嵌入保持并反射等号、隶属及其否定；自动回拉泛型，构造解释相容的成员满覆盖单射，不假定阶段像稠密或模型外部良基 |
| 二步名称的内部递归转换 | [Forcing/TwoStepNameInterpretation](../YesMetaZFC/Model/Forcing/TwoStep/Names/Interpretation.lean)：`two_step_name_l`、`curry_val_entry_l` | 原 ZF 内实际递归图的存在唯一性；同一转换在每个第一泛型扩张内成为第二阶段名称，并满足精确条目方程 |
| 双重求值与关系规范化 | [Forcing/TwoStepValuation](../YesMetaZFC/Model/Forcing/TwoStep/Names/Valuation.lean)：`two_step_valuation_l`；[InternalOrderCongruence](../YesMetaZFC/Model/Forcing/Internal/Forcing/OrderCongruence.lean)：`forces_order_l` | 原二步名称的双重求值总且唯一，成员递归精确使用组合滤子；第二阶段关系删除域外条目不改变任何名称公式的力迫 |
| 单次二步扩张与双重扩张同构 | [Forcing/TwoStepIsomorphism](../YesMetaZFC/Model/Forcing/TwoStep/Names/Isomorphism.lean)：`two_step_iso_l`；[TwoStepFlatValue](../YesMetaZFC/Model/Forcing/TwoStep/Flatten/Value.lean)：`flat_value_l` | 原 ZF 内三层条目递归实现任意第二阶段名称的摊平及求值还原，补齐双射；保持并反射成员关系且保留逐名称解释，适用于外部非良基模型 |
| 支撑迭代的坐标后继 | [Forcing/IterationStage](../YesMetaZFC/Model/Forcing/Iteration/Stage/Basic.lean)：`row_zero_l`、`row_successor_l`；[IterationCohen](../YesMetaZFC/Model/Forcing/Applications/Cohen/Successor.lean)：`row_cohen_successor_l` | 实际部分函数零阶段及任意名称后继，原样完全嵌入、共同顶与精确前缀；有限／可数支撑同时保持，Cohen 添加量仍可依赖前阶段泛型 |
| 跨阶段投影与尾部提升 | [Forcing/IterationProjection](../YesMetaZFC/Model/Forcing/Iteration/Condition/Projection.lean)：`Row_link_d`、`row_link_comp_l`；[IterationSplice](../YesMetaZFC/Model/Forcing/Iteration/Condition/Splice.lean)：`row_splice_supp_l` | 实际名称后继返回单调限制投影；更强前缀与原尾部的拼接是共同加强。阶段链接可复合，有限／可数支撑拼接仅需 ZF |
| 模型内阶段族的支撑极限 | [Forcing/IterationLimit](../YesMetaZFC/Model/Forcing/Iteration/Limit/Basic.lean)：`row_limit_l`、`row_system_limit_l`；[IterationSystemSuccessor](../YesMetaZFC/Model/Forcing/Iteration/Stage/SystemSuccessor.lean)：`row_system_successor_l` | 从实际模型内序列构造有限／可数支撑极限偏序、各旧阶段的完全嵌入和保留尾部的加强；极限写回序列后可继续名称后继 |
| 完整内部支撑迭代 | [Forcing/IterationRecursion](../YesMetaZFC/Model/Forcing/Iteration/Recursion/Basic.lean)：`row_iteration_l`、`row_iteration_unique_l`、`row_iteration_step_l`、`cohen_iteration_l` | 给定已验证的原公式后继规则，在原 ZF 内构造任意内部序数长度的整个有限／可数支撑系统；字面唯一、前缀方程及参数化 Cohen 实例均已证明，适用于外部非良基地模型 |
| 有限支撑直接并与 CCC 迭代保持 | [Forcing/IterationDirectUnion](../YesMetaZFC/Model/Forcing/Iteration/FiniteSupport/DirectUnion.lean)：`row_limit_union_l`；[IterationRecursionCCC](../YesMetaZFC/Model/Forcing/Iteration/FiniteSupport/RecursionCCC.lean)：`row_iteration_ccc_exists_l`；[CohenIterationCCC](../YesMetaZFC/Model/Forcing/Applications/Cohen/FiniteSupport.lean)：`cohen_iteration_ccc_l` | ZF 内精确刻画非空阶段系统的有限支撑直接并；ZFC 内证明任意名称二步与有限支撑极限 CCC，再以内部超限归纳装配全部阶段，参数化 Cohen 实例自动返回 CCC |
| Lévy 有限公式反射 | [SetTheory/LevyReflection](../YesMetaZFC/Model/SetTheory/LevyReflection.lean)：`ZF.lr_finite_l`、`ZF.lr_reflect_l` | 原 ZF 构造包含任意给定集合的累积层，统一反射有限原公式族及全部层内参数；内部 ω 递归、秩界与实际结构解码均已证明，无额外反射公理 |
| 内部集合模型编码 | [SetTheory/Internal](../YesMetaZFC/Model/SetTheory/Internal.lean)：`smdl_satisfaction_l`、`source_satisfaction_l`、`scode_numbering_l` | 原 ZF 内构造结构码、全部内部有限指令码及完整递归满足关系；原 Project AST 与任意有限参数已自动编译，全部内部公式码已有自然数单射 |
| 内部司寇伦闭包 | [SetTheory/Internal/Skolem](../YesMetaZFC/Model/SetTheory/Internal/Skolem.lean)：`ssk_hull_l` | 原 ZFC 内构造实际见证选择图及任意内部可数种子的最小可数闭包，覆盖非标准有限参数并证明空种子时仍非空；通用闭包存在、最小性及单步可数性只需 ZF |
| 内部可数初等子模型 | [SetTheory/Internal/ElementaryHull](../YesMetaZFC/Model/SetTheory/Internal/ElementaryHull.lean)：`selem_hull_l`；[TarskiVaught](../YesMetaZFC/Model/SetTheory/Internal/TarskiVaught.lean)：`selem_iff_tv_l` | 原 ZFC 自动构造包含指定内部可数种子的实际初等子模型，比较全部内部公式码与完整内部赋值；有限支撑、Tarski–Vaught 双向等价、复合及编码理论保持均在 ZF 强度下证明 |
| 内部主条件与 CCC properness | [Forcing/InternalProper](../YesMetaZFC/Model/Forcing/Proper/Basic.lean)：`ccc_proper_l`、`proper_mstr_l`；[CohenProper](../YesMetaZFC/Model/Forcing/Applications/Cohen/Proper.lean)：`cohen_names_proper_l` | 实际构造可数主条件 club，证明 CCC 的 properness 并装配含任意可数种子的主加强；参数化 Cohen 名称有全局证书，并已接入完整可数支撑保持 |
| 全内部 N[G] 初等提升 | [Forcing/InternalGenericElementaryHull](../YesMetaZFC/Model/Forcing/Proper/Generic/ElementaryHull.lean)：`ng_elementary_hull_l` | 从 properness 和可数种子自动构造传递 X、内部初等 N 及主加强 q；每个接受 q 的泛型都满足整个 N[G]≺X[G]，覆盖全部内部公式码与赋值，X[G] 传递且 N[G] 可数；允许外部非良基与非标准 ω，自动选择使用 ZFC，提升证明只需 ZF |
| H(χ)、二步主条件与统一阶段模型 | [InternalHereditaryHull](../YesMetaZFC/Model/Forcing/Proper/Hereditary/Hull.lean)：`ng_hchi_hull_l`；[TwoStepMasterExtension](../YesMetaZFC/Model/Forcing/TwoStep/Proper/Extension.lean)：`two_step_master_extension_l`；[InternalGenericFamily](../YesMetaZFC/Model/Forcing/Proper/Family/Basic.lean)：`ng_family_hull_l` | H(χ) 双向泛型对应、二步主条件合成及主加强；同一个内部 N 支持全部成员阶段的 N[G]≺H(eχ)。完整区间迭代引理及最终 proper club 均已构造 |
| 二步主条件完整分解 | [TwoStepMasterDecomposition](../YesMetaZFC/Model/Forcing/TwoStep/Proper/Decomposition.lean)：`two_step_master_iff_l`、`two_step_master_decompose_l` | 二步 N 主性当且仅当首坐标 N 主性且首坐标迫使第二坐标 N[G] 主性；实际判定集与稠密原像保持指定首阶段泛型，自动构造规范 N[G] 名称，不要求模型外部良基或可数 |
| 内部提升证书、名称后继与稠密选择 | [IterationProperSuccessor](../YesMetaZFC/Model/Forcing/Iteration/Proper/Successor.lean)：`row_step_proper_name_l`、`row_step_proper_l`；[IterationDenseName](../YesMetaZFC/Model/Forcing/Iteration/Names/DenseName.lean)：`row_dense_force_l`、`row_dense_name_l` | 全阶段内部提升证书、统一规范名称图及旧条件精确回拉已有实际构造。相邻后继处理随泛型变化的商条件名称；任意阶段间选择进入 N 内稠密集的商加强名称，均保留指定主前缀。整列名称比较与融合主性已完成，一般内部序数的区间归纳已完成，最终 club 版保持已完成 |
| 相邻后继迭代引理与阶段传输 | [IterationSuccessorGeneric](../YesMetaZFC/Model/Forcing/Iteration/Proper/SuccessorGeneric.lean)：`row_step_pil_l`；[IterationBounded](../YesMetaZFC/Model/Forcing/Iteration/Names/Bounded.lean)：`row_delta0_force_l`、`row_rel_force_l` | 名称后继直接给出内部 Row_pil_d；指定主前缀严格不变，row_pil_value_l 自动构造 G∩check(N) 成员力迫。名称逐对象不变的阶段传输及真实滤子名称已实现；通用 Δ₀ 绝对性只需成员满单射 |
| 迭代引理的区间复合与稠密加强 | [IterationProperLemma](../YesMetaZFC/Model/Forcing/Iteration/Proper/Lemma.lean)：`row_pil_id_l`、`row_pil_comp_l`；[IterationProperDense](../YesMetaZFC/Model/Forcing/Iteration/Proper/Dense.lean)：`row_pil_dense_l` | 恒等与相邻后继有实际实例，已证明区间可复合；指定稠密名称选择保留原前缀及原名称的真实尾部比较。命题有原公式，适用于内部归纳；所有内部区间已统一装配，最终 club 版保持已完成 |
| proper 后继的共同模型装配 | [IterationProperFamily](../YesMetaZFC/Model/Forcing/Iteration/Proper/Model/Family.lean)：`row_pr_family_l`；[IterationProperRule](../YesMetaZFC/Model/Forcing/Iteration/Proper/Model/Rule.lean)：`row_iteration_pr_prepare_l`、`cohen_rule_pr_l` | ZFC 内实际收集全部辅助名称，自动构造共同 N、全阶段提升、统一规范名称图及 N 全部成员后继的迭代引理；任意添加量 Cohen 规则已有实例，一般内部序数的区间装配已完成 |
| 全部内部有限区间的迭代引理 | [IterationProperNatural](../YesMetaZFC/Model/Forcing/Iteration/Proper/Natural.lean)：`row_pil_nat_l` | 以原公式作内部 ω 归纳，从相邻后继和区间复合推出全部内部有限区间，包含外部非标准阶段；归纳只需 ZF，共同模型入口已自动返回该结论 |
| 变动前缀的限制比较与极限还原 | [IterationPrefixStep](../YesMetaZFC/Model/Forcing/Iteration/Proper/Prefix/Step.lean)：`row_cut_step_l`；[IterationPrefixLimit](../YesMetaZFC/Model/Forcing/Iteration/Proper/Prefix/Limit.lean)：`row_cut_fusion_l`、`row_cut_total_l` | 实际初值与名称投影给出比较实例；延长保持、共尾融合保持及旧支撑受界时的完整尾部比较均只需 ZF。相容前缀列、整列名称比较与融合主性已有实际构造 |
| 可定义类上的内部依赖选择 | [ClassChoice](../YesMetaZFC/Model/SetTheory/ClassChoice.lean)：`class_indexed_choice_l` | 原 ZFC 中通过反射见证闭包构造实际秩界，再用集合选择与原公式内部归纳得到 ω 函数图；不要求外部标准性或全局选择，已被变动主前缀递归实际使用 |
| 变动主前缀的实际内部序列 | [IterationThreadOmega](../YesMetaZFC/Model/Forcing/Iteration/Proper/Thread/Omega.lean)：`row_pr_omega_thread_l`；[IterationThreadCoherence](../YesMetaZFC/Model/Forcing/Iteration/Proper/Thread/Coherence.lean)：`row_pr_coherent_l` | 从共同 N 与真实 proper 后继图自动构造首个内部极限的共尾指标、稠密枚举、初始投影及主前缀序列，任意两指标精确相容；选择用 ZFC，一致性只需 ZF。整列名称比较与主融合已完成 |
| 早期名称比较及实际主融合 | [IterationThreadComparison](../YesMetaZFC/Model/Forcing/Iteration/Proper/Thread/Comparison.lean)：`row_pr_bound_l`；[IterationThreadMaster](../YesMetaZFC/Model/Forcing/Iteration/Proper/Thread/Master.lean)：`row_pr_master_fusion_l` | 任意早期名称的比较沿实际内部序列保持到全部后期，真实共尾尾段恢复完整尾部加强；稠密枚举、规范成员反射和拼接最大下界给出主性。比较与给定融合的主性只需 ZF，构造主融合使用 ZFC |
| 首个内部极限的完整区间迭代引理 | [IterationProperOmega](../YesMetaZFC/Model/Forcing/Iteration/Proper/Omega.lean)：`row_pr_omega_l`、`row_iteration_pr_omega_l` | 从实际 proper 规则、可数支撑迭代和种子自动返回共同 N 及 ω 终点的全部 Row_pil_stage 区间，保留原主前缀、旧名称完整尾部比较与主性，覆盖非标准内部自然数起点。一般内部超限归纳及实际 proper club 均已完成 |
| 任意内部长度的完整区间迭代引理 | [IterationProperInduction](../YesMetaZFC/Model/Forcing/Iteration/Proper/Induction.lean)：`row_pr_induction_l`、`row_iteration_pr_l`、`row_iteration_pr_exists_l`；[CohenIterationProper](../YesMetaZFC/Model/Forcing/Applications/Cohen/CountableSupport.lean)：`cohen_iteration_pil_l` | 原公式分离反例集，内部超限归纳统一零、后继和任意极限；自动构造同一个 N 的全部区间，保留指定前缀、主性和旧名称实际尾部比较。Cohen 添加量与内部长度直接参数化；适用于外部非良基模型。实际 proper club 及最终保持已完成 |
| 完整可数支撑 proper 保持 | [IterationProper](../YesMetaZFC/Model/Forcing/Iteration/Proper/Preservation.lean)：`row_iteration_proper_l`、`row_iteration_proper_exists_l`；[CohenIterationProper](../YesMetaZFC/Model/Forcing/Applications/Cohen/CountableSupport.lean)：`cohen_iteration_proper_l` | 固定三张实际运算图，以最小闭包构造任意包含条件域的 X 上的交集 club；同一 N 支持完整区间归纳，零前缀 check 条件产生主加强。全部阶段满足原 Proper_d，支持任意外部非良基 ZFC 模型，添加量及内部长度直接参数化 |
| proper 的可数性反射与 ω₁ 保持 | [InternalProperCountable](../YesMetaZFC/Model/Forcing/Proper/Preservation/Countable.lean)：`proper_countable_l`、`proper_omega_one_l`、`proper_extension_l`；[IterationProperPreservation](../YesMetaZFC/Model/Forcing/Iteration/Proper/Extension.lean)：`row_iteration_preserves_l` | 每个旧集合在 proper 扩张中可数当且仅当地模型中可数，旧 ω 的 Hartogs 序数精确保留。所有内部阶段同时装配 ZFC、ω、ω₁ 及旧可数性；`cohen_iteration_preserves_l` 直接参数化添加量和内部长度 |
| proper 的旧可数覆盖 | [InternalProperCoverValue](../YesMetaZFC/Model/Forcing/Proper/Preservation/CoverValue.lean)：`proper_countable_cover_l`、`proper_set_cover_l` | 旧集合在扩张中的每个新可数子集都有实际旧可数覆盖；任意新可数集合与旧集合的交亦可覆盖。覆盖证书的原公式实际稠密，由给定原泛型接受；全部可数支撑及 Cohen 阶段自动装配此性质，旧可数性反射已迁移为直接推论 |
| proper 的可数共尾性保持 | [InternalProperCofinality](../YesMetaZFC/Model/Forcing/Proper/Preservation/Cofinality.lean)：`proper_cf_omega_l`、`proper_countable_bounded_l`；[Cofinality/Countable](../YesMetaZFC/SetTheory/Card/Cofinality/Countable.lean)：`ZF.cf_omega_countable_l` | ZF 内从可数共尾集实际递归出严格 ω 共尾列；proper 扩张精确保留共尾度为 ω 的旧序数，旧共尾度大于 ω 时每个新可数子集均有严格旧界。全部可数支撑及 Cohen 阶段自动装配，不要求旧序数正则或模型外部良基 |
| 可数闭二步及坐标后继 | [TwoStepClosed](../YesMetaZFC/Model/Forcing/TwoStep/Closed.lean)：`two_step_chain_bound_l`、`two_step_closed_l`；[IterationClosedSuccessor](../YesMetaZFC/Model/Forcing/Iteration/Closed/Successor.lean)：`row_next_chain_bound_l`、`row_next_closed_l` | 对实际内部下降链构造共同下界；任意已压住整条链的前缀可原样保留。后继闭性来自被迫闭性与实际名称链，适用于非标准 ω，已接入任意内部长度的完整闭性归纳 |
| 参数化可数闭塌缩后继 | [CollapseClosed](../YesMetaZFC/Model/Forcing/Applications/Collapse/Closed.lean)：`collapse_two_step_closed_l`、`collapse_pair_closed_l`、`row_collapse_closed_l` | 自动生成条件域、序关系、顶与闭性名称，不要求调用者提供后继保持回调；两组任意集合参数直接生成可数闭二步塌缩，已有坐标阶段可追加实际闭后继并保留支撑约束 |
| 完整可数支撑闭性保持 | [IterationClosedInduction](../YesMetaZFC/Model/Forcing/Iteration/Closed/Induction.lean)：`row_cl_induction_l`、`row_iteration_closed_l`、`row_iteration_closed_exists_l` | 原链支撑并的有界／共尾分支实际构造任意极限下界，严格内部共尾列与相容前缀融合保留指定旧前缀；原公式超限归纳给出全部阶段闭性与完整区间，允许外部非良基模型 |
| 参数化闭塌缩迭代与序列反射 | [CollapseIteration](../YesMetaZFC/Model/Forcing/Applications/Collapse/Iteration.lean)：`collapse_iteration_closed_l`、`collapse_iteration_preserves_l` | 两个集合参数和内部长度直接构造整个可数支撑塌缩迭代；规范名称字面唯一、原公式规则存在唯一性及闭性证书均有实际证明。各泛型扩张满足 ZFC，并为实数、任意旧目标上的内部 ω 函数及旧集合的可数子集返回实际旧原像；可数子集原像同时具有地模型内部可数性 |
| 可数闭预序的 properness 与闭塌缩区间装配 | [InternalClosedProper](../YesMetaZFC/Model/Forcing/Closed/Proper.lean)：`closed_proper_l`；[CollapseIteration](../YesMetaZFC/Model/Forcing/Applications/Collapse/Iteration.lean)：`collapse_iteration_pil_l` | 实际稠密见证闭 club 与内部下降链给出主加强；只需预序。原塌缩规则取得真实 proper 名称证书，对任意可数种子自动返回共同 N 和全部适用区间引理；闭扩张同一规范嵌入还自动保持 ω₁、旧可数性及 ω 共尾性 |
| 可数支撑前缀融合 | [Forcing/IterationFusion](../YesMetaZFC/Model/Forcing/Iteration/Fusion/Basic.lean)：`row_fusion_l`；[IterationFusionRestriction](../YesMetaZFC/Model/Forcing/Iteration/Fusion/Restriction.lean)：`row_fusion_reconstruct_l` | 内部可数共尾前缀族有唯一的实际并条件，精确保留全部前缀；任意已构造极限条件可自动分解并还原，允许非标准 ω |
| 商名称投影与尾部加强复合 | [IterationProjectionName](../YesMetaZFC/Model/Forcing/Iteration/Names/ProjectionName.lean)：`row_project_name_l`；[IterationQuotientTransfer](../YesMetaZFC/Model/Forcing/Iteration/Names/QuotientTransfer.lean)：`row_quot_transfer_l`、`row_quot_lower_comp_l` | ZF 内构造前缀商名称，投影被接受后原名称进入新商偏序，并复合决定分支上的实际序加强；任意预序均适用 |
| 极限构造的内部指标与支撑界 | [IterationModelSequence](../YesMetaZFC/Model/Forcing/Iteration/Proper/Model/Sequence.lean)：`row_model_sequence_l`；[CountableCofinal](../YesMetaZFC/SetTheory/CountableCofinal.lean)：`ZF.cc_cofinal_sequence_l` | 实际构造共尾于 sup(N∩β) 的内部阶段列及 N 内全部稠密集的枚举，证明原 N 条件的支撑位于该上确界以下；共尾列与稠密枚举只需 ZF，相容主前缀递归与融合主性均已完成 |
| 固定前缀见证与混合闭合 | [Forcing/InternalNamePool](../YesMetaZFC/Model/Forcing/Internal/Maximum/Pool.lean)：`name_pool_mix_l`、`name_pool_represent_l`；[IterationWitness](../YesMetaZFC/Model/Forcing/Iteration/Names/Witness.lean)：`row_next_witness_l`、`row_next_lower_name_l` | 实际后继库对可定义混合闭合；等值代表及指定名称加强只需 ZF，一般有界存在见证使用 ZFC，输出后继条件的指定前缀字面不变 |
| 后继与极限的确定构造 | [Forcing/InternalNameHull](../YesMetaZFC/Model/Forcing/Internal/Maximum/Hull.lean)：`name_hull_exists_l`；[IterationNext](../YesMetaZFC/Model/Forcing/Iteration/Stage/Next.lean)：`row_next_unique_l`；[IterationLimitSyntax](../YesMetaZFC/Model/Forcing/Iteration/Limit/Syntax.lean)：`row_limit_unique_l` | 给定具体名称后，最小闭名称库、二步偏序、坐标后继与极限对象唯一；全部提供实际原公式，生产装配已直接迁移 |
| 内部累积层级与规范名称 | [SetTheory/CumulativeRank](../YesMetaZFC/SetTheory/CumulativeRank.lean)：`ZF.v_cover_l`；[CumulativeSelection](../YesMetaZFC/SetTheory/CumulativeSelection.lean)：`ZF.v_min_exists_l`；[Forcing/InternalNameNormal](../YesMetaZFC/Model/Forcing/Internal/Maximum/Normal.lean)：`norm_name_exists_l` | ZF 内构造覆盖全部模型对象的累积层级，并从最早层候选集得到全局力迫等号类的唯一规范名称；返回幂等证书，最大值与 Cohen 名称装配已直接迁移 |
| ZF 唯一见证与确定 Cohen 后继 | [Forcing/InternalUniqueMaximum](../YesMetaZFC/Model/Forcing/Internal/Maximum/Unique.lean)：`unique_maximum_l`；[CohenNames](../YesMetaZFC/Model/Forcing/Applications/Cohen/Names.lean)：`cohen_names_l`；[IterationCohen](../YesMetaZFC/Model/Forcing/Applications/Cohen/Successor.lean)：`row_cohen_unique_l` | 有界局部见证池与混合给出唯一规范名称；完整 Cohen 名称三元组和整个坐标后继均由实际原公式唯一确定，构造只需 ZF |
| ZF 强度的全局名称构造力迫 | [Forcing/InternalGenericCriterion](../YesMetaZFC/Model/Forcing/Internal/Reflection/Criterion.lean)：`forces_of_generics_l`；[TwoStepNameForcing](../YesMetaZFC/Model/Forcing/TwoStep/Names/Forcing.lean)：`curry_forces_name_l` | 同时反射实际原模型公式与名称参数，规范配对和二步名称性已有全局实例；原模型无需外部可数或良基 |
| 标准布尔值 ZFC 模型与一致性 | [Boolean/ZFC](../YesMetaZFC/Model/Boolean/ZFC.lean)：`bv_models_zfc`、`zfc_consistent` | 对任意完备布尔代数构造全部小名称，核验原 ZFC 及所有有限参数模式；从实际命题布尔代数与原六规则可靠性得到一致性 |
| Rosser 双侧独立性 | [PureRosserComplete](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean)：`PureRosser.independent` | 裸 ZFC 一致；具体纯闭句及其否定均不可证 |
| 可证明性 D1–D3 | [PureProvability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureProvability.lean)：`necessitation_m`、`distribution_m`、`introspection_m` | 无一致性或标准模型前提；任意纯闭句 |
| Löb 内部公式与规则 | [PureLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLoeb.lean)：`PureProvability.loeb_axiom_m`、`loeb_m` | 固定点实际构造；不另假定反射原则 |
| 哥德尔第二不完备定理 | [PureSecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSecondIncompleteness.lean)：`PureProvability.second_incompleteness_m` | 裸 ZFC 一致时，不能证明对应的对象一致性句子 |
| 纯公式自身编码的带参数固定点 | [PureFixedPoint](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFixedPoint.lean)：`fixed_point_m` | 任意有限参数；编码是最终纯公式自身的完整 AST 码 |
| Tarski 真不可定义性 | [PureTarski](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTarski.lean)：`undefinable_syntax_m`、`undefinable_parameters_m` | 句法版假定一致；语义版覆盖任意裸模型和参数赋值，量化同一参数上下文的全部纯开放公式 |

源理论、保留源编码的纯翻译和纯公式自身编码的具体合同分列如下。
原元数学核验覆盖 530 个依赖审计入口；小图层另核验 38 个关键接口。布尔层新增
50 个关键接口审计，并复核 8 个小图入口。全库构建与内模型审计的当前范围见核验指南。
原公理的 8 处句法闭合性原生依赖仍保留；详见
[UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md)。

## 内模型与可容许递归

总入口为 `YesMetaZFC.SetTheory.InnerModel`；[详细进度与调用边界](../YesMetaZFC/SetTheory/InnerModel/README.md)
区分 KP、KPi、ZF 和参数版本。以下是实际模型语义定理，允许模型 ω 非标准和外部非良基。

| 成果 | 最终入口 | 前提与范围 |
| --- | --- | --- |
| J 构造与可构造公理 | [Jensen/Constructibility](../YesMetaZFC/SetTheory/InnerModel/Jensen/Constructibility.lean)：`l_model_kpl_l` | 背景 KPi；实际 J 并类满足 KP＋V=L，并有完整公式成员归纳 |
| Δ₁ 可计算性等价 | [Computation/Readback](../YesMetaZFC/SetTheory/InnerModel/Computation/Readback.lean)：`cd_equiv_l` | KPi＋V=L；互补 Σ₁ 正规形与总 J 搜索布尔程序双向编译，基本运算及 Δ₀ 判定只需 KP |
| J 层的统一局部良序 | [Order/Statement](../YesMetaZFC/SetTheory/InnerModel/Order/Statement.lean)：`jh_order_model_l` | KPi；每个非空 J 层满足同一原语言良序句子，比较统一局部 Σ₁／Δ₁，完整初段属于同层；不假设单层可容许 |
| Σ₁ 凝聚及高度界 | [Condensation/Size](../YesMetaZFC/SetTheory/InnerModel/Condensation/Size.lean)：`jc_bounded_condensation_l` | KPi；任意内部大小的 Σ₁ 子结构坍塌为唯一 J 层，返回高度单射，并固定传递参数的子集 |
| L 满足 ZFC＋GCH | [GCH/Model](../YesMetaZFC/SetTheory/InnerModel/GCH/Model.lean)：`l_model_gch_l` | 背景仅 ZF；幂集、后继基数及等势双射均在同一实际 L 模型内解释 |
| 内部 OD/HOD 与 Σ₂ 证书 | [OD/Complexity](../YesMetaZFC/SetTheory/InnerModel/OD/Complexity.lean)、[HOD/Definition](../YesMetaZFC/SetTheory/InnerModel/HOD/Definition.lean) | ZF；内部 V 层满足关系、规范序数码、原公式唯一可定义性对应，以及 OD/HOD 成员的实际 Σ₂ 公式 |
| 参数内模型 | [HOD/BracketChoice](../YesMetaZFC/SetTheory/InnerModel/HOD/BracketChoice.lean)：`hb_model_zfc_l`；[Models](../YesMetaZFC/SetTheory/InnerModel/HOD/Models.lean)：`hp_model_zf_l` | 背景仅 ZF；HOD[A] 满足 ZFC，HOD(A) 满足 ZF；圆括号允许内部有限 A 参数列 |
| 弱齐性 HOD 比较 | [Homogeneous/HOD](../YesMetaZFC/Model/Forcing/Internal/Homogeneous/HOD.lean)：`whom_hod_comparison_l`、`whom_hb_comparison_l` | ZF、泛型、弱齐性及 OD／OD[A] 完整呈现；扩张 HOD／HOD[e(A)] 包含于地模型相应类的像，自动构造嵌入及坍塌 |
| Cohen 比较实例 | [Cohen/HOD](../YesMetaZFC/Model/Forcing/Applications/Cohen/HOD.lean)：`cohen_hod_comparison_l` | ZF、实际 Cohen 呈现、序数添加量和泛型；不另要求自同构、OD 呈现或坍塌证书 |

HOD 比较只断言从扩张到地模型的包含关系。L[A]、原 OD 解码／良序图的 Δ₂ 证书、
原无参数 `hod_model_l` 的完整模型接口归并等仍未完成，统一见详细指南的待建表。

## 裸 ZFC Rosser 实例

纯理论为 `PureModel.theory`，具体闭句为 `PureRosser.sentence`。记它为 $R$：

$$
\operatorname{Con}(\mathrm{ZFC})\Longrightarrow
(\mathrm{ZFC}\nvdash R)\land(\mathrm{ZFC}\nvdash\neg R).
$$

$R$ 只含隶属关系、等号与逻辑符号，是当前源 Rosser 句子的实际纯翻译。
最终定理仅假定裸 ZFC 一致；任意原模型对应 `Agreement` 已有证明。

| 成果 | 声明与源码 |
| --- | --- |
| 具体纯句子与普通 Hilbert 固定点推导 | [PureRosser](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosser.lean) 的 `sentence`、`fixed_point` |
| 任意原模型上的句子对应 | [PureRosserComplete](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) 中 `PureRosser.agreement` |
| 裸 ZFC 双侧不可证性 | [PureRosserComplete](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) 中 `PureRosser.independent` |
| 三参数纯 Δ₀ 矩阵及实际推导等价 | [PureRosserDelta0](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `matrix_delta0`、`parameters_exists`、`parameters_unique`、`representation_derives` |
| 当前纯句子非 Δ₀，以及一致性下排除无参数闭 Δ₀ 等价代表 | [PureRosserDelta0](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserDelta0.lean) 的 `sentence_not_delta0`、`no_closed_delta0_equivalent` |

纯 Δ₀ 矩阵为 $\neg\exists p\in w\,(p\in A\land\forall q\in p\,q\notin B)$。
参数定义未分类为 Δ₀，保留定义的完整存在闭句非 Δ₀。

## 普通可证明性的 D1–D3、Löb 与第二不完备定理

令 $T=\texttt{intrinsic_zfc_theory}$，$\Box\varphi$ 为
`ReducedProvability.provable φ`，使用原有
`ReducedNaturalProofPresentation.presentation.graph` 和完整 AST quotation。

| 成果 | 声明与源码 |
| --- | --- |
| D1：$T\vdash\varphi$ 推出 $T\vdash\Box\varphi$ | [ReducedProvability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProvability.lean) 的 `necessitation`；通用表示版见 [Provability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Provability.lean) |
| D2：$T\vdash\Box(\varphi\to\psi)\to(\Box\varphi\to\Box\psi)$ | [ReducedDerivability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedDerivability.lean) 中 `ReducedProvability.distribution` |
| D3：$T\vdash\Box\varphi\to\Box\Box\varphi$ | [ReducedIntrospection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedIntrospection.lean) 的 `ReducedProvability.introspection`；原验证矩阵反射已完整填入 |
| 具体 Löb 固定点 $T\vdash\psi\leftrightarrow(\Box\psi\to\varphi)$ | [ReducedLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedLoeb.lean) 的 `loebSentence_m`、`loeb_fixed_point_m`；复用原码域和对角构造 |
| 内部 Löb 公式 $T\vdash\Box(\Box\varphi\to\varphi)\to\Box\varphi$ | [ReducedLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedLoeb.lean) 的 `loeb_axiom_m` |
| Löb 规则：若 $T\vdash\Box\varphi\to\varphi$，则 $T\vdash\varphi$ | [ReducedLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedLoeb.lean) 的 `loeb_m` |
| 对象一致性句子 $\neg\Box\bot$ 及相对支撑语言的 Π₁ 分类 | [ReducedProvability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProvability.lean) 的 `consistency`、`consistency_pi1` |
| 内部第二不完备公式 $T\vdash\mathrm{Con}(T)\to\neg\Box\mathrm{Con}(T)$ | [ReducedSecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedSecondIncompleteness.lean) 的 `second_incompleteness_internal_m` |
| 第二不完备定理：若 $T$ 一致，则 $T\nvdash\mathrm{Con}(T)$ | [ReducedSecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedSecondIncompleteness.lean) 的 `second_incompleteness_m`；使用上述 `consistency` |
| 任意内部自然数证明码上的实际 MP 构造 | [ReducedProofComposition](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofComposition.lean) 的 `modus_ponens` |

D1–D3、Löb 和内部第二不完备公式不假定 $T$ 一致、可靠或其模型的自然数域外部标准。
D2 合并内部轨迹，
验证新增 MP 节点和根行，最后由既有强完备性导出普通 Hilbert 推导。
D3 通过实际公式的内部强归纳反射原已检查轨迹。Löb 的通用推导见
[Loeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Loeb.lean)，只消费 D1–D3
与固定点等价；具体实例实际构造该固定点，不把它另列为假设。
第二不完备定理将 Löb 规则应用于 $\bot$，只以 $T$ 一致为前提排除 `consistency` 的推导。
裸 ZFC 中的对应成果使用下述纯语言算子。

## 裸 ZFC 的可证明性、Löb 与第二不完备定理

令 $Z=\texttt{PureModel.theory}$，$e$ 为纯句子向原支撑语言的嵌入，$\tau$ 为支撑消元翻译。
纯语言算子定义为 $\Box_Z\varphi=\tau(\Box_T e(\varphi))$；
它仍使用原 quotation 和检查器，且 `checked_iff_m` 已证明接受嵌入句子证书
当且仅当 $Z\vdash\varphi$。

| 成果 | 声明与源码 |
| --- | --- |
| 纯句子双向推导 $T\vdash e(\varphi)\iff Z\vdash\varphi$ | [PureSentenceTransfer](../YesMetaZFC/Model/ZFC/Pure/PureSentenceTransfer.lean) 的 `derives_iff_m`；`translate_embed_m` 给出实际往返等价推导 |
| 纯语言可证明性的精确表示及 D1–D3 | [PureProvability](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureProvability.lean) 的 `checked_iff_m`、`necessitation_m`、`distribution_m`、`introspection_m` |
| 实际固定点、内部 Löb 公式和 Löb 规则 | [PureLoeb](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLoeb.lean) 的 `loeb_fixed_point_m`、`loeb_axiom_m`、`loeb_m` |
| $Z\vdash\mathrm{Con}_Z\to\neg\Box_Z\mathrm{Con}_Z$ | [PureSecondIncompleteness](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSecondIncompleteness.lean) 的 `second_incompleteness_internal_m` |
| 若裸 ZFC 一致，则 $Z\nvdash\mathrm{Con}_Z$ | 同文件 `second_incompleteness_m`；其中 $\mathrm{Con}_Z=\neg\Box_Z\bot$，`consistency_translation_m` 证明它等于原一致性句子的纯翻译 |

上述最终定理均在 `PureProvability` 命名空间中，句子只含纯隶属语言的符号。
固定点和 D3 使用任意原模型上的可证明性对应，没有额外反射或标准性前提。
这里没有另换一套直接编码纯 ZFC 证明树的检查器；与另选原生编码在对象理论内部的等价
不包含在这些结果中。

## 原支撑理论的塔斯基真不可定义性

令 $T=\texttt{intrinsic_zfc_theory}$，候选真谓词 $P$ 为无额外自由参数的任意
`FormulaTemplate.Unary`，$P(\ulcorner\varphi\urcorner)$ 使用当前 `IntrinsicQuotation.quote`。
下列入口均在 [ReducedTarski](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedTarski.lean) 中。

| 成果 | 声明 |
| --- | --- |
| 实际反例句 $L_P$ 及 $T\vdash L_P\leftrightarrow\neg P(\ulcorner L_P\urcorner)$ | `liarSentence_m`、`liar_fixed_point_m` |
| $T\vdash\neg(P(\ulcorner L_P\urcorner)\leftrightarrow L_P)$ | `liar_refutes_m`；不要求理论一致 |
| 一致性下，相应真值等价式不可证 | `biconditional_unprovable_m` |
| 一致性下，不存在全部真值等价式均可证的一元公式 | `undefinable_syntax_m` |
| 任意 $\mathcal M\models T$ 中，不存在对全部闭句正确的无参数真谓词 | `undefinable_semantics_m`；模型载体宇宙任意 |

反例句复用原对角构造，未留下固定点前提；逻辑核心见
[Tarski](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/Tarski.lean)。
无参数语义版量化宿主 `SetSentence`，允许模型内部自然数非标准。
保留源编码及使用最终纯公式自身编码的裸 ZFC 版本均见下文。
既有 `TarskiTruth` 提供集合结构的满足关系规格，与这里的真不可定义性分别登记。

### 任意有限参数的逐赋值版本

[ReducedTarskiParameters](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedTarskiParameters.lean)
的命名空间为 `ReducedTarski.Parameters`。候选 $P(x,\bar z)$ 允许任意有限参数列，
实际构造开放公式 $L_P(\bar z)$，其原 quotation $\ulcorner L_P\urcorner$ 不随参数取值变化。

| 成果 | 声明 |
| --- | --- |
| $T\vdash L_P(\bar z)\leftrightarrow\neg P(\ulcorner L_P\urcorner,\bar z)$ | `liarFormula_m`、`liar_fixed_point_m` |
| $T\vdash\forall\bar z\,\neg(P(\ulcorner L_P\urcorner,\bar z)\leftrightarrow L_P(\bar z))$ | `liar_refutes_closed_m`；无一致性前提 |
| 一致性下，任意有限参数上下文均不能具有全部可证真值等价式 | `biconditional_unprovable_m`、`undefinable_syntax_m` |
| 同一反例在任意原模型的每一组参数赋值下使等价式失败 | `liar_fails_at_m` |
| 固定任意参数赋值，排除全部候选公式 | `undefinable_at_m` |
| 同时排除任意有限参数数目、取值及候选公式 | `undefinable_parameters_m` |

真值合同是对所有相同自由上下文中的宿主开放公式 $\varphi(\bar z)$，要求
$P(\ulcorner\varphi\urcorner,\bar a)\leftrightarrow\varphi(\bar a)$。
参数是任意模型元素，不要求由闭项或标准数码命名。这个合同包含使用参数本身的反例公式；
它不等同于仅要求候选判定无参数闭句的真值集合，也不把非标准内部语法的满足关系列为已构造内容。

### 裸 ZFC 中保留源编码的纯语言版本

[PureTarskiSource](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTarskiSource.lean)
允许任意纯候选 $P(x,\bar z)$。令 $S_P$ 为其嵌入原语言后实际生成的反例，
$L_P=\tau(S_P)$ 为纯反例，$\tau$ 是现有的完整关系消元。以下推导均使用裸 `PureModel.theory`。

| 成果 | 声明 |
| --- | --- |
| 纯候选、源反例及实际纯反例 | `Candidate_m`、`sourceLiar_m`、`liarFormula_m` |
| 消元后的候选实例恰好应用原纯候选，保留全部参数 | `predicate_satisfies_m`；编码值由 `quotation_m` 给出，与赋值无关 |
| $L_P$ 与对应候选实例的否定等价，以及反驳式的全称闭合 | `liar_fixed_point_m`、`liar_refutes_closed_m`；无一致性前提 |
| 裸 ZFC 一致性下，排除相应等价式及全部可证真值等价式 | `biconditional_unprovable_m`、`undefinable_syntax_m` |
| 任意裸 ZFC 模型、每组有限参数赋值下均失败 | `liar_fails_at_m`、`undefinable_at_m`、`undefinable_parameters_m` |
| 直接排除原纯候选定义规范扩张中全部源开放公式的真值 | `undefinable_source_at_m` |

合同量化源公式 $\varphi(\bar z)$，在其原编码处要求
$P(\ulcorner\varphi\urcorner,\bar a)\leftrightarrow\tau(\varphi)(\bar a)$。
因此这里的反例编码是 $\ulcorner S_P\urcorner$，不是 $\ulcorner L_P\urcorner$。
这个接口保留其源编码合同；纯公式自身编码的结果由下一独立接口给出。

### 裸 ZFC 中纯公式自身编码的版本

[PureQuotation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureQuotation.lean) 与 [PureQuotationFaithful](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureQuotationFaithful.lean)
提供完整纯 AST 编码、单射性及原编解码器对应。
[PureFixedPoint](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFixedPoint.lean) 的 `fixed_point_m` 对任意有限参数的纯候选 $P$
实际构造纯公式 $L$，证明 $\mathrm{ZFC}\vdash L(\bar z)\leftrightarrow P(\ulcorner L\urcorner,\bar z)$；
其中编码是最终纯公式 $L$ 本身的码，编码实例用纯数码公式定义。

[PureTarski](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTarski.lean) 导出：

| 成果 | 声明 |
| --- | --- |
| 实际纯反例及自身编码 liar 固定点 | `liarFormula_m`、`liar_fixed_point_m` |
| 裸 ZFC 直接反驳相应真值等价式及其全称闭合 | `liar_refutes_m`、`liar_refutes_closed_m`；无一致性前提 |
| 一致性下排除全部可证纯真值等价式 | `biconditional_unprovable_m`、`undefinable_syntax_m` |
| 任意裸模型、任意有限参数赋值下排除纯真值定义 | `liar_fails_at_m`、`undefinable_at_m`、`undefinable_parameters_m` |

合同量化所有相同自由上下文的纯公式 $\varphi(\bar z)$，要求
$P(\ulcorner\varphi\urcorner,\bar a)\leftrightarrow\varphi(\bar a)$。
编码独立于参数赋值；参数不要求闭项名称，模型不要求标准。
这仍是宿主有限公式的真不可定义性，不是非标准内部语法满足关系的构造。

## 内部数码与轨迹反射

继续使用现有 `ObjectNumeralSyntax.condition` 与完整 AST 编码。
其输入和输出是任意内部自然数，不要求能解码为宿主 `Nat`。

| 成果 | 声明与源码 |
| --- | --- |
| 数码图总性与唯一性的实际对象闭句推导 | [PureSourceNumeralTotality](../YesMetaZFC/Model/ZFC/Pure/PureSourceNumeralTotality.lean) 中 `PureSourceNumeralSyntax.totalUnique_derives` |
| 数码输出通过当前完整语法图的闭项检查 | [InternalNumeralQuotation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralQuotation.lean) 中 `PureSourceNumeralSyntax.wellFormed_derives`、`quotation_exists_unique`；`graph_term` 还覆盖任意内部上下文长度 |
| 标准输入与既有 AST 编码算法一致 | [PureSourceNumeralTotality](../YesMetaZFC/Model/ZFC/Pure/PureSourceNumeralTotality.lean) 中 `PureSourceNumeralSyntax.standard_iff` |
| 固定完整 AST 的非标准自由代入 | [PureSourceSubstitution](../YesMetaZFC/Model/ZFC/Pure/PureSourceSubstitution.lean) 中 `PureSourceInstantiation.formula_substitution`、`unary_substitution`；接入当前模式 3 变换图 |
| 数码命名与代入在整个内部 ω 上的实际总性推导 | [InternalNumeralSubstitution](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralSubstitution.lean) 的 `total_derives`；同一个合法闭项数码作为代入表条目 |
| 非标准结论码上的六类节点装配和 MP | [ReducedProofComposition](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofComposition.lean) 的 `codeProof_of_node`、`modus_ponens_code`；保留原证明图与实际语法条件 |
| 内部逻辑公理及存在引入 | [ReducedProofLogicalConstruction](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofLogicalConstruction.lean) 的 `logical_rule`、`exists_introduction`；须提供实际模式 2 实例化证书及正文、项和实例的语法证书 |
| 自由代入与点实例化的同一输出 | [PureSourcePointInstantiation](../YesMetaZFC/Model/ZFC/Pure/PureSourcePointInstantiation.lean) 中 `PureSourceInstantiation.unary_point`；抽象后的模式 2 输出等于原公式的模式 3 输出 |
| 无额外语法义务的数码存在引入 | [InternalNumeralProof](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralProof.lean) 的 `instance_wellFormed`、`exists_introduction`；只消费数码图及实例的内部证明 |
| 已证定理的全部内部数码实例 | [InternalNumeralSpecialization](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralSpecialization.lean) 中 `InternalNumeralProof.specialize_values`、`specialize_finite`；任意有限参数数目，旧单参数入口与 MP 复用统一构造 |
| 连续特化保持已代入数码 | [InternalNumeralTransform](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralTransform.lean) 中 `PureSourceNumeralSyntax.graph_transform`；[InternalNumeralParameters](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralParameters.lean) 的 `PureSourceInstantiation.numeral_point`，保持任意内部深度下的合法数码 |
| 任意内部数码可证明属于 ω | [InternalNumeralArithmeticReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralArithmeticReflection.lean) 中 `InternalNumeralReflection.natural`、`natural_derives`；实际可分离公式归纳，零／后继步骤无反射假设 |
| 内部数码零测试的正负反射 | [InternalNumeralZeroReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralZeroReflection.lean) 中 `InternalNumeralReflection.zero`、`nonzero`；两种真值均生成当前证明图接受的内部证明 |
| 任意两个内部数码的相等与不等反射 | [InternalNumeralEqualityRules](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralEqualityRules.lean) 中 `InternalNumeralReflection.equal`；[InternalNumeralEqualityReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralEqualityReflection.lean) 中 `unequal`、`unequal_derives`，对非标准自然数也成立 |
| 内部自然数严格／非严格序的正负反射 | [InternalNumeralOrderReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralOrderReflection.lean) 的 `order`、`weak_order`、`order_derives`；序关系及其否定都生成原证明图接受的内部证明 |
| 任意内部自然数的加乘幂数码求值 | [InternalArithmeticEvaluation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalArithmeticEvaluation.lean) 的 `addition_evaluation`、`multiplication_evaluation`、`exponentiation_evaluation`、`arithmetic_evaluation_derives`；三个运算复用实际公式的内部归纳，没有求值反射假设 |
| Gödel 配对及复合编码项求值 | [InternalPairingEvaluation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPairingEvaluation.lean) 的 `pairing_evaluation`、`pairing_evaluation_derives`；[InternalCodingEvaluation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCodingEvaluation.lean) 覆盖字段列、节点、Horn 表达式和参数化 AST 码项，共用 `binary_term_evaluation` |
| 既定 quotation 的求值证明 | [InternalQuotationEvaluation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalQuotationEvaluation.lean) 的 `quotation_evaluation`；保持原树编码，输出原证明谓词接受的数码等式证明 |
| 复合项原子及逻辑联结词的正负反射 | [InternalAtomicReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalAtomicReflection.lean) 的 `atomic_reflection`；[InternalBooleanReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalBooleanReflection.lean) 的 `boolean_reflection`，数值与内部证明可非标准 |
| 任意内部自然数界的量词反射 | [InternalBoundedTerms](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalBoundedTerms.lean) 的 `bounded_term_reflection`；全称／存在、正／负方向共用界项求值与 `bounded_bundle`，不假定内部区间外部有限 |
| 原验证矩阵的有限轨迹证明装配 | [InternalVerificationTrace](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalVerificationTrace.lean) 的 `finite_verification`；原检查器及局部条件不变，有限骨架及各行内部证明仍是输入 |
| 任意内部数码递归轨迹的正负反射 | [InternalNumeralTraceReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralTraceReflection.lean) 的 `numeral_trace_positive`、`numeral_trace_positive_derives`；[InternalNumeralTraceDecision](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalNumeralTraceDecision.lean) 的 `numeral_trace_negative`、`numeral_trace_reflection`；使用原 `ObjectNumeralSyntax.condition` 和原证明图；实际对象公式归纳，无外部有限轨迹或反射假设，支持已求值复合项 |
| 原投影图全部七条规则的内部正反射 | [InternalProjectionReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProjectionReflection.lean) 的 `projection_positive`、`projection_term_positive`、`projection_positive_derives`；索引、输入和原轨迹均可非标准，取尾递归使用实际对象公式归纳 |
| 原一般语法图的内部正反射 | [InternalSyntaxReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSyntaxReflection.lean) 的 `syntax_positive`、`syntax_term_positive`、`syntax_positive_derives`；项、参数列和公式共用实际公式的内部强归纳，覆盖非标准输入与上下文，并保留原检查器规则 |
| 原四种语法变换的内部正反射 | [InternalTransformReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalTransformReflection.lean) 的 `transform_positive`、`transform_term_positive`、`transform_positive_derives`；原 28 条规则共用分层内部强归纳 |
| 原 schema 与传输包图的内部正反射 | [InternalSchemaGraphs](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaGraphs.lean)、[InternalPacketReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalPacketReflection.lean)；正文、重命名、表生成、闭句、quotation 转换及传输包的原规则均已反射 |
| verifier 实际 schema／公理查询的内部正反射 | [InternalSchemaQueries](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalSchemaQueries.lean) 的 `packet_term_positive`、`axiom_term_positive`、`axiom_query_positive`、`axiom_query_positive_derives`；保留原有界查询和数码，覆盖非标准参数，无查询反射前提 |
| 原逻辑／证明行查询的内部正反射 | [InternalProofRowReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofRowReflection.lean) 的 `logical_term_positive`、`node_term_positive`、`row_term_positive`、`row_named_positive` 及三项 `*_positive_derives`；全部原逻辑公理、六类节点及实际行封装，无局部查询反射假设 |
| 实际检查步骤的局部证明装配 | [InternalCheckedStepReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalCheckedStepReflection.lean) 的 `proof_step_values`、`finite_verification_of_links`；局部查询只需真值，原 Horn 连边证明仍须提供 |
| 原证明树任意内部已检查轨迹反射 | [InternalProofTraceReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalProofTraceReflection.lean) 的 `proof_trace_positive`、`proof_trace_values`、`proof_trace_positive_derives`；覆盖全部原规则与非标准根行，不要求外部骨架或连边证明 |
| 原验证矩阵与完整证明矩阵的数码反射 | [InternalVerificationReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/InternalVerificationReflection.lean) 的 `verification_reflection`、`proof_matrix_reflection`；保留原图、quotation 和自然数 guard |

内部归纳使用最终解释的实际纯公式，并先证明原模型与规范扩张的真值对应。
`checkedRankedAt_agrees` 同时覆盖原 checked 轨迹及其数码实例的可证明性；
两阶段秩证书只依赖原证明树的固定规则表，输入证明码覆盖整个内部 ω。
`proof_trace_positive` 结合已完成的局部行查询正反射，消去了外部有限骨架和连边证明输入。
`verification_reflection` 经 `verificationMatrix_trace` 接回原检查器正文，
`proof_matrix_reflection` 补齐自然数 guard；`ReducedProvability.introspection`
因此给出 $T\vdash\Box\varphi\to\Box\Box\varphi$，无附加反射假设。

有限骨架、单行装配及条件性矩阵装配接口仍可单独调用；它们不是完整轨迹反射的假设。
本次结论是原验证图及其数码实例的正反射，不登记一般负反射或完整真理反射。

## 可复用的基础成果

| 成果 | 实际入口 | 指路表 |
| --- | --- | --- |
| 完整自然数证书往返与可推导性表示 | [ZFC/NatEncode](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/NatEncode.lean)、[ZFC/NatDecode](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/NatDecode.lean) | [证书和对象图](NAT_DECODING.md) |
| 当前 quotation 的具体证明表示与源 Rosser 实例 | [ReducedProofPresentation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofPresentation.lean)、[ReducedNaturalProofPresentation](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedNaturalProofPresentation.lean)、[ReducedRosser](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedRosser.lean) | [证书和对象图](NAT_DECODING.md) |
| 有限基使用的 64 个函数、46 个关系的纯定义 | [PureCompletedStage](../YesMetaZFC/Model/ZFC/Pure/PureCompletedStage.lean) | [定义与规格](ELIMINATION.md) |
| 119 条有限基及原无限参数支撑理论的模型验证 | [PureSupportModels](../YesMetaZFC/Model/ZFC/Pure/PureSupportModels.lean) 的 `support_models` | [逐项公理索引](UNIFIED_VERIFICATION.md) |
| 原 ZFC 像、纯翻译、模型扩张与约化 | [PureZFCModels](../YesMetaZFC/Model/ZFC/Pure/PureZFCModels.lean) 的 `models`、`translated_models`、`expands`、`reduction` | [模型与推导](UNIFIED_VERIFICATION.md) |
| 全部内部自然数证明码的实际图对应 | [PureSourceLocalTests](../YesMetaZFC/Model/ZFC/Pure/PureSourceLocalTests.lean) 的 `proof_agreement` | [内部模型对应](UNIFIED_VERIFICATION.md) |

一般反向句法保守性未包含在上表结论中。原递归序列族之并在合法递归器下的
ω 全域性仍是独立数学待办。源码核验与可信依赖以
[UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md) 的当前基点为准。
