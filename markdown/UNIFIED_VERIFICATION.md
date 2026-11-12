# 公理验证与不完备性接口指路表

本页记录数学接口、理论强度与可信依赖边界。构建入口见 [RESTORE.md](RESTORE.md)，
轻量策略及模块职责见 [PROVER_SPLIT.md](PROVER_SPLIT.md)。

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

## 当前 Lean 公理边界

公理解耦的源码基点、验证命令与计数方法见 [解耦审计报告](AXIOM_DECOUPLING_20261006.md)。

2026-10-06 对源码基点 `1e89850` 的全生产声明审计覆盖 1,751 个源模块、46,361 条声明。
逐声明原始传递依赖闭包的公理并集仅为 `propext`、`Quot.sound`、`Classical.choice`；
没有生产自定义公理、原生决策公理或 `sorryAx`。这表示依赖并集，不表示每个端点均依赖三者。
原 13 处 `sentence!` 闭合性原生公理已移除，当前审计不再放行这些旧证书。
各端点的精确集合以对应源码基点的原始依赖闭包为准，修改后须重新运行相关审计。

[`sentence!`](../YesMetaZFC/SetTheory/Notation/Surface.lean) 先尝试 `decide +kernel`，
仍为内核不能约化的 opaque 输入保留 `native_decide` 后备分支；上述结论针对已审计的
生产声明，不是对该语法未来所有输入的全局禁用声明。
[闭合性兼容测试](../scripts/test_sentence_closedness.py) 区分透明输入、opaque 后备与开放公式拒绝；
[精确公理守卫](../scripts/check_axiom_decoupling.py) 及[端点清单](../scripts/axiom_decoupling_bounds.json)
维护生产切片的实际依赖边界。

## 内模型与弱齐性比较的核验

当前内模型端点及理论强度统一见[内模型进度](../YesMetaZFC/SetTheory/InnerModel/README.md)。
J 的递归与局部良序消费 KPi；L 的 ZFC＋GCH、OD/HOD 参数模型及弱齐性比较消费 ZF。
内部全公式小壳的一般构造使用 ZFC，GCH 证明先在 L 中导出 AC，再在 L 内调用它，
因此 `l_model_gch_l` 的背景前提仍为 ZF。

相对 Jensen 层级、规范 L(ℝ)、AD 与武丁基数定义的入口见
[Relative](../YesMetaZFC/SetTheory/InnerModel/Relative/README.md) 和
[LargeCardinal](../YesMetaZFC/SetTheory/LargeCardinal/README.md)。`lr_model_zf_l` 仅需 ZF；
统一层界、有界分离、序数包含和公式相对化仅需 KPi。

[TypeOneStep](../YesMetaZFC/SetTheory/LargeCardinal/Types/OneStep.lean) 的 `ee_one_step_l`
完成 Neeman 3.23：实际构造 τ+ω、源和不可达最大强度扩展器，保留原固定子类型程序、
内部任意有限元数与排列。[WoodinTypeStep](../YesMetaZFC/SetTheory/LargeCardinal/Cardinals/WoodinTypeStep.lean)
的 `woodin_elastic_step_l` 从武丁假设自动产生同一元组的两份弹性类型和一步实例。
两个证明的 Lean 公理均仅为 `propext`、`Quot.sound`、`Classical.choice`；
纯结果关系 `Ee_one_step_d` 仅依赖前两者，原定义的子类型查询 `Ts_subtype_d` 无公理依赖。
完整实现及编译证书中既有平坦配对实例的经典依赖位于 Prop 证明字段，未引入不可计算数据。
该层已通过 `lake --wfail build` 的默认公共导入图和 `scripts/check_internal_models.py`
四组声明审计：内部模型 710 模块／11989 声明，HOD 2／42，小壳 41／360，Łoś 106／1095。
两份新证明模块分别为 76、55 行，编译约 3 秒；这项核验不包含尚未完成的 L(ℝ)⊨AD。

[LocalIndiscernibles](../YesMetaZFC/SetTheory/LargeCardinal/Cardinals/LocalTypeTransportTuple.lean)
在 ZF 中实际构造参数带 V(δ+ω) 和全部内部查询域。类型值属于同一幂集；
`ordinal_unbounded_fiber_l` 通过原公式收集取得无界纤维，产生任意下界以上、
满足 ν+ω<μ 的完整类型相同的序数对。`Li_pair_d.read_l` 将它读取为原公式的
逐参数真值对应。[LocalIndiscerniblesLeast](../YesMetaZFC/SetTheory/LargeCardinal/Cardinals/LocalTypeTransportTuple.lean)
按原 δ<ν 条件、第二坐标优先的顺序构造最小对，并证明唯一性及原公式表示，不把额外间隔条件
加入最小化。固定查询关系、原公式及赋值数据另经无选择依赖检查。
这一层已纳入上述四组审计。五份构造模块共 354 行，单模块 39–95 行，正常编译约 2–5 秒。

[LocalTypeTransportTuple](../YesMetaZFC/SetTheory/LargeCardinal/Cardinals/LocalTypeTransportTuple.lean)
的 `Li_pair_d.transport_l` 已完成有限后继秩层的完整类型搬运。k>0 与元组长度都取自
内部 ω；源元组逐项自动生成原名字列，固定对象可以来自整个共同极限参数带。
`li_canonical_transport_l` 从任意 θ≥δ 自动产生最小不可分辨对，固定参数带 V(θ+ω)，
而指定常量仍为 δ。新元组在 V(μ+k) 实现原 V(ν+k) 中字面相同的 κ 型，
包括原常量域与全部内部查询。背景只需 ZF、ω<δ 且 δ 为极限序数；未对源秩层附加 ZF。
原加法递归历史和内部有限函数的秩闭包均实际证明。八份搬运模块共 716 行，单模块
48–137 行，编译约 2–4 秒。原名字、矩阵、读取公式与结果关系额外通过无选择依赖审计；
全部新增声明无新公理、`sorryAx` 或不可计算数据。

[TypeGameDecoding](../YesMetaZFC/SetTheory/LargeCardinal/Game/RecoverySyntax.lean) 已把一张图恢复
接入实际子类型见证。内部有限集合公式完整核验中间坐标的两个包含方向；节点谓词再检查
坐标图的函数性、精确定义域和三元组图属于树。源绝对性只使用传递性。
`tg_one_graph_recovery_l` 自动构造三个实际查询，保留任意双射排列及逐项对应，恢复原树、
末位和恰好一个新增标签；高度由最大序数查询推出为 α+1。
[TypeGameReset](../YesMetaZFC/SetTheory/LargeCardinal/Game/Reset.lean) 实际构造二元重置
类型，连同完整节点、空根和最大序数查询的语义证书及真值。规范局部不可分辨对的最小化
同时校正为原 5.12 的第二坐标优先约定，已重验其存在性、唯一性及完整类型搬运。
本层十一模块共 775 行，单模块 42–120 行，正常编译约 3 秒，均少于一分钟。
全部新增声明已纳入上述四组审计；14 个关系、原公式及查询证书另经无选择依赖检查。

[TypeDrop](../YesMetaZFC/Model/SetTheory/Types/DropEmbedding.lean) 已实际构造内部前缀投影和
dcp。查询的自然数公式码不变，名字列只将指定常量 δ 的元数标记从小元数重编码为大元数；
裸类型的投影是该纯语法关系的逆像。结果由实际限制元组实现，增加末位后再取 dcp
字面返回原完整类型。[TypeGameReply](../YesMetaZFC/SetTheory/LargeCardinal/Game/ReplyDescent.lean)
装配规则 (7) 的子类型、空根、严格秩界及加二最大序数；实际语言工厂和低层回答构造均已实现。
严格秩界另已与原集合秩公式证明等价，实现高度由查询准确读取为末位加三。
[TypeElasticDomain](../YesMetaZFC/SetTheory/LargeCardinal/Types/ElasticDomain.lean) 将原定义域
查询的独立读取纳入既有弹性语言，不需要完整弹性或 ZFC；
[TypeGameRigidity](../YesMetaZFC/SetTheory/LargeCardinal/Game/Rigidity.lean) 只用 ZF、
超过关系和 dcp⁻ 定义域，就证明新类型的末位为最大序数。
[WoodinGameReset](../YesMetaZFC/SetTheory/LargeCardinal/Cardinals/WoodinTypeStep.lean) 在原 ZFC 武丁
假设下实际生成任意参数域下界以上的重置类型，完整节点、根、最大序数和 dcp 弹性同时为真。
本层十四模块共 855 行，单模块 34–91 行，编译约 3 秒；全部模块仍少于 2000 行。
新增关系、公式、游戏约束及语言证书中 21 个声明另通过无选择依赖检查；全部新增
声明已通过上述四组审计，无新增公理、`sorryAx` 或不可计算数据。
两张图恢复及 5.15 的迭代获胜论证已接到 TypeGameTransfer 的实际 II 策略；真类 Woodin 下的最终 L(ℝ)⊨AD 已由 `wd_lr_ad_l` 证明。

[TypeGame](../YesMetaZFC/SetTheory/LargeCardinal/Game/RoundNativeScope.lean) 的 `tg_game_l` 已完成原 5.13
辅助闭博弈的实际装配。先从 max(δ,rank(S)) 自动选择原最小局部不可分辨点，再在模型内部
统一化三张固定代码表；弹性表、节点／端点表的图包含于 Vδ，仅依赖内部元数的子类型程序表
的图包含于 Vω。原函数图、名字列及完整编译性质都有原语言公式和精确解码定理。
合法性只读取同一固定表项及查询字面成员性，不给裸类型假定逻辑闭包或可实现性。

[TypeGameHistory](../YesMetaZFC/SetTheory/LargeCardinal/Game/RoundNativeScope.lean) 构造全部内部
有限历史与逐步检查集合，完整合法历史另形成前缀树。七条规则保留域增长、原重置类型、
回读较早轮、pred(t) 及任意排列的 subtype／exceeds；唯一额外坐标条件为空根。
[TypeGameStages](../YesMetaZFC/SetTheory/LargeCardinal/Game/RoundNativeScope.lean) 用内部序数除法
对每个时刻恢复唯一轮号、阶段、责任玩家及相应规则，保留 II 辅助、I 回答、原实数落子的因果顺序。
[FirstViolationMinimum](../YesMetaZFC/SetTheory/Descriptive/Game/FirstViolationMonotone.lean) 在模型内
最小化失败前缀的长度，不使用外部 ω 的良基性。`Tg_game_d.payoff_l` 精确证明 I 获胜当且仅当
全程合法或首次违规属于 II；闭收益集及其开补集都是实际集合。策略空间及常值策略实例也实际构造。
获胜策略由下述闭博弈定理另行取得。

完整博弈装配层含 31 个新增模块、2336 行，每模块 29–125 行，正常检查约 2–9 秒。
66 个纯公式和数据接口另经无选择依赖检查；全部新声明纳入上述四组审计。

[ClosedDeterminacy](../YesMetaZFC/SetTheory/Descriptive/Game/ClosedDeterminacy.lean) 的
`cg_closed_det_l` 在 ZFC 中证明任意非空集合字母表、任意固定玩家时序上的闭博弈决定性。
证明遵循 Neeman 4.16 的获胜局面集合：内部策略量词定义 II 获胜区，ZF 构造按首项拼接的
策略图，模型内选择提供子策略族及 I 的可走字母，再以最早进入获胜区的内部长度证明避让。
整个论证不要求 ω 外部标准或外部良基。
[TypeGameDeterminacy](../YesMetaZFC/SetTheory/LargeCardinal/Game/RoundNativeScope.lean) 的
`Tg_game_d.determined_l` 返回原三阶段游戏策略空间中某一方的实际获胜策略。
TypeGameTransfer 已完成 5.15 的实际 II 策略转移。TypeGameCollapse 的 `tg_lemma61_l` 已闭合 6.1：
最小编号策略、原实数坐标一致性、地稠密集调用和 6.6 首达捕获共同推出严格高度矛盾。
旧类型实现关系在地模型中形成实际集合；扩张 ZF 内只读取其像并对已捕获高度取最小元，
不假定旧 Vα 是扩张的 Vα。实际 δ≅Vδ 双射诱导有限条件的序同构及泛型回拉，
端点直接使用原 Col(ω,δ) 名称扩张并保留规范名称求值方程。
TypeGameCorollary67 的 `tg_corollary67_l` 已接出 6.7：自动添加无约束 ω 坐标，
删除映射的树逆像与地嵌入交换，在地面及扩张内分别证明两投影相等并保留同一策略。
该投影对应仅需 ZF；Woodin 与 ZFC 假设由原 6.1 消费。
TypeGameCorollary610 的 `tg_corollary610_l` 已完成 6.10。首项拼接推广到任意集合字母表，
内部后继奇偶律反转玩家，实际策略图保留正确首手条件；移位树及投影对应沿地嵌入保持。
同一获胜接口同时支持投影和补投影，6.7 的全部调用已迁移。
TwinTreeCertificate 的 `td_determinacy_l` 已完成优化稿定理 2.3：地面两投影互斥与原坍缩
正条件的强迫覆盖，给出地面互补、实际获胜策略和反方反例树的有界序数秩。
截面树秩回传固定旧实数的投影成员关系；同一名称扩张中的实际策略对弈排除两个泛型分支。
TwinTreeGround 调用原 `source_of_generics_theory_l`：实际构造可数初等子模型和泛型滤子，
再用原强迫真值定理及初等反射返回任意地模型；没有外部可数性或泛型存在假设。
TwinTreeOutward 的 `Td_winner_d.outward_l` 保持同一策略和反例树秩，目标只需 ZF；
I 分支使用外模型的两树覆盖，II 分支不需要覆盖。一般树秩已抽至 TreeRank，旧策略尝试树直接复用。

包含 6.1、6.7、6.10 及双树决定性、向外胜策保持端点的生产源通过
`python scripts/lean_cache.py build` 的全部 2770 个独立模块检查；
各批实际执行 `lake --wfail build`，公共入口亦在其中。
`python scripts/check_internal_models.py` 的内部模型切片覆盖 887 模块、15154 声明，
连同 HOD、小壳与 Łoś 三组全部通过；`python scripts/check_forcing.py` 的七组审计亦全部通过。
未发现新增公理、`sorryAx` 或不可计算数据；旧实现表、已捕获高度、有限序列重编码、
树逆像、坐标删除、二坐标投影、移位树、双树覆盖原公式及胜策秩证书的纯定义
另通过无选择依赖检查。力迫内部切片为 150 模块、2348 声明。
相对 `33fbf401` 的净代码增量为 995 行；新增 13 个模块，最长 135 行，
全仓最长模块为 1952 行。本轮新增模块编译均低于一分钟，最终全源构建中最慢的重建模块为 6.7 秒。

`scripts/check_internal_models.py` 覆盖这些模块以及嵌入读取、派生超滤、有限支撑测度图
和共同纤维完备性证明的全部实际声明；博弈、谓词嵌入、武丁基数与测度族的原定义
另检查无选择依赖。有限支撑测度构造的背景仍为 ZF，图的定义域唯一性仅需外延性，
函数值域扩大不需要集合公理。坐标复合与重排图在 KP 中构造；任意有限坐标的
协调律及任意载体派生测度的 κ 完备性在 ZF 中证明，原可测基数端点已迁移。
内部约化幂层在 ZF 中构造指定函数族的等价类、投影和商关系，并证明代表元无关性；
商的等价性与关系只用共同细化，可在 KP 中从指定候选集合分离合法代表。
源内部子集代数、其相对派生超滤与精确源内部函数族的商已构造；相对否定律
只对已证明容许的真值逆像成立。全部背景内部函数的代表族已在 ZFC 中证明
全部内部代码的 Łoś 方程；赋值和更新留在 ZF 层，存在见证统一化单独使用原选择公理。
`pe_compile_l` 已构造覆盖全部内部代码的逐点解释程序及实际根映射；
`sc_pe_trace_l` 已将其用于源中真值逆像，逐点赋值和常值代表均有实际构造。
`sc_diagonal_l` 与 `sc_pe_witness_l` 实际构造源内对角及统一代表，
`rs_los_l` 在实际原公式上完成源内部函数族的全部内部行归纳。
`rs_satisfies_l` 给出统一满足关系的 Łoś 方程；`rs_los_assignment_l` 从真实 ω→G 图
自动构造赋值空间、商赋值和代码集。源内入口消费传递源的 `Sc_theory_d`，背景为 ZF；该理论已由实际 Hχ 和传递初等后继构造。
其中赋值投影与逐点逻辑方程按 ZF 审计，相对超滤的或非规则不需要集合公理。
常值初等嵌入及分量初等映射已经由实际源函数图与商投影构造；
`es_source_projection_l` 将有限支撑测度协调律接入同一构造，返回实际初等交换图。
源内有界分离、容许代数、限制超滤和拉回核按 ZF 审计；从代表图下降到商图的
`rp_lift_exists_l` 另逐项限定 ZF。源内复合、源内部 Łoś 与常值初等嵌入均按 ZF 审计；分量间完整初等性的商赋值代表选择按 ZFC 审计。
恒等、复合、常值交换律及坐标重排的对应图方程另检查无选择依赖。
内部定向系统的新层按同一 ZF 可信基审计：指标、标签与过渡关系都是模型内部集合；
规范商、极限关系和关系保持映射的泛性质只用 ZF。可数定向极限及可数完备测度分量的
良基性显式消费内部 DC，实际 `ZFDC` 与 `ZFC` 模型均已有这个实例。
`woodin_wf_components_l` 的背景为 ZF＋DC，保留有限支撑测度族的协调与共同纤维性质。
有限支撑测度族现已装配为实际全系统：`ep_system_exists_l` 收集源分量模型图和全部过渡，
代表族精确为源中的函数；分量模型收集按 ZF 审计，初始 Hχ 与完整投影装配按 ZFC 审计。
`es_joint_fiber_l` 在 ZF 中用单射坐标列和逐层有限交，同时实现任意内部可数有限支撑约束。
`ep_limit_wf_l` 的背景仅为 ZF＋DC：实际下降代表图、约束族及统一求值图把极限下降链
变成源下降链。`woodin_extender_l` 从同一个武丁测度族自动返回源、全系统、极限结构码与良基性。
`di_elementary_limit_l` 在 ZF 中量化全部内部代码证明完整初等极限，已由源分量实际实例化。
完整测度的源内限制保持同一个规范商；原过渡图因而取得完整内部初等证书。
外延性通过真正的内部等号句子传递，`wc_smaps_l` 在 ZF 中构造良基外延结构的传递坍塌和双向完整初等同构。
武丁自动入口现位于 `ExtenderDerivedLimit`，以 ZFC 中的 Hδ＝Vδ 采用原 Vδ 源，
并返回求值方程 k([a,f])＝j(f)(a) 的实际关系因子；没有将关系因子标成到原目标的完整初等嵌入。
`ExtenderLength` 在 ZF 中由实际坐标覆盖恢复临界点、长度界及原因子固定性。
`woodin_rank_strength_l` 在 ZFC 中按 ν 自动选择不可达 L>κ,ν。可测基数的正则性及
小幂集无反向单射在 ZF 中证明，强极限性用原对象选择公理补齐实际编号。
`er_inaccessible_cover_l` 对全部严格秩层使用短枚举、累积历史比较及两个支撑坐标，
证明同一个因子像包含整个 V_L；传递坍塌于是逐点固定 V_L，并恢复谓词一致性。
`ep_inaccessible_bound_l` 从原 P(κ) 常值像下的代表构造实际满射，再用 |V_L|=L
和 Cantor 定理证明同一目标缺少某个 L 的子集，故最大强度恰为 L。
`Ex_strength_d` 以所属源中的实际有界超幂和求值图记录该事实；原公式 `es_strength_m`
保留源内量词，完整初等传输与指定实际超幂中的读取均按 ZF 边界核验。
`Sc_inaccessible_d` 使用原始正则基数和强极限基数公式；初始 Vδ 中的实际共尾图、
值域与幂集单射给出内部实例。该判断沿完整初等图传输，并在严格极限秩段中保持。
`Ex_short_d.local_l` 回收原测度图及可数共同纤维，直接构造初始 Vδ 的内部短扩展器判断。
这些构造只需背景 ZF，不额外要求整个相对模型满足 ZF；函数解释仅消费实际配对闭包。
`Vr_d.rank_l` 回收同一较早秩层及原历史，旧层级闭包已直接迁移；`Er_level_d.rank_l`
同时保留实际枚举图。`Eb_collapse_d.rank_l` 用该枚举控制原节点集，再在截断中
塌缩并识别同一个传递像和求值图。`Ex_strength_d.rank_l` 保留相对幂集及原遗漏子集，
故最大强度也在严格秩截断中保持。`Ep_strong_limit_d.rank_l` 自动构造截断源并返回
强度、枚举、内部不可达性与短扩展器判断；截断高度只要求源内正则性，无强极限前提。
nice 树的全前驱 Pₙ 递归、内部下降反证、整树 Skolem 回拉、返回原 Vθ 的初等因子与 ω₁ 长公开弱迭代策略已完成。
`Ep_strong_limit_d` 将全部结论与同一张 F、同一个系统和商投影绑定。
谓词初等性覆盖全部内部代码：先证明 Vδ＝Hδ 的原代表族包含全部所需函数，再用任意关系的
完整 Łoś 和关系更换定理处理同一个极限。新嵌入具有实际 `Spred_emb_d`，而非仅有原子谓词保持。
秩历史比较、因子固定、关系更换、同像比较及谓词原子求值按 ZF 审计；
枚举族、完整谓词 Łoś 与自动强性端点按 ZFC 审计，纯定义和原公式另排除选择依赖。
传递后继源保持已接入同一个 `Ep_collapse_d`：对每个 κ′∈N、ω⊆κ′，实际构造下一步源。
`UniversalSyntax`／`UniversalClosure` 用原公式内部归纳处理任意非标准程序的全称闭包；
有效性和编码理论的正向传输、分离与统一化的目标保持、ω 固定、全部背景内部有限函数闭性
及序列空间保持都按 ZF 审计。`Sc_theory_d` 与 `Sc_sequences_d` 的定义另排除选择依赖。
初始 Hχ 的全部内部模式和任意字母表的有限序列空间按 ZFC 审计；后继保持不再要求嵌入 Hχ。
源自身的函数、坐标投影、代表族与分量模型，以及原求值装配和极限因子接口均已降低到 ZF。
相对测度、子集一致性、真值集合搬运及复制核按 ZF 审计；实际代表族始终在源中。
定向极限的有限参数覆盖通过内部有限归纳和唯一值收集完成，完整初等锥的因子也只需 ZF。
分量复制和系统复制按 ZFC 审计，返回实际完整初等图、唯一性、常值交换方块及良基性回传。
`ep_copy_apply_l` 自动构造两侧系统；`ep_owned_copy_l` 构造 N∈X 的实际跨模型实例。
`ep_copy_identity_l` 另单独收紧为 ZF；相对接口及复制图的定义排除选择依赖。
源内代表正规化、有限坐标编码、坐标原子、正规前驱封闭与坐标坍塌值按 ZF 审计；
同一复制图的支撑搬运及坍塌共轭也只需 ZF。有限原公式在实际像中的有界 Łoś
复用全内部满足关系，参数赋值由有限递归构造。
`ep_successor_agree_l` 从实际相对施加及两侧坍塌推出完整 L 上的有限幂子集一致性，且 L 属于两侧后继；
`Ex_short_d.successors_l` 自动构造两侧后继及下一步源。`ep_copy_successor_l`
实际生成后继复制；极限支撑秩段带实际枚举时，进一步返回 k(L)=σ(L) 及整个 j(κ)+1 上的一致性，
同时保存原超幂、目标超幂及完整常值交换方块。
完整分量嵌入、后继一致性装配及两个自动入口按 ZFC 审计；新增定义另排除选择依赖。
迭代树层保存内部树序、模型码、全部嵌入图及操作图，所属扩展器使用模型内原公式的满足关系。
`it_order_extend_l` 与 `it_move_push_l` 只需 KP；复合图唯一性和后继非极限性只需外延性。
新增祖先箭头由替代收集，完整初等性、交换律和整树扩张按 ZF 审计；单根与 pad 已构造。
`di_cone_limit_l` 从覆盖锥给出实际直接极限；`it_branch_limit_l` 将树的前驱像覆盖条件接到该证书。
`it_apply_l` 的一般施加接口单独收紧为 ZF；背景短扩展器自动施加、后继一致性及三结点分叉
按 ZFC 审计。模型内短扩展器判断不作为背景良基性的替代，全部新定义另检查无选择依赖。
极限层从原模型列和嵌入列构造带标号系统、实际集合商、全内部规范初等嵌入及传递坍塌，
`it_wf_branch_extend_l` 给出新树和同一系统到新模型的 `Di_limit_d`。分支指标序和极限树序
只需 KP。`it_sigma_extend_l` 在 ZF＋DC 中消费给定共尾枝及 ω<cf(α)；
`it_pruned_extend_l` 在 ZF 中从内部 ω 共尾序列、任意高的树后继及实际相容良基实现
自动选枝并添枝。选择下一指标使用序数最小值与确定递归；相容实现仅需成员关系保持。
任意内部极限长度的 padding 树及其完整极限扩张已有实际构造；一般迭代策略未列入成果。
`Wc_iso_d` 提供 Δ₀ 的实际传递塌缩同构证书，原关系的外延性只需外延性，良基性只需 KP。
`sc_h_collapse_l` 与 `sc_v_collapse_l` 给出小相对良基外延关系塌缩的实际实例，后者仅需 ZF；
`sc_collapse_iff_l` 在 ZF 中传输整条存在句子，已直接纳入所有源与后继源构造。
`Ea_subset_d.relation_l` 在 ZF 中用二项有限列单向搬运小关系；`ep_transitive_code_l`
从实际源内枚举自动生成关系码，`Ea_subset_d.transitive_l` 在另一源内部塌缩并识别原传递集合。
支撑端点使用常值 κ 的像作统一界，再在目标有限列空间内实际分离其迹；原严格界接口已直接迁移。
序数不下降性、源内可数图的有界性及 `Sc_omega_bound_d` 的双向初等保持按 ZF 审计；
该共尾性条件已有实际正则基数实例。`smap_small_restriction_l` 从序数限制图回拉关系码，
在目标内塌缩并还原原枚举，从而构造整个小传递域上的限制图。
`ep_copy_countable_restriction_l` 自动取小界，只消费 φ 以下逐层一致性；
`ep_copy_successor_l` 的同一实际复制已带限制恢复结论。不可达 Vκ 的 κ 枚举及其 Hχ 源实例按 ZFC 审计。
相对秩层的唯一性、传递性、Vδ 初始层级和初等保持均按 ZF 审计；
`Er_level_d` 的实际初始枚举用 ZFC，枚举与相对秩历史的传输、整层限制恢复只需 ZF。
外部枝反射 `Sc_branch_d` 已独立：Hχ 实例用 ZFC，极限 Vδ 实例用 ZF；
`Ep_source_d.tree_branch_l` 从实际源与枝反射构造源内总分支，按 ZF 审计。
完整初等嵌入尝试树与解码已实现：有限语法、赋值空间和真值表实际存在于源，
源内节点公式与检查全部内部公式的 `At_node_d` 等价；相对分离构造整棵前缀树。
`Ep_source_d.countable_membership_l` 返回源内完整 `Smap_d`、规定限制保持及嵌入图的
源内可数性单射；给定实际源证书及枝反射后全链只需 ZF。模型内小 Skolem 壳及源内枚举也已实现：
极限 Vδ 和正则 Hχ 提供实际实例，全参数保持及跨源塌缩隶属的一步构造已经证明。
正则 Vβ 适用的弱源接口已实现并迁移，完整源实例不再要求强极限性。
`sc_countable_function_rank_l` 只用内部不可数共尾性证明可数函数图及其给定编号属于严格相对秩层；
`ep_skolem_rank_step_l` 已接通尝试树回收、该秩界、Vκ∪{κ,σ} 的实际枚举及小壳塌缩。
新嵌入保持原传递定义域，嵌入图和可数性见证属于新模型自身；低秩指定值与 κ 保持。
同一输出已自动保留完整源证书、枝反射、相对层级、相对幂集及小壳闭包。
`Ep_source_d.rank_l` 在 `Sc_regular_d` 的内部正则界下构造完整秩段源；有限列保持给定序数界，
全内部分离和统一化经源内有限真值表得到，小塌缩由同一编号的成员归纳控制秩。
`Ep_source_d.skolem_rank_l` 以有界图闭包保持小壳性质，分离、统一化、序列、塌缩及小壳传输
均已提供回拉；这些构造按 ZF 审计。
`ep_branch_reflection_l` 在 ZF＋给定 DC 下，用同一共同纤维保持定义出的无枝标签关系良基性；
`Ex_short_d.node_l` 的实际后继装配按 ZFC 审计，自动返回源、枝反射、层级、相对幂集和小壳不变量。
`Sc_power_d` 的相对幂集只含源已有的子集；极限 Vδ 给出初始实例，完整初等图及相对极限秩段保持该性质。
`rs_bounded_model_l` 实际构造源内有界函数集、类投影、商载体及关系码；类与投影沿用原约化幂定义。
`sf_maximal_relative_l` 用载体的源内相对幂集构造单元素扩张，从内部极大性导出实际相对超滤，
没有假定相对模型满足 ZF。`It_local_d.measures_l` 和 `coherent_l` 直接读取原扩展器公式；
`apply_l` 在子集一致性下自动生成完整初等定向极限，按 ZFC 审计，读取与有界商入口仍按 ZF 审计。
`Ea_subset_d.levels_l` 把施加源 X 中的完整可数层族搬到较小所属模型 Y⊆X；
先用两源共有的 κ 编号搬运层族的带长度标记并集，再逐层还原。
`It_local_d.source_fiber_l` 结合这项搬运、Y 的枝反射及内部可数纤维条件，构造 Y 中的实际共同纤维；
层族属于 X 是必要前提，未把内部短扩展器改成背景可数完备扩展器。
`ep_bounded_desc_l` 在同一极限投影上构造源内有界代表关系的完整逆像，并用枝反射回收下降图。
源内 Cantor–Bernstein 构造支撑的单射覆盖，有限交证明整张源内约束层族的每层具有测度一；
`It_local_d.source_wf_l` 据此在 ZF＋DC 中证明相对后继良基性。
同一有界代表方法处理无枝标签关系，`It_local_d.branch_l` 证明实际后继的枝反射。
`ep_constant_limit_l` 和 `ep_collapse_l` 已直接改为 ZF 加已有初等性证书，旧调用全部迁移。
`It_local_d.node_l` 在 ZFC 中自动构造携带全部不变量的同一后继；`it_local_apply_l`
再把这张实际超幂边加入原迭代树。全过程保留原商类、代表及投影，不假定所属模型满足 ZF。
`It_local_d.atoms_l` 和 `normal_l` 在 ZF 中直接读取内部原子条件与源内正规性。
`It_local_d.successors_l` 实际构造两侧后继，证明支撑端点上的子集一致性并保留全部不变量；
`ep_source_trace_l` 用源内有界分离计算有限支撑幂迹，`It_local_d.subsets_l` 将自身超幂的
这些子集送回所属模型。两步复合得到 `Ea_subset_d`，直接供编码与小壳塌缩搬运使用。
单向搬运所需的关系、函数、集合值代表、层族和 Skolem 步接口已迁移并削弱到该条件。
`ep_set_restriction_l` 以源内有限真值表证明完整内部初等限制；`it_ultra_rank_l` 实际辨认
内部正则秩段的超幂为 j(Vα)，且超幂边就是 j↾Vα。`ep_copy_successor_l` 已改为固定原树
的实际超幂来构造复制目标；所属判断沿同一原初等图搬运。
`It_local_d.rank_l` 已证明原短扩展器公式的全部条款在严格极限秩段中保持；
`It_local_d.return_l` 对指定实际后继给出编码回收。
`it_ultra_unique_l` 在 ZF 中识别同源同扩展器的实际超幂及其嵌入；
`it_ultra_rank_agree_l` 从共同正则秩段得到同一像秩段、像高度和限制图。
`sc_presentation_l` 通过前驱纤维商在源内塌缩允许重复代表的小关系，
`it_ultra_owned_image_l` 据此在原源中还原低秩传递集合的同一个 j(B) 及实际求值图。
`eb_owned_value_l` 通过双向搬运 κ 值代表，直接把施加超幂的同一个 j(κ) 和求值图放回所属源。
`Eb_collapse_d.map_l` 沿 σ 传输完整节点、原测度关系及求值图；`realize_l` 用重复代表的塌缩唯一性
辨认目标施加超幂。有限幂编码还推出 π(f)=σ(f)，从而在 ZF 中完成 j(κ)+1 上的复制一致性。
`ep_copy_successor_l` 已接入支撑端点保持、完整常值交换方块和目标实际超幂。
集合值函数和二元关系的实际有限幂编码已提取，并直接替换旧所属搬运证明中的重复构造。
`Eb_trace_d` 的源内构造、沿嵌入传输和跨源读取给出 `ep_copy_subsets_l`，证明全部有限 L 幂子集的像一致。
`Ea_maps_d.transitive_l` 由实际源内枚举和关系码证明整个被枚举传递集合上的逐点一致性；同一后继入口已返回此结论。
`Smap_d.countable_fixed_l` 固定源内可数传递集合；`sc_domain_numbering_l` 从已有可数函数图
直接回收精确定义域及其编号，旧调用已迁移。`ep_countable_ultra_l` 在包含源内构造全部
原代表、测度一关系及满射呈示，回收原超幂和它的内部可数编号；原复制后继直接消费此结果。
严格秩截断、Pₙ 全前驱历史、内部下降反证及到 j(A) 的完整初等复制均已实现。
历史延伸直接由原树读取并构造下一行，内部 ω 递归不消费另行假设的可延伸接口。
`ja_failure_l` 现从可数根模型构造整树公共编号、联合尝试关系及正则基数值下降秩；
下降链解码为实际共尾枝、完整初等腿和传递直接极限，且满足原根复合式。
`It_local_d.closed_limit_l` 用所属源的有界值域 ω 闭性构造跨模型良基超幂；
`It_ultra_d.closed_l` 通过共同强度秩段回收任意目标 ω 序列，保持背景可数闭性。
`ep_set_copy_l` 将 π:M→A 复制到同一大超幂中的 j(A)，保持完整内部初等性、
常值方块、支撑端点及全部有限 L 幂子集上的 σ。证明使用实际有限代表矩阵、整张真值表及原源 Łoś；A 的高度不要求正则。
`Ic_row_d.copy_l` 已构造整棵长度 ω 的 nice 复制树。正规 Vδ 给出可数闭工作源，
所属秩段中的原判断向上读取后实际施加扩展器；共同强度秩层保留所有前驱的一致性。
实际类依赖选择收集原公式编码的有限历史，三张相容图取并保留全部初等箭头、
真实超幂边、常值方块、原根嵌入及目标秩段的像。递归不预设统一高度界或外部标准 ω。
联合节点公式已迁移到实际有限真值证书，与全部内部公式检验双向等价。
`Ep_source_d.ja_node_l` 证明源内外节点判定一致；有限部分图闭性回收每个背景节点。
`Ja_space_d.full_image_l` 在像参数给出实际枚举图时证明完整像树及原严格扩展关系，
不是仅保持旧节点的逐点像。以上新端点均按 ZF 边界核验。
`it_countable_fixed_l` 已从公共可数传递载体固定原树全部编码；联合尝试节点沿复制方块严格延伸。
`Ic_history_d.rank_l` 实际收集内部 ω 上的唯一移位高度，在每条严格树边上证明新高度小于旧高度的像。
`rank_cut_l` 将模型内正则高度转换成包含原扩展器和支撑的实际秩段列；根高度保留背景正则性。
`it_nice_failure_copy_l` 从原可数 nice 树的返回失败自动构造正规根和整棵下降复制树。
`Fs_read_d` 将超幂证书读取收紧到传递性、配对和内部有限函数闭性。完整源及其任意包含 ω 的
拥有极限秩段均提供实际实例，后者不要求高度正则。`it_ultra_read_l` 恢复原有限支撑系统、
商投影、直接极限、常值图、坍塌和复合图；完整初等性由原 Łoś 定理及常值代表唯一性恢复，
不把原满足关系公式假定为绝对。原 `Ep_graph_d`／`Ep_system_d` 已整体迁移到只参数化有序对解释的定义。
`ep_reflect_hull_l` 在实际极限反射层之上取正则包络及可数壳；小层的有限闭性由原相对秩历史给出。
`it_nice_pull_l` 恢复同一树序、完整初等边、指定超幂、最大强度及递增支撑；实际复制模型的幂集闭性来自原历史。
`it_cut_pull_l` 和 `it_drop_pull_l` 回拉正则秩段与原下降值；`pn_initial_pull_l` 从背景正则根的实际限制构造首行。
`it_nice_return_l` 接入下降反证，完成 Neeman 定理 2.3。目标 Vθ 的极限性已从配对闭包推出，不另作假设。
`it_nice_weakly_iterable_l` 完成推论 2.4：真实 Hχ 同时容纳全部可数 nice 走法，
原选择公理给出实际应答函数；历史原公式的超限归纳证明合法对局一直有效。
状态取并、规范商投影及其腿、前缀重放与公开策略输出对应均保留原图。
获胜证书覆盖直到实际 Hartogs(ω) 的全部初始对局；运行唯一性只用 ZF 和局部单值性。
真类 Woodin 下的 L(R) AD 已由 `wd_lr_ad_l` 证明。
有限矩阵、内部源闭性和正则下降秩的关系操作按 ZF 边界核验；实际超幂、赋值代表选择和正则化使用 ZFC。
短扩展器层全部按 ZF 边界审计：`Ex_pre_d`、`Ex_short_d` 及原公式对应已实现，
正规性、临界点种子、布尔运算、有限坐标乘积、有界投影、可数纤维和长度截断均已证明。
有界投影的见证使用序数最小值统一化，未调用对象选择公理。
`woodin_short_l` 对每个 κ<L<δ 返回同一个测度族、实际幂集算子和
`E(A)=j(A)∩L^{<ω}` 的精确识别；有限列表示保留对象模型内全部长度。
`woodin_extender_l` 已直接消费该接口，源模型装配继续单独按 ZFC 审计。
同构与 Mostowski 坍塌已在 ZF 中核验全部内部代码的真值保持；可数壳构造在 ZFC 中
自动返回可数传递坍塌及完整初等嵌入。一般传递源与 J 层实例共用同一构造，
编码理论沿嵌入回拉；外部标准模式与全部内部代码模式的区别仍需保留。
任意内部程序的分离实例现已构造为真实代码，支撑外新变量由原有限支撑定理核验。
ZF 中只要像集合的全部子集包含于目标，就能沿完整初等嵌入取得源内分离集。
极限 V 层的可数传递壳已有此自动实例；可数壳构造单独按 ZFC 审计。
全内部收集实例也已构造为程序码；正则 H(χ) 的实际见证小集沿初等嵌入回拉，
从可数种子自动取得同时具有分离和收集的可数传递模型。代码构造保留 ZF 强度，
H(χ) 中的见证统一化与小集合封闭单独按 ZFC 审计。
统一函数图的代码现已构造，两个实参使用不同坐标；实际函数图和值域界经初等嵌入回到源。
H(χ) 的配对与乘积封闭已迁至集合论层，原力迫调用直接迁移，不保留旧命名空间转发。
混合模块中的后继保持、源内函数与分量模型、模式正向传输及因子接口另逐条收紧到 ZF。
核验不包含尚未实现的“真类个武丁基数 ⇒ L(ℝ) 满足 AD”证明。

`whom_hod_comparison_l`、`whom_hb_comparison_l`、`cohen_hod_comparison_l` 在上述
`1e89850` 原始依赖审计中均只依赖 Lean 的 `propext`、`Quot.sound`、`Classical.choice`，
没有原生闭合性公理或 `sorryAx`。这里的命题内经典证明不等于假定背景模型满足 AC；
上述三个定理的对象理论前提仍为 ZF。
临时审计模块及其产物已移除，生产审计清单维护在
[check_internal_models.py](../scripts/check_internal_models.py) 和 [check_forcing.py](../scripts/check_forcing.py)。

## 模型、公理与推导

| 要使用的结果 | 接口与源码 | 精确范围 |
| --- | --- | --- |
| 原生小图模型与裸 ZFC 一致性 | [SmallGraph/ZFC](../YesMetaZFC/Model/SmallGraph/ZFC.lean)：`sg_model`、`sg_project_zfc`、`sg_models_zfc`、`zfc_consistent` | 小图双模拟商直接构造；原公理及全部有限参数分离、收集模式已经核验，无模型存在或一致性前提；载体固定为 `Type (u+1)` |
| 标准布尔值 ZFC 模型 | [Boolean/ZFC](../YesMetaZFC/Model/Boolean/ZFC.lean)：`project_zfc`、`bv_models_zfc`、`zfc_consistent` | 任意 `B : Type u` 及实际 `CB_alg B`；名称节点同层，载体固定在 `Type (u+1)`；原公理与所有有限参数模式逐句核验 |
| 任意地模型的内部泛型商 | [Forcing/InternalQuotient](../YesMetaZFC/Model/Forcing/Extension/Isomorphism.lean)、[InternalChoice](../YesMetaZFC/Model/Forcing/Extension/Choice.lean) | 外部非良基、内部 ω 非标准的地模型也满足完整真值及原 ZFC 保持；商载体与地模型同 universe，基础公理通过内部公式归纳证明 |
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
在 `1e89850` 原始依赖审计中的精确集合为上述三项，不再继承原八条固定公理的
`sentence!` 原生闭合性证书，没有自定义公理、`sorryAx` 或原生决策公理。
全库构建的当前范围见上节；代码范围及载体边界见
[模型论指南](../YesMetaZFC/Model/README.md)。

布尔层新增 50 个关键依赖入口并交叉复核 8 个小图入口。`name_structure`、名称等号的
递归定义、图并合、混合和 ω 数据均无公理依赖；一般布尔值六规则可靠性以及名称的
等词、分离、幂集、无穷、基础证明仅涉及 `propext`、`Quot.sound`。最大值、收集、选择及
ZFC 终点仍依赖 `Classical.choice`；`Boolean.zfc_consistent` 在 `1e89850` 原始依赖
审计中与小图一致性终点同为上述三项，没有 `sorryAx`、自定义公理或原生决策公理。
将对象理论限制到 ZF，不改变这些模型构造与一致性端点的元层依赖。

集合结构的内部编码由 `scripts/check_internal_models.py` 单独审计，ZF 基础覆盖
65 个模块、1170 条实际声明；司寇伦、club 闭包、遗传小集合、初等模型装配与
类上依赖选择另覆盖 13 个模块、50 条声明。结构码、变量赋值、
非标准有限指令码、递归真值表、统一满足关系及编码理论模型性均有实际原公式。
ZF 基础的存在性已不再继承原生句法闭合性公理；数据与
定义端点继续严格排除 `Classical.choice`。`smdl_table_l` 给出唯一真值表及精确成员真值，
`smdl_satisfaction_l` 将全部满足对收集成内部集合；没有新增公理或不可计算数据。
`source_compile_l`、`source_satisfaction_l` 已完成原 Project AST 的编译及任意有限
参数下的精确语义对应，不要求解码结构外延。`ZF.countable_fseq_l` 通过内部 ω 递归
构造全部有限序列的统一编号；`scode_numbering_l` 据此给出包含非标准公式的内部
单射。两项只需 ZF。
`ssk_hull_l` 从原 ZFC 自动构造整张内部司寇伦选择图及任意可数种子的最小可数闭包，
并证明所有内部有限参数下的存在见证闭性；假公式的零元运算确保空种子的闭包也非空。
选择图、有限参数延拓、闭包及见证闭性均有实际原公式。通用闭包存在性、最小性、
有限参数阶段截取与单步可数性仍逐声明保持 ZF 边界；自动选择与完整装配使用 ZFC，
其余端点另作 ZF 核验；各切片均不再允许原生句法闭合性公理。
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
`lr_model_l` 对应到实际内部隶属结构。该层保持 ZF 强度且无原生闭合性公理，全部语法和
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
`ng_elementary_l` 的提升端点保持 ZF 强度；选择图和自动装配使用 ZFC，
均无原生闭合性公理。数据定义严格排除经典选择。
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
共尾序列的值域外延性及长度极限性改为直接内核证明，相关模块按 ZF 切片
审计，不允许原生 DAG 编译证书。旧序数反射与共尾集传输另按无原公理上界检查。
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
函数及旧集合可数子集的实际旧原像。`distributive_fn_dense_l` 先由内部稠密交及替换收集
整张旧函数图，再由原泛型遇到该原公式稠密集；`no_new_countable_l` 反射枚举及其
实际值域，以最小自然数原像返回旧子集的内部可数性。此公共层只需 ZF＋可数分配性；
`closed_distributive_l` 在 ZF＋DC 中从可数闭性产生分配性，原 ZFC 消费者直接装配 DC 实例。
`closed_proper_l` 通过真实二参数见证闭 club 和模型内 ω 下降链证明可数闭预序
的 properness；不需要额外的排除值序公理。`collapse_rule_pr_l` 将该结论提升为
原塌缩后继的实际 proper 力迫，`collapse_iteration_pil_l` 对任意可数种子给出共同
N 与完整区间引理。闭扩张及全阶段保持装配复用分配性层的 ω₁、旧可数性证明，
并复用 proper 层的 ω 共尾性和严格旧序数界证明，保留原来的同一规范嵌入。

力迫源码按[功能目录与构造脉络](../YesMetaZFC/Model/Forcing/INDEX.md)组织；目录职责与
公理审计切片分别维护。数学声明保持原命名空间，审计先检查全部力迫源文件均已登记。

力迫层的 `scripts/check_forcing.py` 审计 403 个生产模块、6727 条声明，包括名称泛型商、
内部基础公理、完整真值、任意地模型的 ZFC 保持、CH 塌缩、参数化 Cohen 添加、
CCC 基数保持、¬CH 模型及原推导核中的 CH 独立性。商载体、解释关系与隶属定义无
经典选择依赖。两侧模型的 Lean 公理依赖限制在 `propext`、`Quot.sound` 与 Prop 内
选择；CH、¬CH 及原固定公理均不再引入原生闭合性公理。
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
这些 ZF 端点继续单独核验；Lean 依赖上界仅为三项标准公理，不再允许原生句法证书；
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
端点继续单独核验，排除原生句法闭合性公理。
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
| 有界见证与局部规则 | [ObjectHornSemantics](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Arithmetic/ObjectHornSemantics.lean)；[PureSourceHorn](../YesMetaZFC/Model/ZFC/Pure/PureSourceHorn.lean) 的 `condition_agrees`、`localTest` | 递归前提读取同一候选集合；不假定其外部有限 |
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
| 无参数纯闭 Δ₀ 可决定 | [FunctionFreeDelta0](../YesMetaZFC/Logic/FirstOrder/FunctionFreeDelta0.lean) 的 `closed_decided` | 纯 ℒ 只有二元 ∈，没有常元、函数或零元关系 |
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
终点的准确参数见 [TROPHIES.md](TROPHIES.md)，反射链和编码格式见
[NAT_DECODING.md](NAT_DECODING.md)，公共证明入口见 [ENGINEERING.md](ENGINEERING.md)。
公理范围按本页开头列出的精确守卫及实际源码核验。

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
[ObjectCheckedReflection](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Arithmetic/ObjectCheckedReflection.lean) 的 `proof_valid` 以 Lean 内核核验原十二条规则：
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

[ObjectTarskiFixedPoint](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Arithmetic/ObjectTarskiFixedPoint.lean)
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

[ObjectParameterDiagonal](../YesMetaZFC/Logic/FirstOrder/FormalSystem/Arithmetic/ObjectParameterDiagonal.lean)
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

## 复跑核验

默认入口使用 `lake --wfail build`，全部独立模块使用
`python scripts/lean_cache.py build`；原生对象与库另加 `--native`。

- 生产端点的精确 Lean 公理依赖：`python scripts/check_axiom_decoupling.py`。
- 内部模型、HOD、司寇伦及 Łoś 的分层边界：`python scripts/check_internal_models.py`。
- 力迫模块及其公共依赖：`python scripts/check_forcing.py`。
- 算术、滤子、初等子结构与超幂分别使用 `scripts/check_arithmetic.py`、
  `scripts/check_filters.py`、`scripts/check_elementary.py`、`scripts/check_ultrapower.py`。

覆盖数量、耗时和成功状态以本次运行输出为准；记录结果时注明源码基点及检查范围。
