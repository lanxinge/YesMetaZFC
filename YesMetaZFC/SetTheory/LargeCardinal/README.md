# 武丁基数的对象定义

[Woodin](Woodin.lean) 固定标准的 Vδ 内 A-strong 刻画，来源为
[Welch，定义 4.5 与定理 4.6](https://people.maths.bris.ac.uk/~mapdw/Birkbeck-NDJFL.pdf#page=15)。
在通常 ZFC 背景下，δ 是武丁基数，当且仅当它不可达，且

\[
\forall A\subseteq V_\delta\ \exists\kappa<\delta\ \forall\nu<\delta\
\exists j:(V_\delta,\in,A)\prec(N,\in,B)
\]

满足 N 传递、N⊆Vδ、包含全部 δ 以下序数，crit(j)=κ、j(κ)>ν、Vν⊆N，
以及 A∩Vν=B∩Vν。临界点在选定 A 后固定，嵌入可以随 ν 变化。
这里的不可达明确为不可数、正则、强极限基数。

`Woodin_d`、`woodin_m` 分别为此条件的语义谓词和原一阶公式；
`woodin_sat_l` 已证明两者对应。`Wd_proper_d` 要求武丁基数在全部内部序数中无界，
与原句子 `Axioms.woodin_proper` 的对应由 `wd_proper_axiom_sat_l` 给出。
本模块未断言 ZFC 可以证明武丁基数存在。

[PredicateEmbedding](../../Model/SetTheory/Internal/PredicateEmbedding.lean) 将 (X,∈,A)
编码为二元关系 R(x,y)↔x∈y∨(x=y∧x∈A)。`spred_read_l` 核验对角线恢复 A、
非对角线恢复 ∈；内部语法具有独立的等号原子。`Spred_emb_d` 用实际函数图与
赋值复合比较原内部满足关系，量化全部内部公式码，允许非标准码。
`spred_exists_l`、`smap_assign_exists_l`、`spred_identity_l` 分别构造结构码、
赋值复合和恒等初等嵌入，均仅需 ZF。

## 已证明：武丁基数是可测基数的极限

[`woodin_measurable_above_l`](Measurable.lean) 在 ZF 中证明：若 δ 是武丁基数，
则对每个 α<δ，存在 α<κ<δ，κ 可测。`woodin_proper_measurables_l` 因而从
真类个武丁基数推出真类个可测基数。`Measurable_d` 与原公式 `measurable_m`
的语义对应已核验；其定义为不可数基数上的非主 κ 完备内部超滤。

[`wd_complete_ultrafilter_l`](MeasureCompleteness.lean) 在 ZF 背景中，从
`Woodin_d I δ` 和 α<δ 自动返回内部 ω、序数 κ 和集合 U，满足 ω<κ、α<κ<δ，
U 是 κ 上的极大适当滤子，不含单点集，且对全部内部 μ<κ 长族的交封闭。
短族和交集都是内部集合图；因此特别包含内部可数完备性。
`ed_cardinal_l` 用补单点集族排除更短序数枚举 κ，完成初始序数证明。
`Ed_complete_d κ D U` 区分长度界 κ 与滤子载体 D；`ed_complete_l` 对任意源载体 D
和合法种子 a∈j(D) 证明 κ 完备性。原可测基数证明已直接迁移到 D=κ 的实例。

证明链如下：

- [EmbeddingSource](../../Model/SetTheory/Internal/EmbeddingSource.lean) 把原公式编译为同一内部码，沿 j 复合赋值。
- [PredicateSource](../../Model/SetTheory/Internal/PredicateSource.lean) 用 R(x,y)∧¬R(y,x) 恢复真实隶属，给出完整原语言及背景 Δ₀ 保持。
- [DerivedFilter](DerivedFilter.lean) 在源中的实际子集代数上分离 U={s:a∈j(s)}，核验相对超滤性；完整幂集实例给出极大适当滤子。
- [CriticalMeasure](CriticalMeasure.lean) 用临界点逐点固定证明非主性；[CriticalOrdinal](CriticalOrdinal.lean) 排除有限临界点及 κ=ω。
- [CumulativeClosure](../CumulativeClosure.lean) 证明极限 V 层的幂集与有界关系图封闭；[MeasureCompleteness](MeasureCompleteness.lean) 据此容纳全部短族，传输其交集定义。

指定下界 α 时，选取 α<β<ν<δ，并把 β 本身作为谓词。
若临界点 κ≤α，则 κ∈β，其像 j(κ) 属于像谓词 B。B 的传递性迫使 β∈B，
而 ν-强性在 Vν 上给出 β∈β 的矛盾。因此得到 κ>α，整个无界性证明
使用带谓词语言的初等性，而非预设“武丁基数下方可测基数无界”。

## 派生测度族、协调与共同纤维

[MeasureFamily](MeasureFamily.lean) 的 `ef_family_exists_l` 同时收集全部种子处
唯一的派生集合，得到实际内部函数图。`ef_family_ultra_l` 验证合法种子处的超滤性。
`ed_projection_l` 对任何实际内部投影 p 证明：若 j(p)(b)=a，则
p⁻¹(A)∈U_b 当且仅当 A∈U_a；逆像本身也在证明中实际构造。

[TreeReflection](TreeReflection.lean) 的 `ed_branch_pull_l` 把目标载体中的像树分支
回拉到原载体。`wd_cover_embedding_l` 对 Vδ 中任何指定的实际集合，选择
覆盖它的 ν-强嵌入；不预设目标对外部序列封闭。

[FiberCompleteness](FiberCompleteness.lean) 的 `ef_common_fiber_l` 证明：任意内部层族 H，若第 n 层
只含 n 长 κ 值列，而且其逐层像具有一个 L 值共同纤维，则原层族也有 κ 值共同纤维。
三个条件 `Ef_levels_d`、`Ef_fiber_d`、`Ef_image_fiber_d` 均已接上原公式及语义对应。
证明回拉各层之并上的分支，再由函数定义域唯一性恢复精确层号；不只证明逐个超滤的可数完备性。

[FiniteSupport](FiniteSupport.lean) 将全部内部有限列 a:n→L 同时作为定义域，
实际构造唯一的函数图 F(a)=U_a，其中 U_a 是 κ^n 上种子 a 派生的测度。
`es_seed_l` 用全称量词的初等性证明 a∈j(κ^n)，包含目标中不在 j 的像内的支撑；
`es_family_ultra_l` 因而证明每个分量的适当超滤性质与 κ 完备性。
[SupportCompleteness](SupportCompleteness.lean) 的 `Es_fiber_d` 仅从 F 读取测度成员资格，
不以 j 为完备性条件的参数；其原公式与像共同纤维的等价都已证明。

[Composition](../InnerModel/Recursion/Composition.lean) 以 Δ₀ 公式刻画 t=s∘q，
在 KP 中构造实际复合与整个坐标重排函数 p；只需给定已实现的源、目标函数空间。
[SupportProjection](SupportProjection.lean) 证明临界点以下序数之间的内部函数被 j 固定，
并构造 p 及 j(p)，证明 j(p)(a)=a∘q。
[Coherence](Coherence.lean) 的 `Es_coherent_d` 与原公式 `es_coherent_m` 只读取 F：
若 b=a∘q，则 π_q⁻¹(A)∈U_a 当且仅当 A∈U_b，其中 π_q(s)=s∘q。
`es_coherent_l` 构造这个逆像并证明协调律。q 可以遗漏、重复或置换坐标，长度可以内部非标准。

[SupportConstruction](SupportConstruction.lean) 的 `woodin_components_l` 是统一入口：
对任意谓词 A⊆Vδ，先固定 κ，再对每个 L<δ（ω⊆L）返回上述实际有限支撑测度图、全部分量的 κ 完备超滤证书，
以及由 F 自身表述的坐标协调律和共同纤维完备性。它先用有限次幂集容器统一覆盖 L 上所有关系图，
再选择强嵌入，故所有有限支撑与完整对局同时进入目标，构造仍仅需 ZF。
对每个分量，它还自动构造任意非空载体 Q 上、任意关系 R 的内部商结构。
这里明确返回全部背景内部 D→Q 函数组成的集合，Q 的秩没有 Vδ 上界。

[ReducedPower](../../Model/SetTheory/Internal/ReducedPower.lean) 的通用构造处理实际代表函数族，
`rp_family_model_l` 将候选函数限制在指定集合内，已用于源模型内部函数族。
`Rp_eq_d` 的等价性和 `Rp_rel_d` 的代表元替换不变性已证明；等价类、投影图、商关系及
结构码都实际构造，`rp_kernel_l` 精确识别类相等。这些构造仅需 ZF 与含载体、
成员有界且具有有限交共同细化的集合族 `Base_d`，
不选择代表元，也不要求 j 作用于代表函数。

[Filter/Relative](../Filter/Relative.lean) 的 `Rel_ultra_d` 只在指定子集代数内向上封闭及二择。
[Filter/Source](../Filter/Source.lean) 在 KP 中从已有 rudimentary 闭包构造源内部子集代数
P={A∈X:A⊆D}，并构造 X 内的常值代表函数。
[SourceMeasure](SourceMeasure.lean) 的 `ed_source_model_l` 在 ZF 中从实际初等嵌入自动得到
P 上的派生超滤、精确代表族 G={f∈X:f:D→X}、源隶属结构与分量商结构。
该构造不要求 X 包含背景中的全部 D 子集或全部 D→X 函数。

[Internal/Collapse](../../Model/SetTheory/Internal/Collapse.lean) 对实际 Mostowski 正逆图
证明全部内部公式码的初等性；[ElementaryHull](../../Model/SetTheory/Internal/ElementaryHull.lean)
的 `selem_hull_collapse_l` 从任意传递隶属结构及可数种子，自动构造可数传递模型和返回原结构的
完整内部初等嵌入。已有 J 层可数凝聚入口也已迁移。`Smap_d.models_l` 保持已给出的内部编码理论，
但尚不能把外部标准 ZF 模式直接当作覆盖全部非标准公式码的模型性。

[SeparationCode](../../Model/SetTheory/Internal/SeparationCode.lean) 构造任意内部公式的分离实例代码。
新参数坐标从实际有限支撑之外取得，因而没有变量捕获；公式可以内部非标准。
[Separation](../../Model/SetTheory/Internal/Separation.lean) 的 `smap_separation_l` 仅要求目标含有
像集合的全部子集，在 ZF 中回拉源内的实际分离集。
[SeparationHull](../../Model/SetTheory/Internal/SeparationHull.lean) 的 `v_separation_hull_l` 从极限 V 层
和可数种子，自动得到保留种子原像、具有全内部公式码分离的可数传递模型。
[CollectionCode](../../Model/SetTheory/Internal/CollectionCode.lean) 同时构造逐点存在和收集结论的内部代码。
[Collection](../../Model/SetTheory/Internal/Collection.lean) 在正则 H(χ) 中用实际小见证集证明收集，
并沿初等嵌入回拉源内见证集。[UniformizationCode](../../Model/SetTheory/Internal/UniformizationCode.lean)
把函数图条件和原公式组合为完整内部统一化代码；[Uniformization](../../Model/SetTheory/Internal/Uniformization.lean)
利用 H(χ) 的乘积和子集封闭，回拉实际属于源的统一见证函数及值域界。
[UniformizationHull](../../Model/SetTheory/Internal/UniformizationHull.lean) 的 `h_uniform_hull_l`
自动选择正则 H(χ) 环境，再从可数种子构造同时具有全部内部码分离、收集与统一化的
可数传递模型；统一化两个实参的变量坐标不同。

[Pointwise](../../Model/SetTheory/Internal/Pointwise.lean) 的 `pe_compile_l` 对任意内部程序
构造代表函数逐点解释的代码，并返回覆盖全部旧行的实际翻译表。原子用有界公式读取函数值，
存在量词在实际源内部函数域量化；[UniformizationSource](../../Model/SetTheory/Internal/UniformizationSource.lean)
构造源内常值函数及源内值域界，保证对象见证与函数见证对应。程序长度归纳使用真实原公式，
覆盖非标准代码，不调用外部有限列表递归。
[PointwiseTrace](../../Model/SetTheory/Internal/PointwiseTrace.lean) 的 `sc_pe_trace_l`
将这一翻译接入源内分离，实际构造指定代表函数赋值的真值逆像 A∈X。
逐点对象赋值也由唯一值收集构造；给定实际源理论后，逐点解释和源内真值集只需 ZF。

[PointwiseWitness](../../Model/SetTheory/Internal/PointwiseWitness.lean) 的 `sc_pe_witness_l`
在源中集合 A 上把逐点存在见证统一成一个 D 上的源内代表。先对翻译码统一选取函数值，
再由 [PointwiseDiagonal](../../Model/SetTheory/Internal/PointwiseDiagonal.lean) 的 `sc_diagonal_l`
构造 h(p)=gₚ(p)，在 D∖A 上取源中基点；函数图和值域界都属于源。
[ReducedPower/SourceLos](../../Model/SetTheory/Internal/ReducedPower/SourceLos.lean) 的 `rs_los_l`
在真实原公式 `rs_los_m` 上完成全部内部行的归纳。或非明确使用源内真值逆像，
存在步使用上述实际统一代表。此定理消费传递源的 `Sc_theory_d`；正则 H(χ) 及其传递初等后继均有实际实例。
[SourceSatisfaction](../../Model/SetTheory/Internal/ReducedPower/SourceSatisfaction.lean) 的 `rs_satisfies_l`
给出统一满足关系上的源内部 Łoś，`rs_los_assignment_l` 从实际 ω→G 代表赋值图
自动构造赋值空间、商赋值及全部内部代码集；G 精确为源中的 D→X 函数。
源内部 Łoś 与常值初等嵌入只需 ZF；分量间的完整初等映射另用 ZFC 选择商赋值的代表。

[ReducedPower/Constant](../../Model/SetTheory/Internal/ReducedPower/Constant.lean) 的 `rs_constant_embedding_l`
实际收集源内常值函数，构造 x↦[cₓ] 的完整内部初等嵌入，并返回其精确代表方程。
[ReducedPower/Projection](../../Model/SetTheory/Internal/ReducedPower/Projection.lean) 的 `rs_projection_embedding_l`
从实际 t:D₁→D₀ 与测度投影方程构造 [f]↦[f∘t]；复合函数图属于源，映射精确保持、
反映代表等价，并保持全部内部代码。源内逆像与相等集的构造仅用 ZF。
[ProjectionLaws](../../Model/SetTheory/Internal/ReducedPower/ProjectionLaws.lean) 核验恒等、复合和
常值交换律；这些图方程只读取既有证书，不需要额外集合公理。

[SourceProjection](SourceProjection.lean) 的 `es_source_projection_l` 是有限支撑入口：从已有
`Es_coherent_d`、对应分量超滤及源中的坐标数据，自动生成源子集代数、限制超滤、
真实坐标投影、两侧源内部超幂、两个常值初等嵌入和一个分量初等映射，并返回交换方程。
原超滤与限制超滤的精确成员对应、常值嵌入的代表方程也作为结论保留，供后续良基性与极限构造使用。
坐标函数只要求是实际函数图，允许重复、遗漏和置换。坐标层的恒等与反向复合
另由 `cp0_projection_id_l`、`cp0_projection_comp_l` 核验，可直接接入商层复合律。

[DirectedSystem](../../Model/SetTheory/Internal/DirectedSystem.lean) 用内部索引、标签图及过渡图
表示任意集合大小的定向关系嵌入系统。在 ZF 中构造规范商、极限关系、分量嵌入、
非空极限的结构码及关系保持映射的唯一分解。`di_sigma_wf_l` 在 ZF＋DC 中证明
可数定向系统的良基极限；`di_cone_wf_l` 在 ZF 中从实际良基目标的相容锥推得良基性。
任意定向子结构族及幂集索引族均有自动构造的实例。这里的“可数定向”要求每个
内部 ω 指标族有共同上界，不能用有限支撑系统通常具有的有限定向性替代。

[ComponentWellFounded](ComponentWellFounded.lean) 的 `rp_wf_l` 在 ZF＋DC 下，
从完整滤子的可数交性质证明任意源函数族的关系商内部良基。
完整真值集合由背景分离构造；源超滤只须包含于原滤子，不要求源拥有这些背景集合。
[WellFoundedComponents](WellFoundedComponents.lean) 的 `woodin_wf_components_l`
已将它接入实际武丁测度族：自动构造全部良基分量，并保留原协调与共同纤维性质。
此处没有把分量良基性当成整个有限支撑极限的良基性，也没有让原嵌入作用于高秩代表。

## 已证明：有限支撑全系统与整个良基极限

[ExtenderSystem](ExtenderSystem.lean) 的 `ep_system_exists_l` 实际构造全部分量模型图、
带支撑标签的载体、过渡图和分量关系，并核验恒等、复合、单射及关系保持与反映。
索引为全部内部有限单射坐标列，允许置换和非标准有限长度；
`ep_support_cover_l` 证明任意有限坐标列（包括重复坐标）都可投影到某个索引。
每个分量的代表族精确为 `G_n={f∈X:f:κ^n→X}`。
[ExtenderComponents](ExtenderComponents.lean) 利用分量结构码的唯一性和替代一次收集模型图；
[ExtenderGraphs](ExtenderGraphs.lean) 利用类均为 X 的子集给出统一集合界，再分离全部过渡。
[ExtenderSource](ExtenderSource.lean) 的 `ep_source_exists_l` 自动构造包含所需参数的实际正则 H(χ) 源，
已有源内分离与统一化接口提供坐标投影及函数拉回，系统装配的背景为 ZFC。

[JointFiber](JointFiber.lean) 的 `es_joint_fiber_l` 在 ZF 中把共同纤维性质转为任意
内部可数有限支撑约束族的同时实现。先将全部出现的坐标嵌入一条单射 ω 列，
再在每个有限前缀上取有限多个测度约束的交；一个共同纤维便同时满足全部约束。
支撑长度可以无界，统一求值与坐标投影交换。

[ExtenderWellFounded](ExtenderWellFounded.lean) 的 `ep_limit_wf_l` 只用 ZF＋DC 证明整个极限内部良基。
反设有内部下降链，先取指标递增的代表节点链及一张源代表函数图；
把每一步下降改写为较后分量上的测度约束，实际收集约束族，调用共同纤维统一求值，
最终得到源关系中的内部下降链，违反源良基性。
此处消费实际共同纤维性质，不要求有限支撑索引族可数定向。

[ExtenderLimit](ExtenderLimit.lean) 的 `ep_limit_exists_l` 返回完整系统、实际商极限、
结构码、良基性、完整内部初等性及传递坍塌。通用短扩展器仍可作用于任意实际 `Ep_source_d`。

## 已证明：完整内部初等性、坍塌及原嵌入因子

[DirectedSystem/Elementary](../../Model/SetTheory/Internal/DirectedSystem/Elementary.lean)
的 `di_elementary_limit_l` 在 ZF 中，对任意实际初等过渡系统构造分量到极限的完整 `Smap_d`。
归纳量化全部阶段与赋值；存在量词的反向步骤把当前阶段与见证的阶段推到共同后继，
再用过渡的完整初等性回拉。仅用有限定向性，公式码可以内部非标准。
[ReducedPower/Restriction](../../Model/SetTheory/Internal/ReducedPower/Restriction.lean)
证明将完整测度限制到源内子集代数保持同一个类集合、商图及结构码；
[ExtenderElementary](ExtenderElementary.lean) 据此把现有过渡图升级为完整内部初等映射。
[ExtenderConstant](ExtenderConstant.lean) 构造源到整个极限的常值初等嵌入及精确代表方程。

[Internal/Extensionality](../../Model/SetTheory/Internal/Extensionality.lean)
用真正的内部等号指令编译外延性句子，证明完整初等嵌入将关系外延性传到目标。
[Collapse/RelationIso](../Collapse/RelationIso.lean) 在 ZF 中对良基外延关系构造传递坍塌同构；
[ExtenderCollapse](ExtenderCollapse.lean) 因而返回整体坍塌及逆图的完整内部初等性，
并得到源到传递目标的完整内部初等嵌入。

[InaccessibleHierarchy](../InaccessibleHierarchy.lean) 在 ZFC 中证明不可达 δ 以下的 Vα 具有实际较小序数单射界，
进而证明 Hδ＝Vδ。[ExtenderRankSource](ExtenderRankSource.lean) 直接构造 Vδ 的源实例。
[DerivedEvaluation](DerivedEvaluation.lean) 证明原求值 j(f)(a) 精确识别商等号及成员关系；
[ExtenderFactor](ExtenderFactor.lean) 装配全部求值并下降为整个极限到原目标的实际关系嵌入。
其图方程保留每一个类代表，尚未断言该因子到原目标的完整初等性。

自动入口 [`woodin_extender_l`](ExtenderDerivedLimit.lean) 已迁移到上述 Vδ 源，
返回同一个系统的完整初等极限、传递坍塌和原目标因子 `Ep_derived_limit_d`。
原 j 因此只作用于已经证明属于 Vδ 的代表。

## 已证明：传递后继继续作为源

[ExtenderSource](ExtenderSource.lean) 的 `Ep_source_d.successor_l` 在 ZF 中证明：
若 X 是实际源，j:X→N 为完整内部初等嵌入，N 传递，则每个 κ′∈N、ω⊆κ′
都实际得到 K′∈N 和 `Ep_source_d ω κ′ K′ N W`。κ′ 可以不在 j 的像中。
`Ep_source_d` 已统一改为源自身满足的全内部分离、统一化、有限序列空间与关系塌缩证书；
源内 Łoś、常值、复合、投影和全部有限支撑消费者均使用该接口。

[UniversalClosure](../../Model/SetTheory/Internal/UniversalClosure.lean) 用实际原公式归纳
构造任意非标准内部程序的全称闭包，`Smap_d.valid_l` 传输全部赋值上的有效性，
`Smap_d.models_forward_l` 正向保持任意已编码理论。
[SourceTheory](../../Model/SetTheory/Internal/SourceTheory.lean) 据此保持分离与统一化，覆盖 N 的全部新参数。
[EmbeddingOmega](../../Model/SetTheory/Internal/EmbeddingOmega.lean) 证明 j(ω)=ω；
[SourceFinite](../../Model/SetTheory/Internal/SourceFinite.lean) 用内部归纳证明 N 包含全部背景内部有限函数。
[SourceSequences](../../Model/SetTheory/Internal/SourceSequences.lean) 再把相对序列空间识别为真实全部有限序列空间。
[SourceCollapse](../../Model/SetTheory/Internal/SourceCollapse.lean) 传输整条塌缩存在句子，
覆盖目标中的任意相对良基关系；相对良基性只量化目标模型自身的子集。

初始正则 Hχ 的理论和全部字母表序列空间分别由 `sc_h_theory_l` 与
[HereditarySequences](../HereditarySequences.lean) 的 `ZFC.h_fseq_l` 在 ZFC 中构造，
实际 Vδ 源复用 Hδ＝Vδ。`ep_collapse_l` 已把下一步源证书直接附在同一个传递坍塌 N 上，
因此 `Ex_short_d.limit_l`、`woodin_extender_l` 与秩强性入口的坍塌结果自动保留它。
初始塌缩闭包由 [HereditaryCollapse](../HereditaryCollapse.lean) 与 `sc_h_collapse_l`
实际证明：Hχ 包含其元素的全部实际子集，关系的塌缩像大小不超过载体，图属于相应乘积。
此结论保证后继模型可复用现有源内部超幂构造；下一扩展器的可迭代性仍须另证。

## 已证明：跨模型施加与双映射复制

[ExtenderRelative](ExtenderRelative.lean) 的 `Em_source_d` 与 `Ec_source_d` 只要求
测度决定施加源中的子集，并在这些子集上协调。`Ea_agree_d` 精确表示两个模型
在全部内部有限 κ 幂的子集上相同。原分量、过渡、初等极限和坍塌构造已直接消费
相对接口；完整测度族由 `Em_family_d.source_l` 给出实例。
[ExtenderUltrapower](ExtenderUltrapower.lean) 的 `ep_apply_l` 由子集一致性自动构造
另一源上的整个内部超幂，代表始终是该源中的实际函数。

[ExtenderCopy](ExtenderCopy.lean) 的 `ep_copy_l` 对施加源之间的 π 和所属模型之间的 σ，
在 σ(F)=F′、σ(L)=L′、π(κ)=κ′ 及两图在相关源子集上一致时，构造
τ([a,f])=[σ(a),π(f)]。它保持全部内部公式码，满足 τ∘i_F=i_F′∘π，
由该代表方程唯一确定，并从目标超幂良基性推出原超幂良基性。
`ep_copy_identity_l` 在同一个超幂上证明两张恒等原图诱导恒等复制。

[SourceTransport](../../Model/SetTheory/Internal/SourceTransport.lean) 对所有模型统一编译
逐点解释码；[ReducedPower/Copy](../../Model/SetTheory/Internal/ReducedPower/Copy.lean)
据两侧源内部 Łoś 证明分量复制的完整初等性。
[DirectedSystem/FiniteCover](../../Model/SetTheory/Internal/DirectedSystem/FiniteCover.lean)
仅在 ZF 中作内部有限归纳，随后唯一收集共同分量中的代表；
[ElementaryFactor](../../Model/SetTheory/Internal/DirectedSystem/ElementaryFactor.lean)
由此在 ZF 中证明任意完整初等锥的唯一因子仍完整初等。
分量复制的商赋值代表选择与整个系统装配仍按 ZFC 边界提供。

[ExtenderCopyApplication](ExtenderCopyApplication.lean) 的 `ep_copy_apply_l` 同时构造
两侧施加系统、超幂及复制图。`ep_owned_copy_l` 从已有完整测度族自动构造
包含 F、L 的所属模型 N，再构造 N∈X 的施加源，返回子集一致性、实际恒等原图
和对应的完整复制。正则 Hχ 的大小在这里用于产生初始实例；通用复制定理
消费任意已有的相对源及实际初等图。迭代树后继构造见 [Iteration](Iteration.lean)；
非平凡迭代的可迭代性仍待证明。

## 已证明：后继子集一致性与复制的支撑保持

[ExtenderSuccessor](ExtenderSuccessor.lean) 的 `ep_successor_agree_l` 证明：同一个 F
作用于 `Ea_agree_d ω κ X Y` 的两源，若 κ、L 为序数且两侧已实际传递坍塌，
则 L 本身属于两侧后继 N、N′，且 `Ea_agree_d ω L N N′`。
这里量化全部内部自然数 m 以及 Lᵐ 的全部背景子集，包含原接口遗漏的支撑端点。
`Ea_agree_d.mono_l` 自动推出任意子字母表 μ⊆L 上的一致性。
输入只消费相对测度、源内协调与正规性、坐标原子及实际坍塌，不要求原派生嵌入。

证明的关键是两个识别。[ExtenderSeedNormal](ExtenderSeedNormal.lean) 用源内正规性
排除坐标类的额外前驱，[ExtenderSeedCollapse](ExtenderSeedCollapse.lean) 再以原公式成员
归纳证明坐标 α 的坍塌值就是 α。[ExtenderSupportBound](ExtenderSupportBound.lean)
把常值 κ 与任意坐标移到共同支撑，证明 L⊆j(κ)，并由序数比较得到 L∈N。
[ExtenderValueBound](ExtenderValueBound.lean) 以常值 κ 的像作界，把 A⊆Lᵐ
的代表逐点正规化为 κᵐ 的子集；[ExtenderSetCode](ExtenderSetCode.lean) 用坐标拼接
编码整张成员图，在另一源重建同一代表。[ExtenderTupleValue](ExtenderTupleValue.lean)
识别有限坐标列的坍塌值，[ExtenderSetTransfer](ExtenderSetTransfer.lean) 比较完整支撑中的
有限列成员资格。最后在目标内的实际 L 值有限列空间中分离其迹，恢复同一个 A；
不把 L 当成支撑中的一个坐标。原严格界证明已直接迁移，投影和列长度保留内部表示。

[ExtenderSuccessorApplication](ExtenderSuccessorApplication.lean) 的 `Ex_short_d.successors_l`
实际构造两侧传递后继，保留绑定原系统与坍塌的 `Ep_successor_d` 证书，返回上述一致性；
对每个 ω⊆μ、μ∈L 或 μ=L，还自动返回两侧的下一步源证书。
[ExtenderCopyCollapse](ExtenderCopyCollapse.lean) 在同一原复制图上共轭两侧坍塌，
证明所得完整初等图 k 满足 k↾L=σ↾L，并保留精确共轭方程。
[ExtenderCopySuccessor](ExtenderCopySuccessor.lean) 的 `ep_copy_successors_l` 自动构造这些对象；
原侧只需预扩展器，目标侧的可数共同纤维经复制回传原侧良基性。
其结果还包含两侧支撑端点的成员资格，以及同一个复制图的小传递域限制恢复结论。
这两个入口产出的条件已接入下面的迭代树后继构造。

## 已证明：实际迭代树及后继扩张

[IterationTree](IterationTree.lean) 的 `It_tree_d` 保存对象模型内部的树序 T、模型码列 Q、
完整初等嵌入列 G 和操作列 E。长度为任意内部序数。树序以自反闭包存储，
严格边沿序数递增，每个结点的前驱构成链，序数后继有树前驱，极限的前驱共尾。
模型均为已实现的传递源；已有极限结点要求被严格前驱的嵌入像覆盖。
结构遵循 [Neeman 定义 1.24–1.25](https://www.math.ucla.edu/~ineeman/detLR.pdf/#page=16)。

`It_local_d` 使用所属模型内对原 `ex_short_m` 的满足关系；`it_local_short_l` 将该模型内
实际的 `Ex_short_d` 接入这个判断。活动步从当前结点 ξ 读取 F，施加到其树前驱 k 的源，
并保留所需的有限 κ 幂子集一致性。`It_ultra_d` 把边 j 与同一个源内部超幂、常值图、
整个商极限和传递坍塌绑定。操作记录用空集标记 pad，用实际有序对保存 κ、L、F。

[IterationTreeExtend](IterationTreeExtend.lean) 的 `it_tree_extend_l` 实际添加整个后继列：
新结点 α 可以接到任意 k<α；新增祖先嵌入为 j∘jᵢ,ₖ，新对角线为恒等图。
[IterationNextMaps](IterationNextMaps.lean) 用替代统一收集这些图；
[IterationDiagramExtend](IterationDiagramExtend.lean) 证明全部交换三角形，
随后保持旧操作、旧模型和已有极限条件。树序添枝与操作列添加只需 KP；
复合图唯一性只需外延性，其余一般扩张装配只需 ZF。

[IterationRoot](IterationRoot.lean) 的 `it_root_l` 和 `it_pad_l` 给出实际单根树与恒等延长。
[IterationApply](IterationApply.lean) 的 `it_apply_l` 直接消费现有 `Ep_limit_d`，构造新模型和
超幂边，再调用整树扩张；`it_short_apply_l` 进一步从背景短扩展器的共同纤维自动构造该极限。
模型内的短扩展器判断本身不保证背景中的良基性，一般入口保留实际良基超幂证书。
[IterationAgreement](IterationAgreement.lean) 的 `it_short_apply_agree_l` 同时构造所属模型的
超幂，证明它与树中新加入的同一个模型在每个 μ∈L 的有限幂子集上一致，并返回下一步源。

[IterationLimit](IterationLimit.lean) 的 `it_branch_limit_l` 将上述极限覆盖条件实现为实际
`Di_system_d` 与 `Di_limit_d`：前驱的嵌入像组成带指标定向系统，取值图实现同一目标。
[IterationFork](IterationFork.lean) 的 `it_fork_l` 从给定的合法短扩展器自动构造三结点树
0→1、0→2，并证明两个后继不可比较；第一步为 pad，第二步为实际扩展器施加。

## 已证明：极限添枝与共尾良基分支判据

[IterationBranch](IterationBranch.lean) 的 `It_branch_d` 是向下封闭的共尾链。
[IterationTag](IterationTag.lean)、[IterationSystem](IterationSystem.lean) 从原 Q、G 实际构造
带标号并 `(i,x)` 及全部过渡图；[IterationDirectLimit](IterationDirectLimit.lean) 构造真实集合商，
并证明每个原模型到商的规范图保持全部内部公式码。这里不预设新的极限模型。

[IterationLimitModel](IterationLimitModel.lean) 从商的内部良基性构造传递坍塌、新源证书和整列
规范初等嵌入。各腿由同一个代表公式唯一定义并经替代收集，不选择商类代表。
[IterationBranchExtend](IterationBranchExtend.lean) 的 `it_wf_branch_extend_l` 自动添入极限顶点，
其严格前驱恰为 B；旧模型、旧嵌入及操作列保持。输出 `It_limit_extension_d` 同时保存原带标号
系统和新模型的 `Di_limit_d`，因而新模型、嵌入和直接极限是同一次构造的对象。
树序添枝只需 KP；商、坍塌与完整扩张只需 ZF。

已实现的良基性及选枝入口如下：

| 入口 | 数学条件与结论 |
| --- | --- |
| `it_sigma_branch_l`、`it_sigma_extend_l` | ZF＋DC；给定共尾枝 B 和 ω<cf(α)。任意内部可数指标族被枝上某阶段控制，故原隶属分量的良基性传到直接极限，并自动添枝。 |
| `it_cofinal_branch_l` | ZF；给定内部 ω 共尾序列，每个结点都有任意高的树后继。沿最小后继作确定递归，实际构造经过指定起点的共尾枝。 |
| `it_realized_branch_l` | ZF；给定非空共尾枝及实际相容映射列到内部良基目标。只要求函数保持成员关系并交换，不要求这些腿单射、满射或初等；直接极限良基。 |
| `it_pruned_extend_l` | 结合实际选枝与相容实现：从可延伸树及其相容良基实现，自动选出共尾良基枝并完成极限扩张。 |
| `it_padding_limit_l`、`it_padding_pruned_l` | 从已有真实源构造任意内部极限长度的 padding 树，实际调用同一商、坍塌、选枝与添枝接口，给出参数实例。 |

这些条件均在定理签名中明示。后继模型逐个良基不足以替代极限处的论证；一般
共尾分支假说的范围与反例可参见 [Neeman–Steel](https://math.berkeley.edu/~steel/papers/cbhcounter.pdf)。
本项目的 AD 路线所需目标是 [Neeman《Determinacy in L(R)》定理 2.3、推论 2.4](https://www.math.ucla.edu/~ineeman/detLR.pdf#page=19)：
对可数模型到 Vθ 的初等嵌入，nice 的 ω 长迭代树具有共尾枝，且枝模型仍能初等嵌回 Vθ；
由此获得证明所需的弱迭代性。该目标尚未完成，也未以任意树的无条件选枝取代它。

## 已证明：小传递模型的编码与跨源还原

[RelationBounded](../Collapse/RelationBounded.lean) 的 `Wc_iso_d` 用 Δ₀ 证书描述
关系载体到传递集合的实际双射。其关系外延性只需背景外延性，关系良基性只需 KP；
传递像唯一性复用原 ZF 关系递归。`Sc_collapse_d` 的 Hχ 实例和完整初等后继保持
已接入所有 `Ep_source_d` 构造，因而每次实际后继继续具有内部塌缩能力。

[ExtenderRelationCode](ExtenderRelationCode.lean) 把 κ 上的二元关系编码为二项 κ 值列的集合，
再由 `Ea_agree_d` 搬运并在目标内还原原关系。
[ExtenderModelCode](ExtenderModelCode.lean) 的 `Ea_agree_d.transitive_l` 给出自动端点：
若两源的有限 κ 幂子集一致，B 传递，且源 X 内有实际双射图 F:κ→B，
则 B 属于另一源 Y。关系码、目标内塌缩及其与原 B 的相等全部在证明中构造；
不另要求调用者给出关系码、外延性或良基性。该端点及编码只需 ZF，
初始正则 Hχ 的闭包实例单独使用 ZFC。

这为 Neeman 引理 2.8 最后的小模型编码步骤提供实际还原接口。

## 已证明：可数复制的秩段限制恢复

[EmbeddingSmallRestriction](EmbeddingSmallRestriction.lean) 的 `smap_small_restriction_l`
证明：若 f:κ→B 是源内实际双射、B 传递，且目标 Y 已有 j↾κ，
则 B 属于 Y，并在 Y 中构造整张 j↾B。证明先将 B 的关系码的像沿 j↾κ 回拉，
再在 Y 中作 Mostowski 塌缩；图唯一性还原 f 后，按 j(f)(j(α)) 逐项构造限制。

[EmbeddingCountableBound](EmbeddingCountableBound.lean) 用模型内对旧嵌入 σ 的可数编号
实际收集 ω→φ 的第二坐标图，再由内部不可数共尾性取得 μ<φ；
[EmbeddingOrdinal](../../Model/SetTheory/Internal/EmbeddingOrdinal.lean) 的序数不下降性同时界住首坐标。
所用 `Sc_omega_bound_d` 只要求模型内每张 ω→φ 图有严格界，弱于完整不可达性。
[SourceOmegaBound](../../Model/SetTheory/Internal/SourceOmegaBound.lean) 已从实际正则基数给出实例，
并沿完整初等图双向传输这条句子，覆盖目标中的新函数。

[ExtenderCopyRestriction](ExtenderCopyRestriction.lean) 的 `ep_copy_countable_restriction_l`
因此只需 φ 以下逐层的有限幂一致性：自动取小界、分离并搬运 σ↾κ，
利用实际复制的支撑保持识别 j↾κ，再恢复整个已枚举传递域 B 上的复制限制图。
可数性由模型内真实的 σ→ω 单射图见证；一般入口的枚举同样是源内真实双射。
[InaccessibleEnumeration](../InaccessibleEnumeration.lean) 实际证明 |Vκ|=κ；
[EmbeddingRankRestriction](EmbeddingRankRestriction.lean) 在正则 Hχ 源中自动构造该枚举，
给出不再输入枚举的不可达秩段实例，Vδ 源通过 Hδ=Vδ 使用同一实例。
通用恢复、可数小界与共尾性传输只需 ZF；不可达枚举的构造单独使用 ZFC。

这些是 Neeman 引理 2.8、断言 2.9 所需的编码与限制恢复步骤。

## 已证明：相对秩层装配与源内树枝

[CumulativeRelativeAlgebra](../CumulativeRelativeAlgebra.lean) 对原历史公式作内部成员归纳，
证明同一传递载体中的相对 Vα 唯一且传递。全程只比较载体中的子集。
[SourceHierarchy](../../Model/SetTheory/Internal/SourceHierarchy.lean) 从极限 Vδ 实际提供
全部序数处的相对层，并沿完整初等嵌入传输全称存在句子，覆盖目标中的新序数。
层级闭包单独保留，未加入一般 Hχ 的源条件。
[RelativeRankSegment](RelativeRankSegment.lean) 的 `ep_relative_rank_l` 在初始 Vδ 中
从不可达 κ 自动构造相对秩层及源内 κ 枚举。`Er_level_d.map_l` 将递归历史和枚举的
有界塌缩证书一起传输；其像可直接调用 `Er_level_d.restriction_l` 恢复整层限制，
无需把像序数当成背景中的不可达基数。

[SourceCollapse](../../Model/SetTheory/Internal/SourceCollapse.lean) 的闭包现覆盖任意良基关系，
不再限于外延关系；`Wc_map_d` 的 Δ₀ 证书在 KP 下反映背景良基性。
[SourceBranch](../../Model/SetTheory/Internal/SourceBranch.lean) 从正则 Hχ 构造实际可数枝闭包，
再传到每个初等后继。`Sc_collapse_d.wf_absolute_l` 与 `sc_branch_absolute_l` 因而给出
良基性和存在可数下降链的绝对性，源条件的全部初始、改参和后继构造已经迁移。

[ExtenderTreeBranch](ExtenderTreeBranch.lean) 的 `Ep_source_d.tree_branch_l` 对任意源内字母表 A、
源内前缀树 T⊆A^{<ω} 和外部存在的分支，实际返回源内的 ω→A 分支图。
证明在源内分离子边，取得下降节点列，收集其全部前缀，再逐坐标统一化；
没有把节点列当作最终分支，也不要求内部 ω 外部标准。
该端点仅需 ZF 和实际源证书；初始 Hχ 的可数枝闭包单独使用 ZFC。

**尚未完成的边界：**还须把完整初等嵌入要求及规定的秩段限制编码为源内尝试树，
并从其源内枝恢复满足断言 2.10 的嵌入；随后在相应模型内构造带小枚举的 Skolem 壳，
完成 Pₙ₊₁∈Pₙ 的逐步装配及内部递归。这里没有把上述嵌入或递降步骤作为假设包装成结论；
Neeman 定理 2.3、推论 2.4 的完整弱迭代性仍未得到。

## 已证明：按指定秩选长并恢复强性

[`woodin_rank_strength_l`](WoodinStrength.lean) 在 ZFC 中对每个 A⊆Vδ 固定 κ，
对每个 ν<δ 自动选择 κ,ν<L<δ 的短扩展器。`Ep_strong_limit_d` 将强性证书
绑定到这张 F 的同一个全系统和商投影；其传递实现 N 及嵌入 i 满足：

- i:(Vδ,∈,A)≺(N,∈,B)，初等性覆盖全部内部公式码，包括非标准码。
- crit(i)=κ，L≤i(κ)，Vν⊆N，A∩Vν=B∩Vν。
- 原嵌入分解为 j=k∘i；k 的像精确为全部有限支撑求值 j(f)(a)，且 k 逐点固定 Vν。

[ExtenderCoordinates](ExtenderCoordinates.lean) 先由坐标代表覆盖所有 α<L，
[ExtenderLength](ExtenderLength.lean) 据传递坍塌固定性恢复临界点与长度界。
秩覆盖则使用实际枚举，而非只由序数固定性推断：
[RankLength](RankLength.lean) 将 Vν 的一个小序数枚举及其整张图放进 V_L；
[CumulativeRelative](../CumulativeRelative.lean) 与 [RankTransport](RankTransport.lean)
比较相对累积历史，在原目标已经覆盖 Vν 时恢复真实 Vν。
[RankEnumeration](RankEnumeration.lean) 同时构造源中各 Vα 的最小序数枚举。
其最小性把目标 ν 层所需索引压到 L 以下；[RankCover](RankCover.lean)
用两个有限坐标表示每个 x∈Vν，并将它送入同一个极限。

谓词初等性另由完整 Łoś 证明。[HereditaryFunction](../HereditaryFunction.lean)
先证明正则 Hδ 对小定义域函数封闭，再以 Hδ=Vδ 核验原代表族确已包含全部所需函数。
[FullEmbedding](../../Model/SetTheory/Internal/ReducedPower/FullEmbedding.lean)
给出任意关系下的完整常值与投影初等性；[DerivedPredicate](DerivedPredicate.lean)
识别原嵌入的谓词原子。[ExtenderPredicateLimit](ExtenderPredicateLimit.lean)
沿原过渡图装配全部内部公式码的初等性；[ExtenderStrength](ExtenderStrength.lean)
将它传到同一个传递实现，并由原因子的逆像构造 B。
此处源为实际 Vδ；一般初等子源仍使用源内部 Łoś，不能未经闭性证明更换代表族。

长度随 ν 选择。当前端点恢复上述秩覆盖和谓词强性；它没有断言任意较短截断保留
原嵌入的全部强度，也尚未包装成带 N⊆Vδ、δ⊆N 全部字段的 `Wd_witness_d`。

## 已证明：通用短扩展器与武丁实例的识别

公共入口为 [Extender](Extender.lean)。[ExtenderShort](ExtenderShort.lean) 的 `Ex_pre_d`
刻画有限列表示中的实际预扩展器：临界点 κ 为不可数基数，长度 L>κ，F 是实际函数图，
其分量超滤 κ 完备，满足坐标协调、等号与序关系、正规性和临界点种子条件。
`Ex_short_d` 另加入共同纤维的可数完备性。定义只读取 F；
[ExtenderSyntax](ExtenderSyntax.lean) 的 `ex_pre_m`、`ex_short_m` 及语义定理已接通原一阶语言，
量词包含模型内全部有限长度和实际层族。

[ExtenderNormal](ExtenderNormal.lean) 的 `es_normal_l` 在 ZF 中证明正规性：
若 f(s)<s(i) 在 U_a 上几乎处处成立，则 β=j(f)(a)<a(i)；把 β 添加到 a 的末尾，
实际分离测度一集合，使 f(s↾n)=s(n)。此处 f:κ^n→κ 已证明属于原嵌入的定义域。
[ExtenderSeeds](ExtenderSeeds.lean) 同时证明坐标等号与序的真值集合、
临界点以下种子的主性，以及含不小于 κ 坐标的种子的非主性；空支撑允许主测度。

[ExtenderOperator](ExtenderOperator.lean) 实际收集
`E:P(κ^{<ω})→P(L^{<ω})`，输入可以混合不同长度。
[ExtenderAlgebra](ExtenderAlgebra.lean) 证明交、补集和任意坐标逆像保持；
[ExtenderProduct](ExtenderProduct.lean) 实际构造并保持两张坐标图指定的乘积。
[ExtenderBounded](ExtenderBounded.lean) 从正规性与协调律证明有界投影保持，
见证函数由 [OrdinalChoice](../OrdinalChoice.lean) 逐纤维取最小序数构造，只需 ZF。
`ex_countable_l` 给出算子形式的共同纤维完备性。
[ExtenderTruncation](ExtenderTruncation.lean) 的 `ex_restrict_l` 对 κ<μ≤L 实际构造长度 μ 的短扩展器，
并保留原测度值；正规性产生的新坐标小于旧坐标，因此仍落在 μ 中。

[WoodinExtender](WoodinExtender.lean) 的 `woodin_short_l` 在 ZF 中，对选定谓词固定 κ，
再对每个 κ<L<δ 自动返回上述短扩展器、实际算子及精确识别
`E(A)=j(A)∩L^{<ω}`。[ExtenderRestriction](ExtenderRestriction.lean) 对全部有限列集合 A 证明此方程。
这里使用有限列表示，参照 [Neeman《Determinacy and Large Cardinals》§2](https://www.math.ucla.edu/~ineeman/dlc.pdf/#page=5)
的嵌入限制与有限支撑超幂，以及 [《Determinacy in L(R)》定义 1.2、注 1.5](https://www.math.ucla.edu/~ineeman/detLR.pdf/#page=9)
的算子性质与测度族表述；未将序列图改成 Gödel 序数编码。
`woodin_extender_l` 已直接迁移为这个短扩展器的源系统与良基极限入口；
任意实际短扩展器均可通过 `Ex_short_d.limit_l` 使用同一构造。

[ReducedPower/Los](../../Model/SetTheory/Internal/ReducedPower/Los.lean) 对全部背景内部 D→Q 函数的代表族，
在 ZFC 下证明全部内部公式代码的 Łoś 方程。`rp_los_assignment_l` 从实际赋值族自动构造商赋值，
`rp_satisfies_l` 直接比较两边统一满足关系；内部代码可以非标准。
证明在 `rp_los_m` 这个实际原公式上使用 `sfm_induction_l`。原子、布尔运算、逐列函数图与
赋值更新仅需 ZF；[Witness](../../Model/SetTheory/Internal/ReducedPower/Witness.lean) 的存在量词
见证统一化使用原对象选择公理，审计单独保留这一边界。
[Truth](../../Model/SetTheory/Internal/ReducedPower/Truth.lean) 的相对否定律明确要求
所用真值逆像在容许子集代数中；完整幂集版本已直接迁移为它的实例。

后续沿 [Neeman《Determinacy in L(R)》](https://www.math.ucla.edu/~ineeman/detLR.pdf)
的短扩展器、迭代树、齐性树与泛型迭代路线推进。有限支撑测度图及任意有限坐标投影已构造；
分量商结构、源内部相对超滤与代表族、全背景函数版本的 Łoś 已完成；
实际源理论下的源内部 Łoś、存在见证对角化及传递后继源保持也已完成。
相对测度的跨模型施加、双映射完整初等复制、常值交换方块与良基性回传已完成。
同一扩展器的两次施加保持支撑以下的有限幂子集一致性，坍塌后的复制在支撑上等于 σ。
常值初等嵌入、分量间初等映射以及恒等、复合和交换律现已完成。
通用关系嵌入系统及其极限、有限支撑全系统装配和共同纤维给出的整个极限良基性已完成。
通用短扩展器运算及武丁测度族的标准短扩展器识别也已完成。
极限的完整内部初等性、整体 Mostowski 坍塌及原目标关系因子已完成。
按 ν 选长的 Vν 覆盖、谓词一致性、临界点恢复和完整谓词初等性已完成。
实际迭代树、单根与 pad、任意树前驱上的后继扩张，以及其后继一致性已实现。
极限处添枝和上述条件下的共尾良基分支已实现；小模型的内部编码与跨源还原也已实现。
nice 树的弱迭代性、其策略构造与决定性蕴涵仍待证明。
后续迭代使用的源内部超幂，不能直接用全背景函数版本替代。

当前武丁定义到具有上述强性的实际短扩展器的方向已实现；
与全宇宙类嵌入刻画的完整等价仍待证明。当前定义没有把超幂、良基性或 AD
当作未实现的操作参数。
