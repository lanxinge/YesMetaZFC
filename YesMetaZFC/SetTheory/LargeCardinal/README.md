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
[MeasureRegularity](MeasureRegularity.lean) 用有界初段补集的短交证明可测基数正则；
[MeasurePower](MeasurePower.lean) 用逐坐标真假纤维排除 κ→P(μ)（μ<κ）的单射，两者只需 ZF。
[MeasurableInaccessible](MeasurableInaccessible.lean) 再用对象选择公理取得实际序数编号，
证明强极限性；`woodin_inaccessible_above_l` 因而实际选择任意给定下界之上的不可达基数。

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

[InaccessibleHierarchy](../InaccessibleHierarchy.lean) 保留不可达秩层的较小序数枚举及 Hδ＝Vδ。
[ExtenderRankSource](ExtenderRankSource.lean) 的 `ep_regular_source_l` 直接构造正则 Vδ 源，不要求强极限。
[DerivedEvaluation](DerivedEvaluation.lean) 证明原求值 j(f)(a) 精确识别商等号及成员关系；
[ExtenderFactor](ExtenderFactor.lean) 装配全部求值并下降为整个极限到原目标的实际关系嵌入。
其图方程保留每一个类代表，尚未断言该因子到原目标的完整初等性。

自动入口 [`woodin_extender_l`](ExtenderDerivedLimit.lean) 已迁移到上述 Vδ 源，
返回同一个系统的完整初等极限、传递坍塌和原目标因子 `Ep_derived_limit_d`。
原 j 因此只作用于已经证明属于 Vδ 的代表。

## 已证明：传递后继继续作为源

[ExtenderSource](ExtenderSource.lean) 的 `Ep_source_d.successor_l` 在 ZF 中证明：
若 X 是实际源，j:X→N 为完整内部初等嵌入，N 传递，则每个源内小的 κ′∈N、ω⊆κ′
都实际得到 K′∈N 和 `Ep_source_d ω κ′ K′ N W`。κ′ 可以不在 j 的像中。
`Ep_source_d` 保留全内部分离和有界集合代数；统一化与外延关系塌缩仅要求源内小载体。
源内 Łoś、常值、复合、投影和全部有限支撑消费者均使用该接口。

[UniversalClosure](../../Model/SetTheory/Internal/UniversalClosure.lean) 用实际原公式归纳
构造任意非标准内部程序的全称闭包，`Smap_d.valid_l` 传输全部赋值上的有效性，
`Smap_d.models_forward_l` 正向保持任意已编码理论。
[SourceTheory](../../Model/SetTheory/Internal/SourceTheory.lean) 保持分离与有界代数；[SourceCollection](../../Model/SetTheory/Internal/SourceCollection.lean) 保持小定义域统一化，覆盖 N 的全部新参数。
[EmbeddingOmega](../../Model/SetTheory/Internal/EmbeddingOmega.lean) 证明 j(ω)=ω；
[SourceFinite](../../Model/SetTheory/Internal/SourceFinite.lean) 用内部归纳证明 N 包含全部背景内部有限函数。
[SourceSequences](../../Model/SetTheory/Internal/SourceSequences.lean) 把相对序列空间识别为真实全部有限序列空间，并保持其源内小性。
[SourceCollapse](../../Model/SetTheory/Internal/SourceCollapse.lean) 传输整条塌缩存在句子，
覆盖目标中的小相对良基外延关系；相对良基性只量化目标模型自身的子集。

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
[ExtenderCopySuccessor](ExtenderCopySuccessor.lean) 的 `ep_copy_successor_l` 固定原树中已有的
实际超幂，自动构造复制的目标。原所属模型的短扩展器公式由 `It_local_d.map_l` 沿实际 σ
搬运；目标侧由源内共同纤维得到良基性，原可数模型无需枝反射。给定极限支撑秩段的实际枚举，
返回的同一复制图满足 k(L)=σ(L)、k↾(j(κ)+1)=σ↾(j(κ)+1)，且原边、目标边与复制严格交换；
还返回 `Ea_maps_d ω L P k σ`。原超幂 P 中有实际 L 枚举的传递集合及其枚举图均属于所属源，
两图在该集合上逐点相同；限制图恢复及目标后继的全部闭包不变量同时保留。
旧图 π、σ 及其可数编号属于各自目标时，同一入口还证明原超幂 P 属于复制目标 P'，
并在 P' 中实际构造 P 到 ω 的单射。输入图的精确定义域及其编号由图自身自动回收。
[EmbeddingSetRestriction](EmbeddingSetRestriction.lean) 用源内有限真值表证明实际限制
`j↾A : A→j(A)` 的全内部初等性，覆盖非标准有限程序；
`ep_rank_restriction_l` 进一步自动构造严格相对秩段的像、正则性与限制图。
[ExtenderRankImage](ExtenderRankImage.lean) 的 `it_ultra_rank_l` 在内部正则 α 下实际辨认
`Ult(Vα,E)=j(Vα)`，新超幂边恰为原 j 的限制；逆向像证明使用源内 κ 编号，
把任意 Vα 值代表的整张图放回 Vα。复制可直接消费这个已辨认的同一秩段。
[ExtenderSuccessorUnique](ExtenderSuccessorUnique.lean) 在 ZF 中以相同代表和塌缩唯一性，
识别同源同扩展器的实际目标及嵌入。
[ExtenderRankAgreement](ExtenderRankAgreement.lean) 进一步证明：两源共有包含 κ 的内部
正则秩段时，两次超幂共享同一个像秩段、像高度和限制嵌入；该高度以下所有有限幂子集一致。
[ExtenderBoundedCollapse](ExtenderBoundedCollapse.lean) 用支撑秩段的实际枚举控制有界代表节点，
由源内小关系塌缩还原同一个 j(B) 及其求值图；`Eb_collapse_d` 保留原测度图定义的
节点关系和实际塌缩，供所属模型中的计算沿初等图传输。
[ExtenderBoundedValue](ExtenderBoundedValue.lean) 在施加源与所属源具有相同有限 κ 幂子集时，
双向搬运 κ 值代表，直接把原施加超幂的 j(κ) 及求值图放回所属源。
[ExtenderBoundedTransport](ExtenderBoundedTransport.lean) 搬运完整节点池、测度关系和原求值图；
目标节点的完整性用有界生成公式证明，递归唯一性辨认目标施加超幂的同一个值。
[ExtenderFunctionMap](ExtenderFunctionMap.lean) 从追加末坐标的有限幂编码推出 π(f)=σ(f)。
[ExtenderCopyBounded](ExtenderCopyBounded.lean) 遂证明复制在整个 j(κ)+1 上等于 σ；
闭区间端点自身使用常值代表，支撑端点由 L⊆j(κ) 得到。
[ExtenderTrace](ExtenderTrace.lean) 在所属源内实际分离完整支撑迹；
[ExtenderTraceMap](ExtenderTraceMap.lean) 同时搬运测度、代表、恒等图与分离方程，覆盖目标中的全部新有限列。
[ExtenderSourceTrace](ExtenderSourceTrace.lean) 可在不同施加源的原超幂中读取这个迹，
不再要求外围界集合属于原小模型。[ExtenderCopySubsets](ExtenderCopySubsets.lean)
先用常值 κ 的像正规化任意子集的代表，再由集合值函数编码证明 π(f)=σ(f)，
最终识别实际集合的两种像；结论覆盖全部有限 L 幂子集。
[ExtenderModelMap](ExtenderModelMap.lean) 搬运实际二元关系码，以 Mostowski 唯一性识别
集合像和枚举图像，将上述一致性提升到整个源内已枚举的传递集合。
集合值函数与二元关系的旧所属搬运证明已直接改用提取后的共同编码，无并行兼容层。
[ExtenderPresentation](ExtenderPresentation.lean) 用全部有限支撑与原源函数构造内部代表集，
测度一关系精确读取原超幂隶属关系，满射呈示将原超幂及其可数编号放回包含源。
[ExtenderProductIndex](ExtenderProductIndex.lean) 用有限列编号证明节点乘积在源内可数；
`Smap_d.countable_fixed_l` 固定源内可数传递集合，因此复制目标实际包含原施加源与所属源。
两项构造均由原复制后继直接消费，不假设完整商或原求值图预先属于目标。
[ExtenderRankLocal](ExtenderRankLocal.lean) 的 `It_local_d.rank_l` 保持严格极限秩段中的
原短扩展器公式。极大性使用子集回收，可数共同纤维使用 ω→κ 图的有限秩界；
不假定该秩段满足 ZF。`It_local_d.return_l` 对指定的实际复制目标证明支撑子集回收到
原所属模型，所需相对幂集由目标性质沿 σ 回拉后实际构造。
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
由此获得证明所需的弱迭代性；返回定理与公开策略的已证入口见下文。

## 已证明：小传递模型的编码与跨源还原

[RelationBounded](../Collapse/RelationBounded.lean) 的 `Wc_iso_d` 用 Δ₀ 证书描述
关系载体到传递集合的实际双射。其关系外延性只需背景外延性，关系良基性只需 KP；
传递像唯一性复用原 ZF 关系递归。`Sc_collapse_d` 的小载体 Hχ、Vδ 实例和完整初等后继保持
已接入所有 `Ep_source_d` 构造，因而每次实际后继继续具有内部塌缩能力。

[ExtenderRelationCode](ExtenderRelationCode.lean) 把 κ 上的二元关系编码为二项 κ 值列的集合，
再由单向子集包含 `Ea_subset_d` 搬运并在目标内还原原关系。
[ExtenderModelCode](ExtenderModelCode.lean) 的 `Ea_subset_d.transitive_l` 给出自动端点：
若 X 的有限 κ 幂子集均属于 Y，B 传递，且源 X 内有实际双射图 F:κ→B，
则 B 属于另一源 Y。关系码、目标内塌缩及其与原 B 的相等全部在证明中构造；
不另要求调用者给出关系码、外延性或良基性。该端点及编码只需 ZF，
初始正则 Hχ 的闭包实例单独使用 ZFC。

这为 Neeman 引理 2.8 最后的小模型编码步骤提供实际还原接口。

[ExtenderSourceSuccessors](ExtenderSourceSuccessors.lean) 的 `It_local_d.successors_l`
已从嵌套源中的内部所属判断构造两侧实际良基超幂，并证明支撑端点上的子集一致性。
[ExtenderSourceTrace](ExtenderSourceTrace.lean) 在所属源内部用共同支撑测度判定成员资格，
有界分离给出自身超幂的完整支撑迹；`It_local_d.subsets_l` 因而把相应子集送回原所属源。
两步复合直接产生上述编码搬运条件。后继的源理论、枝反射、相对层级、幂集、传递包络
与小壳不变量均保留；`it_local_apply_agree_l` 将同一节点加入原树。
Pₙ 的全前驱历史、内部下降反证、nice ω 树的返回定理及 ω₁ 长弱迭代博弈策略已接通，见下文。

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

[SourceSmall](../../Model/SetTheory/Internal/SourceSmall.lean) 用源内实际单射图定义小性；
原图可限制到任意子集。`Sc_collapse_d` 只要求小载体外延关系的塌缩，
不再从它推出任意大关系的良基绝对性。独立的 `Sc_branch_d` 把实际外部下降链反射到源内；
正则 Hχ 和大于 ω 的极限 Vδ 有实际实例，一般完整初等映射不自动保持这一外部性质。

[ExtenderTreeBranch](ExtenderTreeBranch.lean) 的 `Ep_source_d.tree_branch_l` 对任意源内字母表 A、
源内前缀树 T⊆A^{<ω} 和外部存在的分支，实际返回源内的 ω→A 分支图。
证明在源内分离子边，取得下降节点列，收集其全部前缀，再逐坐标统一化；
没有把节点列当作最终分支，也不要求内部 ω 外部标准。
该端点仅需 ZF、实际源证书和独立枝反射；后者的 Hχ 实例用 ZFC，Vδ 实例用 ZF。

## 已证明：完整初等嵌入的尝试树与源内解码

[ExtenderEmbeddingTree](ExtenderEmbeddingTree.lean) 的 `Ep_source_d.at_tree_l` 在源内实际分离
尝试树。节点记录枚举前缀的像，检查重复编号的一致性、给定限制图 τ，以及全部内部
公式在全部有限参数列上的双向真值；`At_node_d.prefix_l` 证明前缀封闭。
`Ep_source_d.at_branch_l` 用已有完整初等嵌入生成外部枝，再由独立枝反射取得源内总枝。

源内节点公式的绝对性依赖实际有限证书：[ExtenderFiniteSyntax](ExtenderFiniteSyntax.lean)
把每个合法内部程序和有限赋值空间放入源；[ExtenderFiniteEvaluation](ExtenderFiniteEvaluation.lean)
逐原程序行作内部强归纳，用 Δ₀ 分离构造真值集，最后由有限函数闭性收集真值表。
因此不要求源包含完整赋值空间的幂集，也不把全部公式真值作为额外输入。

[ExtenderEmbeddingCountable](ExtenderEmbeddingCountable.lean) 的 `Ep_source_d.countable_membership_l`
消费源内集合 A、B、限制图 τ、实际源内单射 ι:A→ω，以及外部完整初等图 j:A→B
和 τ⊆j，返回 k、η∈Z，使 k:A→B 为完整内部初等嵌入、τ⊆k，η:k→ω 为单射。
枚举、两边隶属关系的源内成员资格、尝试树、枝和嵌入图的可数性均自动构造。
[EmbeddingAttemptDecode](../../Model/SetTheory/Internal/EmbeddingAttemptDecode.lean) 按有限赋值
编号的共同自然数界选择一个节点，再恢复原 `Smap_d`；包括非标准内部公式。
任意源内关系结构的入口为 `Ep_source_d.countable_embedding_l`，另消费实际关系图的源内成员资格。
这些构造给定实际源证书与独立枝反射后仅用 ZF。

## 已证明：模型内小 Skolem 壳与跨源隶属的一步装配

`Internal/RankSkolem.lean` 的 `sh_source_of_v_l` 直接在 Vδ 中构造小壳实例，
只要求 δ>ω 为极限序数。`ExtenderSkolemInitial.lean` 同时给出正则 Hχ 的实际实例。
给定源内结构、种子 U 及源内 κ→U 双射，返回实际 Skolem 选择图、对它闭合的
相对最小壳 N 和源内 κ→N 双射；κ 只须是含 ω 的序数，不要求背景基数正确性。

`ExtenderFiniteWitness.lean` 将源内有限证书双向还原为原完整内部 Skolem 见证。
`ExtenderSkolemSource.lean` 传输全称存在句子，覆盖后继模型中的新结构、新种子及
新大小参数。所有代码、有限参数空间、选择图和枚举图都实际属于源。

`ExtenderSkolemCollapse.lean` 的 `ep_skolem_collapse_l` 自动构造源内传递塌缩 B、
塌缩图、κ→B 双射，以及反塌缩到原传递结构的完整初等嵌入。
`ep_skolem_step_l` 再从两源的有限 κ 幂子集一致性推出 B 属于另一源；
关系码、良基性、目标内塌缩和唯一性识别均由现有实现产生。

[ExtenderSkolemStep](ExtenderSkolemStep.lean) 的 `ep_skolem_rank_step_l` 现将尝试树回收、
严格秩界及 Vκ∪{κ,σ} 的指定种子直接接通。返回 B∈Y∩Z、同域完整初等图 k∈B、
编号 η∈B，并保持规定低秩条目；同一 B 还带完整源证书、枝反射、相对层级和小壳闭包。
输出性质均由本步构造证明，不作为新节点的输入条件。

## 已证明：后继枝反射与严格秩段的不变量

[ExtenderBranch](ExtenderBranch.lean) 的 `Ex_short_d.node_l` 从实际短扩展器生成同一个
超幂后继、完整初等常值图及完整源、枝反射、层级、小壳闭包四项不变量。
枝反射的核心是 `ep_branch_reflection_l`：把源中所有相对无枝关系合并成带标签关系，
用源的枝反射证明它良基，再由同一扩展器的可数共同纤维传递良基性。
[ExtenderFormulaSystem](ExtenderFormulaSystem.lean) 只改换观察关系，保留原代表族、商类、
过渡图和极限投影；原二元公式的 Łoś 方程由 `ReducedPower/SourceFormula.lean` 证明。

[ExtenderRankClosure](ExtenderRankClosure.lean) 的 `Ep_source_d.rank_l` 从内部正则性
`Sc_regular_d` 构造严格相对秩段的完整源证书。该条件量化源内所有较小序数域的函数，
由实际正则基数给出，并由 `Smap_d.regular_l` 双向保持；不要求初等像在背景中正则。
相对层比较、序数高度及有界图闭包由 `CumulativeRelativeAlgebra/Closure.lean` 给出。
分离和统一化使用源内实际有限真值表；小塌缩的传递像保留原序数编号。
有限列接口已改为保持给定无限序数界；原先只返回某个无指定界的小性结论由此导出。

[ExtenderSkolemRank](ExtenderSkolemRank.lean) 给代码、有限参数列、选择图和小壳逐一提供
有限秩界，因此小壳性质已经在任意含 ω 的严格极限秩段中保持。
枝反射沿秩段和反塌缩回拉；其余源性质、层级及小壳存在性使用完整初等图的双向传输。
这些结果已直接进入 `ep_skolem_rank_step_l`，可继续下一次节点构造。

所属模型内的 `It_local_d` 已由相对施加入口直接消费；完整下降递归使用该入口。
Neeman 定理 2.3 的坏枝归约与推论 2.4 的公开弱迭代策略由下述端点完成。

## 已证明：Pₙ 全前驱递归与内部下降反证

[ExtenderStrengthReturn](ExtenderStrengthReturn.lean) 从原最大强度证书恢复同一实际
超幂与所属源的共同秩层；[RelativeRankEnumeration](RelativeRankEnumeration.lean)
在目标中重新构造支撑到共同秩层的实际双射，不假定支撑在背景中不可达。
[IterationModel](IterationModel.lean) 将递归需要的源、枝反射、层级、幂集、包络、
小壳及内部不可达闭包一起编码，并从真正的正则 Vβ 构造初始实例。

[IterationDescentStep](IterationDescentStep.lean) 的 `pn_copy_step_l` 构造 Pₙ₊₁∈Pₙ，
保留整个旧支撑秩段及端点上的嵌入值。[IterationCutStep](IterationCutStep.lean)
先由缺失子集推出临界点界，再把原树的指定边限制为实际严格秩段超幂。
[IterationHistory](IterationHistory.lean) 对所有内部有限长度编码完整历史；
[IterationCutHistory](IterationCutHistory.lean) 的 `pn_history_extend_l` 从原 nice 树及
严格下降的正则秩段列延伸任意合法历史，同时保留每个前驱的一致性和缺失子集。

[IterationDescent](IterationDescent.lean) 的 `it_nice_no_drop_l` 用 ZFC 内部依赖选择
构造 ω 历史列，投影出实际隶属下降图，再由基础公理导出矛盾。其输入是原 nice 树、
实际正则秩段列和首行；首行由 [IterationInitial](IterationInitial.lean) 从可数传递域
到正则秩层的给定初等嵌入构造。[IterationNice](IterationNice.lean) 的单根与实际
超幂添枝已给出 nice 条件的实例。[IterationNiceReturn](IterationNiceReturn.lean) 的
`it_nice_return_l` 现已接通返回失败、联合尝试秩、整树复制、正则截断与可数 Skolem 回拉，
构造上述反证所需的全部实际输入。可数 nice ω 树因此有共尾良基枝及返回原 Vθ 的完整
初等因子，保持根嵌入的精确复合式，无需目标高度的额外正则性或极限性假设。
这完成定理 2.3，并作为下述弱迭代策略的后继步骤。

## 已证明：ω₁ 上 nice 树的弱迭代策略

[IterationWeak](IterationWeak.lean) 的 `it_nice_weakly_iterable_l` 从可数完整源及其到真实
Vθ 的初等图，自动构造 Ω=Hartogs(ω)、走法集合包络和公开枝策略 Γ。
`Wi_winning_d` 对直到 Ω 的每个初始长度及全部对手走法给出唯一运行；合法时，每个
模型可数且传递，全部旧箭头及返回图保持，公开策略所选的枝有同一商投影的实际极限。

[IterationWeakUnion](IterationWeakUnion.lean) 对所有旧行取三张图的并；
[IterationWeakLimit](IterationWeakLimit.lean) 构造可数极限及其全部规范腿。
[IterationWeakChoice](IterationWeakChoice.lean) 在同一个实际 Hχ 中选择应答，
[IterationWeakWinning](IterationWeakWinning.lean) 用历史的纯公式做超限归纳，证明合法对局始终有真实应答。
包络包含任意可数根上的实际 nice ω 树，不另限制合法走法。
[IterationWeakPublic](IterationWeakPublic.lean) 以唯一重放构造只读取公开走法历史的集合函数；
[IterationWeakPublicWinning](IterationWeakPublicWinning.lean) 将它的输出识别为获胜运行中原树的共尾枝。
这完成推论 2.4。获胜性不要求未来走法已经合法；所有初始对局分别核验。
状态取并、重放唯一性与原公式对应只需 ZF；可数并计数和应答选择使用背景 ZFC。

## 已证明：不可达支撑的最大强度与所属源证书

[`woodin_rank_strength_l`](WoodinStrength.lean) 在 ZFC 中对每个 A⊆Vδ 固定 κ，
对每个 ν<δ 自动选择 κ,ν<L<δ 且 L 不可达的短扩展器。`Ep_strong_limit_d` 将强性证书
绑定到这张 F 的同一个全系统和商投影；其传递实现 N 及嵌入 i 满足：

- i:(Vδ,∈,A)≺(N,∈,B)，初等性覆盖全部内部公式码，包括非标准码。
- crit(i)=κ，L≤i(κ)，V_L⊆N，A∩V_L=B∩V_L。
- N 缺少某个 L 的子集，所以最大强度恰为 L。
- 原嵌入分解为 j=k∘i；k 的像精确为全部有限支撑求值 j(f)(a)，且 k 逐点固定 V_L。

[ExtenderCoordinates](ExtenderCoordinates.lean) 先由坐标代表覆盖所有 α<L，
[ExtenderLength](ExtenderLength.lean) 据传递坍塌固定性恢复临界点与长度界。
秩覆盖则使用实际枚举，而非只由序数固定性推断：
[RankLength](RankLength.lean) 将 Vν 的一个小序数枚举及其整张图放进 V_L；
[CumulativeRelative](../CumulativeRelative.lean) 与 [RankTransport](RankTransport.lean)
比较相对累积历史，在原目标已经覆盖 Vν 时恢复真实 Vν。
[RankEnumeration](RankEnumeration.lean) 同时构造源中各 Vα 的最小序数枚举。
其最小性把目标 ν 层所需索引压到 L 以下；[RankCover](RankCover.lean)
用两个有限坐标表示每个 x∈Vν，并将它送入同一个极限。
`er_inaccessible_cover_l` 对不可达 L 的每个严格秩层实施同一计算，
故同一张 F 和同一个极限覆盖整个 V_L。
[ExtenderStrengthBound](ExtenderStrengthBound.lean) 再从原 P(κ) 的常值像下读取
全部处处有界代表；其有限支撑节点都属于 V_L。若 N 包含 L 的全部子集，
原投影与坍缩便从 V_L 的一个子集满射到 P(L)，与 |V_L|=L 及 Cantor 定理矛盾。
`Ep_realizer_d` 将原常值图和坍缩图保留到长度与强度证书，保证上下界作用于同一个 N。

[ExtenderExactStrength](ExtenderExactStrength.lean) 的 `Ex_strength_d` 将相对幂集、
实际节点关系、j(P(κ)) 及求值图一同放回所属源。强度条款 `es_strength_m` 使用
所属模型内部的量词；`map_l` 搬运这些实际数据，`realize_l` 在指定超幂中读出
同一最大强度。[ExtenderBoundedEvaluation](ExtenderBoundedEvaluation.lean) 的投影与
坍缩计算同时供源内呈示及求值图识别使用，旧构造已迁移。

[SourceInaccessible](../../Model/SetTheory/Internal/SourceInaccessible.lean) 的 `Sc_inaccessible_d`
使用原始共尾度和幂集基数公式。在极限 Vδ 中，实际共尾图、值域及幂集单射均由
秩闭包回收，因而仅用背景 ZF 就能构造这个内部判断，并沿完整初等图传输。
[SourceInaccessibleRank](../../Model/SetTheory/Internal/SourceInaccessibleRank.lean) 证明它
在包含原参数的严格极限秩段中保持；单射和共尾图来自原源，不要求背景不可达性。
[ExtenderInitial](ExtenderInitial.lean) 的 `Ex_short_d.local_l` 直接把原测度图及可数
共同纤维回收到 Vδ，构造原短扩展器公式的所属判断。武丁入口已经同时返回这些
内部证书；两项初始构造均不额外假设整个 Vδ 满足 ZF。

[CumulativeRelativeRestriction](../CumulativeRelativeRestriction.lean) 将较早层及其原历史
一同放入严格极限秩段；旧层级闭包证明已直接复用这个接口。
`Er_level_d.rank_l` 保留同一秩层和枚举图，并在截断中分离实际关系码。
[ExtenderBoundedRank](ExtenderBoundedRank.lean) 的 `Eb_collapse_d.rank_l` 回收全部原节点和
关系，再由实际枚举证明节点集小，以截断源的小关系坍塌恢复原来的像及求值图。
原证书现同时保留求值图完整反映成员关系的证明，两处原构造与初等传输已一并迁移。
[ExtenderStrengthRank](ExtenderStrengthRank.lean) 的 `Ex_strength_d.rank_l` 因而保留
原相对幂集、同一个有界超幂及原遗漏子集，证明最大强度在严格截断中保持。
`Ep_strong_limit_d.rank_l` 直接消费武丁入口返回的实际枚举与证书：当 F,L∈U、
U 是原源内的严格极限秩段且其高度满足源内正则性时，自动构造 U 的源证书，
并返回最大强度、同一秩层的枚举、内部不可达性和原短扩展器判断。
上述保持只需背景 ZF；截断高度不要求强极限，原坍塌像的所属判断也由证明给出。
这些步骤已接入全前驱历史、内部下降反证、返回失败归约及公开弱迭代策略。

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

## 完整类型的实际伸展

[WoodinTypes](WoodinTypes.lean) 的 `woodin_type_stretch_l` 完成 Neeman 引理 3.22
中类型保持的核心论证。给定武丁基数 δ、η>δ 和 Vη 中任意内部有限元组 s，
对每个 α<δ 实际构造 α<κ<δ，使每个 τ<δ 都有同一临界点的短扩展器 E∈Vδ，
其支撑与最大强度同为不可达 L>max(κ,τ)，并且

\[
\operatorname{proj}_\tau\bigl(j_E(\operatorname{tp}^{V_\eta}_\kappa(s;\delta))\bigr)
=\operatorname{tp}^{V_\eta}_\tau(s;\delta).
\]

这里 j_E 是所构造的 Vδ 源超幂嵌入，κ 型自身已证明属于该源。

[TypeTruth](../../Model/SetTheory/Internal/TypeTruth.lean) 的 `Tt_realized_d` 包含实际模型码、
有限元组、指定常量和完整真值集合；常量域恰为 Vκ∪{κ}。查询量化全部内部自然数公式码，
不把内部有限序列限制为外部标准长度。[TypeSource](../../Model/SetTheory/Internal/TypeSource.lean)
将任意原公式编译为这种类型的实际查询。[TypeRank](../../Model/SetTheory/Internal/TypeRank.lean)
证明查询域与类型属于 Vδ。

[PredicateTrace](../../Model/SetTheory/Internal/PredicateTrace.lean) 证明 j(A∩D)=B∩j(D)，
全称定义覆盖目标中不在 j 像内的元素。[WoodinTrace](WoodinTrace.lean) 给真值码谓词加入序数标记 α，
用同一截面定理及低秩一致性迫使 α 固定，得到 κ>α。
[TypeEmbedding](../../Model/SetTheory/Internal/TypeEmbedding.lean) 进一步证明 j(Vκ) 包含共同 V_L，
并逐层搬运名字域、有限列空间和查询对，保证全部新低秩查询进入像类型的查询域。
`Et_stretch_d` 将投影与同一张 E 的实际超幂图绑定。

[TypeElasticSource](TypeElasticSource.lean) 的 `ee_realized_source_l` 已在 V(η+1) 内用单一原公式
读取同一元组的 Vη 完整 κ 型，并检验全部 τ<δ 的实际伸展。公式内部量化源、扩展器、
常量域、查询域与类型，外层无需满足 ZF。任意通过短扩展器及不可达最大强度检验的候选，
都由 [TypeStretchQuality](TypeStretchQuality.lean) 自动构造良基超幂、支撑层枚举和类型秩界。
[TypeElasticCode](TypeElasticCode.lean) 的 `st_ee_build_l` 在 ZF 中按内部 n 构造实际原程序，
自动绑定原变量列；语义读取中的 ZFC 用于超幂及枚举构造。`woodin_elastic_l` 给出这一全高度
条件的实际武丁实例，各高度共用同一源隶属关系及原 κ 型。

[TypeElastic](TypeElastic.lean) 的 `ee_definition_l` 已完成定义 3.13 的查询装配。
只输入 ω、非零极限 κ 和内部元数 n，就在 ZF 中构造 Vκ∪{κ}、全部查询域及固定的四查询组：
最大序数、前驱参数域、δ 不可达、全高度伸展。`Ee_elastic_d` 在这份固定语言表示下只检查
四条查询的成员关系，适用于未实现类型；两条前驱守卫分别检查，未将裸类型当作演绎封闭理论。
`Ee_minus_d` 对原语法前驱算子加入这两条守卫，已有存在域与唯一性定理。
`ee_elastic_absolute_l` 证明固定查询判断在传递源中绝对。整个查询组先于任意类型构造，
实现类型上的等价式再读取同一元组的实际前驱、当前结构的原不可达判断及每个 τ<δ 的伸展。
ω 与 n 的名字合法性直接来自 κ 为非零极限序数，未附加 κ>ω。

引理 3.22 已完成：`woodin_elastic_l` 返回无界多个 κ 的完整弹性类型，并携带
`Ee_language_d` 的实际查询及统一读取证书。`sc_v_inaccessible_l` 在任意包含 δ 的秩层
验证 δ 的原不可达查询，不要求层高为极限或该层对 Kuratowski 配对封闭。
`sc_v_inaccessible_read_l` 给出反向读取。`Ee_language_d.realized_l` 从任意秩实现自动
恢复后继高度、δ 的不可达性、Vδ 源、实际前驱和全部高度的伸展。
[Subtype](../../Model/SetTheory/Internal/Subtype.lean) 已构造定义 3.6 的固定查询，
对任意内部有限元数扩充及排列读取完整实现见证。查询程序先于具体类型及常量固定，
同一查询码具有唯一性。[TypeExceeds](../../Model/SetTheory/Internal/TypeExceeds.lean)
保留定义 3.9 的原秩间隔 ν+1<η 和实际排列。

[TypeOneStep](TypeOneStep.lean) 的 `ee_one_step_l` 完成引理 3.23。
对事先编译的任意子类型程序，由原弹性类型、超过关系和候选类型的参数域构造伸展；
δ 的不可达性及实际 Vδ 源自动读取，结论保留输入的同一程序及参数槽。
正则性给出 τ+ω<δ，弹性提供同一扩展器在前驱类型上的伸展；固定子类型查询经
[SubtypeStretch](SubtypeStretch.lean) 从前驱像搬到原类型像。输出包含支撑等于不可达最大强度
的实际扩展器、τ+ω 上的投影，以及原定义的子类型查询成员关系。
[WoodinTypeStep](WoodinTypeStep.lean) 的 `woodin_elastic_step_l` 给出直接实例：
任意 Vη 中的内部有限元组，在 V(η+3) 与 V(η+1) 有域递增的弹性类型，后者超过前者，
并实际构造所需的一步伸展；两个类型的实现元组和精确高度一并保留。
子类型程序先于临界点及类型固定，全部无界实例使用同一份原代码。

[LocalIndiscernibles](LocalIndiscernibles.lean) 的 `li_indiscernibles_l` 已构造定义 3.27
所需的实际对象，背景只需 ZF。给定序数 δ，固定参数带 U=V(δ+ω) 和包含全部内部
公式码、任意内部有限参数列的查询域 D。在 V(ν+ω) 中以 ν 为指定点的完整类型
属于 P(D)；[UnboundedFiber](../Ord/UnboundedFiber.lean) 的实际原公式收集证明
某个类型在无界多个高度重复，因此对任意下界 α 都能取 α<ν<ν+ω<μ 的不可分辨对。
证明不要求武丁性、外部良基性、标准 ω 或一个假定存在的类型选择函数。

`Li_pair_d.read_l` 返回两边的实际隶属模型和完整实现，并逐个原公式核验
φ(ν,a₀,…,aₖ₋₁) 与 φ(μ,a₀,…,aₖ₋₁) 在各自 V(ν+ω)、V(μ+ω) 中真值相同，
所有 aᵢ 都来自同一 U。重复参数、任意参数顺序以及全部内部查询均保留。
[LocalIndiscerniblesLeast](LocalIndiscerniblesLeast.lean) 的 `li_canonical_l` 自动构造
δ 以上按第二坐标优先的字典序最小不可分辨对；`Li_least_d.unique_l` 保证唯一性，`li_least_m`
给出同一最小条件的原公式。最小化使用原 δ<ν 条件，没有另加间隔限制；带明确
ω 间隔的存在性由前一个入口单独提供。

[LocalTypeTransportTuple](LocalTypeTransportTuple.lean) 的 `Li_pair_d.transport_l`
已把这份真值对应接到完整类型搬运。给定实际 V(ν+k) 元组及其完整 κ 型，
其中 k∈ω 且 k>0，元组长度为任意内部自然数；元组项可以来自整个共同参数带，
也可在任意位置重复出现 ν。接口自动恢复原名字列，在 V(μ+k) 中实际生成新元组，
只把 ν 换成 μ，并保留同一个常量域、查询域及类型集合。`Tm_move_d` 记录原函数图
上的逐项对应，不要求预先排成标准坐标顺序。

`li_canonical_transport_l` 自动选择任意 θ≥δ 的字典序最小不可分辨对，参数带为
V(θ+ω)，指定常量仍为 δ；因此 θ 可以另行覆盖树的秩。背景仅需 ZF，δ 是大于 ω
的极限序数，不要求武丁性、不可达性或源秩层满足 ZF。读取公式一次检验整个候选
类型的所有内部查询；[OrdinalAdditionSource](../../Model/SetTheory/Internal/OrdinalAdditionSource.lean)
直接证明原序数加法的源绝对性，[CumulativeFinite](../CumulativeFinite.lean) 保证
内部有限名字列仍在共同参数带内。`li_canonical_finite_l` 还自动生成共同名字域和
两侧的实际完整类型，供无需指定已有类型的调用使用。

[TypeGameDecoding](TypeGameDecoding.lean) 的 `tg_one_graph_recovery_l` 已实现优化路线的
一张图恢复。先自动编译完整节点、空根和末位最大序数的实际查询，随后读取任意
`Ts_at_d` 子类型见证。全部长度为内部自然数，原双射排列及旧坐标的逐项对应都保留。
完整节点谓词核验三张坐标图的函数性、同一精确定义域和合成节点属于树；中间坐标
只组成集合，不预设标签次序。源绝对性只需传递性，不假设秩层满足 ZF。

在 k≥1、旧树含空根且属于 Vα 的条件下，旧 α 不能进入标签图，也不能成为含非空
节点的树，所以只能处于末位；旧树则恢复为首位。旧图因此包含在新图中，再由精确
定义域和函数性推出新图恰延长一项。最大序数查询反推见证高度为 α+1，未先假设这一
高度。[TypeGameReset](TypeGameReset.lean) 的 `tg_reset_type_l` 从实际含根树构造
(S,ν) 在 V(ν+1) 中的完整类型，并返回上述三个查询的可复用语义证书及真值。
规范不可分辨对已同步校正为原 5.12 的约定：
先最小化第二坐标，再最小化第一坐标。

[TypeDrop](../../Model/SetTheory/Internal/TypeDrop.lean) 已实现 dcp 的原语法投影。
任意内部前缀元数 n≤m 的投影均通过查询重编码逆像构造；原公式自然数码不变，
只把名字列中指定常量 δ 的标记由 n 改为 m。`Tt_realized_d.dcp_l` 证明删除末位后
仍是同一秩层、同一常量域中原前缀的完整类型；`append_l` 实际添加末位，且再次
做 dcp 字面返回原类型。投影对裸查询集合定义，不量化语义正确性作为算子条件。

[TypeGameReply](TypeGameReply.lean) 的 `Tg_reply_d` 已装配规则 (7) 的完整类型约束：
w 是 dcp(u) 的子类型，同时含空根、末位严格超过 δ 和树秩、末位加二最大序数三条
实际查询。`tg_reply_language_l` 自动构造常量域、查询域及代码；`read_l` 从原查询
恢复真实低层模型、任意子类型排列、根和末位，并给出严格秩界与精确高度 α+3。
[TypeGameReplyBuild](TypeGameReplyBuild.lean) 从实际低层前缀添加末位，构造满足这份
约束的完整回答类型和原定义的子类型查询。此构造使用恒等排列，规则及读取不限制排列。

[TypeElasticDomain](TypeElasticDomain.lean) 只用 ZF 从两条定义域查询取得实际前驱。
[TypeGameRigidity](TypeGameRigidity.lean) 的 `tg_exceeds_rigid_l` 完成后继高度刚性：
旧类型含末位加二最大序数，新类型超过它且 dcp⁻ 有定义，便推出新类型末位为最大序数。
证明使用任意真实排列；没有把完整弹性、δ 不可达性或扩展器强性加作这一结论的前提。

[WoodinGameTypes](WoodinGameTypes.lean) 从任意内部有限历史自动构造 dcp 弹性的游戏
类型，参数域可超过任意 χ<δ；[WoodinGameReset](WoodinGameReset.lean) 已将它实例化
为含空根树的实际二元重置类型，完整节点、空根、最大序数和 dcp 弹性同时成立。

[TypeGame](TypeGame.lean) 的 `tg_game_l` 已完成完整辅助闭博弈装配。从 δ、落子字母表
A∈Vδ 和 S 自动选择相对于 max(δ,rank(S)) 的原最小局部不可分辨点，构造三张实际代码表，
再产生模型内部的游戏码、有限历史、合法历史树、无限对局与策略空间。构造只需 ZFC、
ω<δ 且 δ 为极限；这里没有先假设获胜策略，也未把整个秩层假定为 ZFC 模型。

[TypeElasticCatalog](TypeElasticCatalog.lean)、[TypeGameProgramCatalog](TypeGameProgramCatalog.lean)
和 [TypeGameQueryCatalog](TypeGameQueryCatalog.lean) 用已有编译工厂及原公式的集合内统一化，
在任何对局出现前固定查询字节。弹性表和节点／端点表的图包含于 Vδ；子类型程序表只按
内部元数选择，其图包含于 Vω，κ、候选类型不参与程序选择。表项直接回收原完整语义证书。
没有对裸类型加入逻辑闭包，也不在每轮另换语义等价的查询。

[TypeGameAuxiliary](TypeGameAuxiliary.lean) 接合规则 (2)–(6)：完整节点和 dcp 弹性、
初始 rank(A)<κ 与逐轮域增长、原树和 νL 的完整重置类型、tℓ=pred(t) 及新 u 超过旧 w。
[TypeGameAnswer](TypeGameAnswer.lean) 接合规则 (7)，仅增加优化稿要求的空根条件；
任意有限排列仍保留。[TypeGameStages](TypeGameStages.lean) 对每个内部时刻自动恢复
唯一轮号和三阶段之一，依次由 II 出辅助走法、I 回答、按原轮号奇偶落下实数坐标。

[FirstViolation](../Descriptive/FirstViolation.lean) 与
[FirstViolationMinimum](../Descriptive/FirstViolationMinimum.lean) 构造有限违规证据和闭收益集。
最早失败长度由模型内部的序数最小化取得，覆盖非标准 ω；`Tg_game_d.payoff_l` 精确证明
I 获胜当且仅当对局全程合法或首次违规属于 II。完整合法历史树与违规后的胜负树分别构造。
[ClosedDeterminacy](../Descriptive/ClosedDeterminacy.lean) 的 `cg_closed_det_l` 已完成 4.16：
在 ZFC 中对任意非空集合字母表和固定玩家时序，直接分离 II 的获胜局面集合，
按第一步落子拼接模型内的策略，再构造 I 避开该集合的策略。
取模型内部最早进入获胜区的长度证明所有前缀均避开该区，故属于闭收益树。
证明覆盖非标准 ω，策略拼接仅用 ZF；选择公理分别用于选取子策略和可走字母。
[TypeGameDeterminacy](TypeGameDeterminacy.lean) 的 `Tg_game_d.determined_l` 将此结论直接
用于原三阶段游戏，返回原策略空间中的获胜策略及其玩家。
尚待完成 5.15 将 II 的获胜策略从辅助博弈转到原博弈的完整迭代论证。

[TypeGameContinue](TypeGameContinue.lean) 已把继续扩展器施加到指定较早节点，
并在同一目标反射层内得到候选实现与一张图恢复。旧回答查询和任意落子字母表
所在的共同低秩层沿实际根图固定；[TypeGameRigidRead](TypeGameRigidRead.lean)
从原超过见证及 dcp 定义域推出最大序数查询，[TypeGameRecovery](TypeGameRecovery.lean)
保留任意排列并恢复恰好一个新标签。六个反射句子都有已证实例，工作模型不预设 ZFC。
[TypeGameRestart](TypeGameRestart.lean) 将同一次恢复的完整实现、原 dcp 弹性与原程序
直接组成下一轮输入，并调用原更新句子产生完整回答。
[TypeGameRoundScope](TypeGameRoundScope.lean) 从原武丁公式读取工作模型内的正则性，
取回答的小超幂支撑为共同高度，并自动回收原语言、查询域和完整类型。
[TypeGameRound](TypeGameRound.lean) 使用这份回答建立当前完整模型上的实际树边；
首轮已直接迁移到同一接口。`continue_tree_l` 也已接上这一奇数树边，
保留偶数边与奇数边的原回答、根图复合及原字母表的逐点固定性。
实际 nice 树的末项界住整列支撑，下一轮的下界允许等号，回答高度仍严格增长。
[TypeGameAnswerHistory](TypeGameAnswerHistory.lean) 的 `Tg_context_d.answer_history_l`
已将同一个完整回答接入后继模型的原查询表。查询沿共同根图回到实际实现所在层核验，
再在后继反射层内构造回答有序对并追加原策略历史，得到实数落子阶段的控制位置。
该接口允许任意内部轮号；反射层只使用已有闭包和控制记录，不假定其满足 ZF。
[TypeGameTreeStep](TypeGameTreeStep.lean) 的 `Tg_game_d.run_start_l` 已从原 II 获胜策略
自动产生实际首轮实例，包括 padding、超幂及回答后的历史。
[TypeGamePositionNext](TypeGamePositionNext.lean) 和 [TypeGamePositionIssue](TypeGamePositionIssue.lean)
已对任意内部轮号继续完成实数落子、轮号递增、原策略的下一辅助走法及原程序表读取；
这些结果直接由 `answer_history_l` 和 `run_start_l` 返回，不要求下一轮额外给定合法走法。
已发出记录同时保存产生该走法的原前缀及完整辅助合法性，仍使用四十六个坐标。
[TypeGameIssuedReset](TypeGameIssuedReset.lean) 对任意轮的空标签走法直接构造完整重置输入。
[TypeGameIssuedQuery](TypeGameIssuedQuery.lean) 由同一原表项恢复节点查询、实数前缀、
域增长、所选旧轮的继续条件及当前候选的 dcp 弹性。
[TypeGameIssuedLow](TypeGameIssuedLow.lean) 用相对极限秩层的关系闭包证明实数前缀和标签图
属于原字母表所在低层；`continue_tree_l` 已直接消费此构造，调用方不再另给节点查询、
候选合法性或七个低层参数的成员证明。继续分支的旧回答弹性、共同秩段和支撑界
仍须由统一历史不变量提供，尚不能从一个孤立的已发出记录推出。

[TypeGameSaved](TypeGameSaved.lean) 在回答的原反射层内实际打包完整五十四坐标记录，
附带共同秩段及域、常量域、查询域、回答的低层成员证书。存档编码与本轮原坐标
逐项相同，读回时保留这一字面对应。[TypeGamePast](TypeGamePast.lean) 将所有旧轮
保存为内部序数长度函数图，并给出纯一阶历史公式、按轮号选择、旧模型结点对应、
整列共同秩段迁移及低层逐点固定性。
[TypeGamePastStep](TypeGamePastStep.lean) 的 `past_update_l` 已被重置与继续两种实际
树更新调用：在旧历史界低于新临界点时，保存全部旧行并追加本轮原证书，保持与
模型列的对应。旧回答的四个低坐标及其有序对均固定。`run_start_l` 已从空历史
实际构造第一行存档，返回相同原坐标的编码和真实树结点，不另设初值存在前提。

[TypeGameEventHistory](TypeGameEventHistory.lean) 由原控制记录中的时钟单值性识别同一事件，
三次实际追加保留旧历史，规则 (4) 因而推出相邻辅助域严格增长。
[TypeGameTrace](TypeGameTrace.lean) 将旧标签列及回答写成背景 Δ₀ 对应公式；
自然数标签列沿实际初等图固定，域与类型由共同秩段固定，整份对应随当前历史搬运。
[TypeGamePastEvents](TypeGamePastEvents.lean) 将该对应接到所有完整存档行，给出内部一阶公式，
并证明偶数嵌入、历史追加和新行加入时的保持性。首轮实际构造已返回整列对应，
且在实数落子和下一辅助请求之后继续成立。
[TypeGameHistorySelect](TypeGameHistorySelect.lean) 从非空请求的原继续条件取得较早轮号，
自动读取真实旧工作源和完整原记录；事件单值性证明所引用的标签、域与类型均为存档原值。
原超过公式仍在当前反射层内，工作层不需要额外的 ZF 模型性。

[GameAttemptRank](../Descriptive/GameAttemptRank.lean) 的 `Cg_control_d.rank_l` 在 ZF＋DC 中
从原 II 获胜策略证明合法尝试树无枝，实际构造序数值秩函数。任意集合字母表上的
无枝性到良基性由 [TreeDependentChoice](../Descriptive/TreeDependentChoice.lean) 完成，
链取并复用内部 ω 上的 `ds_path_run_l`；没有假定 ω 外部标准。
原控制记录已包含这份秩的存在性，并随原初等图搬运。
[TypeGameRank](TypeGameRank.lean) 在 KP 背景下读取其 Δ₀ 证书，ZF 中排除传递目标内
控制树的背景内部无限合法延长链；不对反射层附加 ZF 或 DC。
这完成了 5.19 所需的尝试树秩与绝对性步骤，但仍须构造统一历史并把它送入偶数极限。
[TypeGameContinueSeed](TypeGameContinueSeed.lean) 已从选中旧轮的完整语言、原弹性、
当前超过见证及事件对应自动装配 `tc_seed0_m`；[TypeGameContinueAuto](TypeGameContinueAuto.lean)
按实际旧回答域重定基源，并调用两条真实树边。原查询表的单值性进入同一控制记录，
重置和继续均保留原请求与完整回答的十九项字面对应。
[TypeGameHistoryStep](TypeGameHistoryStep.lean) 的 `tree_successor_l` 按标签是否为空
统一两种构造。[TypeGameRunAdvance](TypeGameRunAdvance.lean) 的 `Tg_run_d.advance_l`
完成偶数边上的整份历史搬运、回答追加、实数落子和下一辅助请求，并保持所有历史行、
共同根图、锚点、事件对应及支撑界。初值由 `Tg_game_d.run_start_l` 直接产生。
[IterationTreeSyntax](IterationTreeSyntax.lean) 精确编码含 padding 的实际树及最大强度；
[TypeGameRunSequence](TypeGameRunSequence.lean) 的 `Tg_game_d.history_sequence_l`
已经在背景内部的 ω 上构造整列合法历史。初值和总后继均调用上述实际实现，
相邻项保留两次树扩张、偶数边、全部十九项控制参数的像及历史包含性。
该定理在原字母表非空时给出合法历史序列，尚未输出原游戏的获胜策略。
[TypeGameOdd](TypeGameOdd.lean) 将原请求选中的旧历史行、实际奇数嵌入和新存档绑定。
`Tg_run_next_d` 保留旧树与旧图的嵌入像，并证明恢复图恰好增加一个点；
空标签分支保留原偶数前驱和空图。该加强已由同一 `history_sequence_l` 递归实现。
尚待对这列有限树取并，完成偶数极限的秩下降矛盾和奇数无限返回分支。
奇数返回部分还须处理重置产生的 padding；当前 `it_nice_return_l` 接受的是每一步
都有实际扩展器的 `It_nice_d`，不能直接用于此处的 `It_pnice_d`。

后续沿 [Neeman《Determinacy in L(R)》](https://www.math.ucla.edu/~ineeman/detLR.pdf/)
及用户 2026-10-10 的两份改良审阅稿推进。裸 L(ℝ)⊨AD 采用一次坍缩后的双树穷尽终点，
保留类型游戏、6.7 与 6.10 的地面／坍缩二择一、7.22–7.23 的实数吸收，
以及 8.5 的转移和 8.12、8.15–8.18 的双侧树证书，
最后接 8.21–8.24 的高度提升。余解析齐性、齐性传播、projective 展示和 UB 拓扑刻画
不作为这条主线的前置。连续策略族审阅稿的直接游戏和统一反例树秩提供后续的策略输出接口；
其单 Woodin 结论不替代最终 L(ℝ) 的大基数假设。

类型游戏继续允许 subtype／exceeds 的任意有限排列。一张图已经按完整节点谓词恢复，
根角色用固定公式 ∅∈v₀ 锚定；一张图和两张图的恢复分别保留非空长度与不交字母表条件。
旧逐坐标标签查询仍是可独立使用的语法接口，不作为新游戏路线的额外排序规则。
两份审阅稿作为纸面证明依据，其中保留的深层引理仍须逐一在 Lean 中证明。

有限支撑测度图及任意有限坐标投影已构造；
分量商结构、源内部相对超滤与代表族、全背景函数版本的 Łoś 已完成；
实际源理论下的源内部 Łoś、存在见证对角化及传递后继源保持也已完成。
相对测度的跨模型施加、双映射完整初等复制、常值交换方块与良基性回传已完成。
同一扩展器的两次施加保持支撑以下的有限幂子集一致性，坍塌后的复制在支撑上等于 σ。
常值初等嵌入、分量间初等映射以及恒等、复合和交换律现已完成。
通用关系嵌入系统及其极限、有限支撑全系统装配和共同纤维给出的整个极限良基性已完成。
通用短扩展器运算及武丁测度族的标准短扩展器识别也已完成。
极限的完整内部初等性、整体 Mostowski 坍塌及原目标关系因子已完成。
按 ν 选择不可达 L>ν、整个 V_L 覆盖、谓词一致性、临界点恢复和完整谓词初等性已完成。
实际迭代树、单根与 pad、任意树前驱上的后继扩张，以及其后继一致性已实现。
极限处添枝和上述条件下的共尾良基分支已实现；小模型的内部编码与跨源还原也已实现。
nice 树的 ω₁ 弱迭代策略、定义 3.13、引理 3.22–3.23，以及局部不可分辨对象的
实际存在性、真值对应、规范最小选取及有限后继秩层的完整类型搬运已完成；类型游戏的
完整节点查询、一张图恢复、原 dcp、弹性重置类型、规则 (7) 的类型约束及后继高度刚性
也已完成。完整辅助闭博弈、有限历史、首次违规胜负与决定性已完成；
5.15 的迭代获胜论证、泛型迭代、双侧树证书及最终 L(ℝ) 的 AD 蕴涵仍待证明。
后续迭代使用的源内部超幂，不能直接用全背景函数版本替代。

当前武丁定义到具有上述强性的实际短扩展器的方向已实现；
与全宇宙类嵌入刻画的完整等价仍待证明。当前定义没有把超幂、良基性或 AD
当作未实现的操作参数。
