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
[PointwiseTrace](../../Model/SetTheory/Internal/PointwiseTrace.lean) 的 `smap_pe_trace_l`
将这一翻译接入源内分离，实际构造指定代表函数赋值的真值逆像 A∈X。
逐点对象赋值也由唯一值收集构造；整个源内入口目前使用 ZFC，原子、布尔、状态与求值构造保留 ZF。

[PointwiseWitness](../../Model/SetTheory/Internal/PointwiseWitness.lean) 的 `smap_pe_witness_l`
在源中集合 A 上把逐点存在见证统一成一个 D 上的源内代表。先对翻译码统一选取函数值，
再由 [PointwiseDiagonal](../../Model/SetTheory/Internal/PointwiseDiagonal.lean) 的 `smap_diagonal_l`
构造 h(p)=gₚ(p)，在 D∖A 上取源中基点；函数图和值域界都属于源。
[ReducedPower/SourceLos](../../Model/SetTheory/Internal/ReducedPower/SourceLos.lean) 的 `rs_los_l`
在真实原公式 `rs_los_m` 上完成全部内部行的归纳。或非明确使用源内真值逆像，
存在步使用上述实际统一代表。此定理的源为实际完整初等嵌入正则不可数 H(χ) 的传递集合。
[SourceSatisfaction](../../Model/SetTheory/Internal/ReducedPower/SourceSatisfaction.lean) 的 `rs_satisfies_l`
给出统一满足关系上的源内部 Łoś，`rs_los_assignment_l` 从实际 ω→G 代表赋值图
自动构造赋值空间、商赋值及全部内部代码集；G 精确为源中的 D→X 函数。
源内入口使用 ZFC；赋值投影、逐点逻辑方程与相对超滤布尔规则分别保留 ZF 或纯逻辑强度。

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
对上述 H(χ) 初等源的源内部 Łoś 及存在见证对角化也已完成。
常值初等嵌入、分量间初等映射以及恒等、复合和交换律现已完成。
有向极限、良基性、与标准短扩展器的识别、迭代及决定性蕴涵尚待实现。
后续迭代使用的源内部超幂，不能直接用全背景函数版本替代。

本层选择上述标准刻画作为定义，尚未在 Lean 中证明它与 extender 刻画、
全宇宙类嵌入刻画之间的等价。后续 extender 和迭代论须接入实际构造；
当前定义没有把超幂、良基性或 AD 当作未实现的操作参数。
