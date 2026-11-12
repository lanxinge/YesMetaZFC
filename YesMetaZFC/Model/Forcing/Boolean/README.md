# 布尔完备化

非零布尔条件、正则开完备化、规范稠密映射及模型内编码。

[总索引](../INDEX.md)

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [Conditions.lean](Conditions.lean) | `Boolean.lean` | 布尔代数的非零条件 |
| [Generic.lean](Generic.lean) | `BooleanGeneric.lean` | 布尔滤子的局部泛型性 |
| [Internal.lean](Internal.lean) | `InternalBoolean.lean` | 布尔代数的实际模型内编码 |
| [RegularOpen.lean](RegularOpen.lean) | `RegularOpen.lean` | 预序上的正则开完备布尔代数 |
| [Completion.lean](Completion.lean) | `Completion.lean` | 条件到正则开代数的规范稠密映射 |
| [NameValue.lean](NameValue.lean) | — | 实际名字的成员真值集合图、正则性及泛型命中的精确含义 |
| [RegularSet.lean](RegularSet.lean) | — | 地模型内部正则开载体、并集正则化及全部内部集合族的上确界 |
| [RegularAlgebra.lean](RegularAlgebra.lean) | — | 该实际载体上的包含序、交、剩余、双重否定及完备性 |
| [NameMap.lean](NameMap.lean) | — | 将同一成员真值图装入实际内部完备化，并自动构造泛型读取所用的规范地嵌入 |
| [NameLocalization.lean](NameLocalization.lean) | — | 构造条件的主正则开集、实际投影及其核，将名字图局部化并保留包含该条件的每个泛型中的读取 |
| [GroundGeneric.lean](GroundGeneric.lean) | — | 以旧幂集的规范像为参数，精确表达对地模型泛型 |
| [GenericName.lean](GenericName.lean) | — | 从真实小泛型名字值取得局部力迫证书，并在每个通过该条件的泛型中读取证书 |
| [HitValue.lean](HitValue.lean) | — | 构造名字命中任意旧集合的正则开真值及整张内部图 |
| [RegularValues.lean](RegularValues.lean) | — | 正则开补、内部上确界的逐条件刻画与泛型读取 |
| [ConditionValue.lean](ConditionValue.lean) | — | 主正则开集的泛型读取、可数反射模型中的包含判据 |
| [NameHomData.lean](NameHomData.lean) | — | 自动构造小完备化到大条件主区间的实际命中图 |
| [NameHomCountable.lean](NameHomCountable.lean) | — | 在反射模型中证明交、补及全部内部上确界保持 |
| [NameHomSyntax.lean](NameHomSyntax.lean) | — | 同一命中图及全部有限参数的原公式编码 |
| [NameComplete.lean](NameComplete.lean) | — | 消去可数性前提，得到原名字诱导的完全同态并实际调用核定理 |
| [IntermediateQuotient.lean](IntermediateQuotient.lean) | — | 在实际小泛型扩张内构造商载体，精确反映旧目标条件的相容性 |
| [NameQuotient.lean](NameQuotient.lean) | — | 接入同一名字、忠实区间和中间商，证明核补被接受及原大泛型的目标条件属于商 |
| [DenseMap.lean](DenseMap.lean) | — | 原模型中的稠密条件映射及指定源条件以下的提升 |
| [DenseRegular.lean](DenseRegular.lean) | — | 实际正则开回拉、正则性及包含关系反射 |
| [DenseImage.lean](DenseImage.lean) | — | 向下像正则化恢复源正则开集，证明回拉满射 |
| [DenseCompletion.lean](DenseCompletion.lean) | — | 稠密映射诱导模型内双射完全布尔同态 |

从 `NameValue` 起的模块处理地模型自己的集合及幂集；完备性量化原模型中的集合族。

[CompleteHom](../../../SetTheory/Boolean/CompleteHom.lean) 定义实际集合图上的完全布尔同态；
[Interval](../../../SetTheory/Boolean/Interval.lean) 构造主区间及其相对布尔运算、内部上确界。
[Kernel](../../../SetTheory/Boolean/Kernel.lean) 的 `Cbh_d.kernel_l` 在 ZF 中分离
`N = f⁻¹{0}`，构造 `k = ⋁N`，证明 `f(k)=0` 和 `N=↓k`。
实际限制 `f↾(B↓¬k)` 保持完全性、反映顺序、单射，并与原图具有相同像域；目标代数无需额外假定完备。

[Projection](../../../SetTheory/Boolean/Projection.lean) 构造实际完全同态 `a ↦ a∧u`；
[ProjectionKernel](../../../SetTheory/Boolean/ProjectionKernel.lean) 调用通用核定理，证明核上确界为 `¬u`，
忠实限制为主区间上的双射完全同态。`bv_local_kernel_l` 消费这一实例，把任意实际名字的成员真值图
投影到条件 `p` 的主正则开集以下，并证明对每个包含 `p` 的原泛型仍精确读取同一名字。

`bv_name_map_l` 本身只给出条件域上的成员真值图。`gn_value_complete_l` 从实际名字值出发，
自动构造旧幂集、局部条件及完备化之间的映射：小正则开集 U 的像为“τ 命中 check(U)”的真值，
再限制到大条件 p 的主区间。`Nh_d.complete_l` 证明该实际图保持零、交、补和任意内部上确界。
证明先在可数初等模型中用泛型区分正则开集，再通过
[CompleteSyntax](../../../SetTheory/Boolean/CompleteSyntax.lean) 的原公式反射回来；公开接口只要求 ZF，
没有地模型外部可数或良基的前提。`gn_complete_kernel_l` 对该原名字同态实际构造主核及同像的单射完全限制。

`Nh_d.quotient_l` 精确读取同一原名字的小泛型 H，并在 **M[H]** 中构造商条件集及其序。
其条件为与 H 所接受的全部忠实区间元素的像相容的旧目标正条件。核的补确被 H 接受，
原大泛型命中的每个目标正则开集均进入此商。

[Adjoint](../../../SetTheory/Boolean/Adjoint.lean) 构造完全同态的规范左伴随集合图，
证明 `b ≤ i(a) ↔ π(b) ≤ a`；目标只需布尔代数，不额外假设完备或同态单射。
[QuotientProjection](QuotientProjection.lean) 将商条件精确化为 `b ≠ 0 ∧ H 命中 π(b)`。
[QuotientName](QuotientName.lean) 用这些投影值构造实际加权名字，并证明其值恰为上述商载体。

[QuotientDensity](QuotientDensity.lean) 从任意商稠密名字取得旧目标条件见证；
[QuotientLift](QuotientLift.lean) 以 `Z ∧ i([q])` 将见证提升为原代数的稠密集。
[QuotientGeneric](QuotientGeneric.lean) 据此证明商滤子命中 **M[H] 中全部稠密集**，没有把商泛型性作为输入。
[RegularGeneric](RegularGeneric.lean) 将原大泛型实际送到局部正则开代数，供原名字接口自动调用。

[QuotientIteration](QuotientIteration.lean) 用同一个商名字及旧关系的检查名字装配二步序，
返回组合泛型，并构造组合二步扩张到双重扩张的保成员双射及逐名字求值对应。
以上构造均已接入 `Nh_d.quotient_l`。

[DenseExtension](DenseExtension.lean) 证明局部稠密映射给出全部名称商的同构：反向标签图将 q
替换为像在 q 以下的源条件，再以内部双模拟证明往返名字值不变，从而得到满射。
[PrincipalGraph](PrincipalGraph.lean) 构造实际主正则开函数图；
[RegularExtension](RegularExtension.lean) 据此识别原扩张与局部正则开扩张。

[QuotientCoupling](QuotientCoupling.lean) 构造共同条件 `(q,x)`，其中 `q≤c` 且 `q∈π(x)`。
[QuotientComparison](QuotientComparison.lean) 将其映为 `x∧i([q])`；
[QuotientStepMap](QuotientStepMap.lean) 将其映为 `(q,check(x))`，并证明像稠密、顺序保持及反射。
[QuotientIdentification](QuotientIdentification.lean) 证明两侧泛型的回拉都等价于 `H(q) ∧ G(x)`，
因此原布尔扩张与组合二步扩张同构。`Nh_d.quotient_l` 已合成这些实际映射，
得到同一个原名字所读 H 及其商泛型 K 的 **`M[G] ≅ M[H][K]`**。
[Kripke](../Collapse/AbsorptionProduct.lean) 已完成可数坍缩刻画；其中实际稠密树经 `Dmap_d.completion_l`
延拓为双射完全同态。[OrderIsomorphism](../../../SetTheory/Boolean/OrderIsomorphism.lean) 证明该序同构保持全部布尔运算及内部上确界。
[QuotientTrace](QuotientTrace.lean) 利用规范左伴随保持内部上确界，证明旧稠密条件在商中仍有被接受的加强。
[QuotientBasis](QuotientBasis.lean) 在中间模型中分离这些旧条件，其大小由旧条件域的实际单射限制取得。
[QuotientBasisDense](QuotientBasisDense.lean) 保持全部旧稠密集；
[QuotientBasisMap](QuotientBasisMap.lean) 证明主正则开图是到实际布尔商的稠密映射，包括相容性反射。
[DenseRange](DenseRange.lean) 分离实际稠密像集，按序数编号的最小原像构造其单射界。

[QuotientSmall](../Collapse/AbsorptionProduct.lean) 的 `Nh_d.fseq_quotient_l` 已实例化到原有限序列坍缩：
在同一个 M[H] 中得到大小不超过 j(κ) 的旧条件商表示，每个条件都迫使 j(κ) 是 j(ω) 的满射像，
并给出原大扩张与这个小商泛型扩张的同构。证书由实际部分函数泛型并图和逐坐标、逐值稠密性证明。
这里未假设旧正则开代数本身大小不超过 κ，也不假设首阶段之后 j(κ) 自动仍是不可数基数。

[SmallCardinal](../Collapse/AbsorptionProduct.lean) 已在小字母表 α<κ 的情形构造 κ 以下的条件域大小界，
证明商分解中同一个检查名字嵌入 j 保持 κ 的不可数基数性；κ 无需正则或不可达。
[Absorption](../Collapse/AbsorptionProduct.lean) 的 `Nh_d.fseq_absorption_l` 已接入 Kripke 稠密图，
回拉得到 M[H] 上的大坍缩泛型 G* 和保持地模型参数的 **M[G]≅M[H][G*]**。
[DenseGround](DenseGround.lean) 保留规范名字搬运，
[二步 check 展开](../TwoStep/Names/Check.lean) 用实际内部集合图保持嵌套规范值；
[ExtensionRealization](ExtensionRealization.lean) 将大泛型集合和全部对象的名字代表搬回原扩张。
[AbsorptionValue](../Collapse/AbsorptionProduct.lean) 自动从给定小泛型集合调用整条构造。
7.23 专用博弈及每条共尾良基分支的解码仍待完成。
