# 有限支撑与可数支撑迭代

[功能目录与构造历史索引](INDEX.md)

本页记录全库设施与迭代证明的实际边界。两类迭代共用内部名称的后继步；
极限阶段再分别施加模型内有限、模型内可数的支撑条件。

## 全库可复用设施

| 层 | 现有入口 | 可以直接复用的内容与边界 |
| --- | --- | --- |
| 预序与稠密映射 | [Order](Order/Basic.lean)、[Density](Order/Density.lean)、[Separative](Order/Separative.lean) | 加强方向、相容性、预稠密、稠密映射及分离商；原 `PO_dense` 要求像稠密，不是迭代阶段嵌入的合同 |
| 布尔装配 | [Completion](Boolean/Completion.lean)、[Boolean/Algebra](../Boolean/Algebra.lean) | 正则开完备化和完备布尔代数；尚无布尔迭代系统、阶段收缩映射或支撑极限 |
| 内部名称与真值 | [InternalNames](Internal/Names/Basic.lean)、[InternalTruth](Internal/Forcing/Truth.lean)、[InternalChoice](Internal/Extension/Choice.lean) | 任意地模型的名称、商解释、完整公式真值及 ZFC 保持；允许外部非良基和非标准 ω |
| 内部递归 | [Ord/Recursion](../../SetTheory/Ord/Recursion.lean)、[IterationRecursion](Iteration/Recursion/Basic.lean) | 已按原公式后继规则构造任意内部序数长度的支撑迭代，证明唯一性及精确前缀方程；不使用外部良基递归 |
| 内部层级与候选集合 | [Cumulative](../../SetTheory/Cumulative.lean)、[CumulativeRank](../../SetTheory/CumulativeRank.lean)、[CumulativeSelection](../../SetTheory/CumulativeSelection.lean) | 原 ZF 内实际构造累积层级，证明覆盖全部模型对象，并为非空可定义类构造最早层中的唯一见证集合 |
| 支撑大小 | [IterationSupport](Iteration/Condition/Support.lean)、[IterationSplice](Iteration/Condition/Splice.lean)、[Card/CountablePair](../../SetTheory/Card/CountablePair.lean) | 实际定义域的有限／可数支撑在限制、单坐标追加和前缀替换下保持，只需 ZF；可数族并仍由 `Card/CountableUnion` 在 ZFC 下处理 |
| 序数界 | [Card/Cofinality/Boundedness](../../SetTheory/Card/Cofinality/Boundedness.lean) | 小基数子集有界、函数像与族并有界，供极限阶段的支撑界证明使用 |
| 链条件 | [TwoStepCCC](TwoStep/CCC/Preservation.lean)、[IterationRecursionCCC](Iteration/FiniteSupport/RecursionCCC.lean)、[CohenIterationCCC](Applications/Cohen/FiniteSupport.lean) | 任意名称二步 CCC、有限支撑极限及完整内部迭代 CCC；参数化 Cohen 规则已有一键实例 |
| 可数闭性 | [InternalClosed](Closed/Basic.lean)、[IterationClosedInduction](Iteration/Closed/Induction.lean)、[CollapseIteration](Applications/Collapse/Iteration.lean) | 实际内部下降链、精确前缀下界、任意内部长度可数支撑闭性保持及不新增实数；参数化塌缩规则自动装配 |
| 内部模型编码 | [SetTheory/Internal](../SetTheory/Internal.lean) | 实际集合结构码、全部内部有限指令码、赋值空间、唯一真值表及满足关系集合；原 Project AST 编译与参数语义对应、全部内部公式码的自然数编号已完成；只需 ZF |
| 内部司寇伦闭包 | [SetTheory/Internal/Skolem](../SetTheory/Internal/Skolem.lean)：`ssk_hull_l` | 在 ZFC 中自动构造实际见证选择图与任意内部可数种子的最小可数闭包；覆盖非标准有限参数，空种子也返回非空闭包；通用闭包存在性、最小性与单步可数性保留 ZF 强度 |
| 内部可数初等子模型 | [SetTheory/Internal/ElementaryHull](../SetTheory/Internal/ElementaryHull.lean)：`selem_hull_l` | 一次返回实际内部可数载体、诱导结构码和完整内部初等性；全部内部公式及 ω→N 赋值均被覆盖。有限支撑、完整见证回拉及 Tarski–Vaught 双向等价只需 ZF |
| 初等子模型 | [SetTheory/Countable](../SetTheory/Countable.lean)、[SetTheory/ProjectReflection](../SetTheory/ProjectReflection.lean)、[InternalGenericTrace](Proper/Family/Trace.lean) | 外部可数反射、内部初等 `H(χ)` 子模型、全内部泛型提升及指定子集上的实际交集 club |
| 内部主条件与 properness | [InternalProper](Proper/Basic.lean)、[CohenProper](Applications/Cohen/Proper.lean)、[IterationProper](Iteration/Proper/Preservation.lean) | 模型内主条件与实际 club，CCC 的 properness 及完整可数支撑保持；参数化 Cohen 实例自动装配 |
| 可数支撑融合 | [IterationFusion](Iteration/Fusion/Basic.lean)、[IterationFusionRestriction](Iteration/Fusion/Restriction.lean) | 内部可数共尾前缀族的唯一融合、精确限制及实际条件的共尾前缀重构 |

`Model/ZFC/Pure/PureSetIterations` 等既有“迭代”模块服务于纯定义扩张和对象编码，
不是迭代力迫。内部名称的闭支撑 `Supp_d` 收集子名称，也不同于迭代条件的坐标支撑。

## 已实现的共同后继步

设首阶段为 `(B,R,z)`，`A,T` 是首阶段名称，条件 `b` 迫使 `T` 在 `A` 上自反、传递。
从 `A` 的内部闭支撑 `W` 构造地模型集合

\[
C=\{(p,s)\in B\times W:p\le b,\ p\ne z,\ p\Vdash s\in A\},
\qquad
(p,s)\le_C(q,t)\iff p\le q\ \land\ p\Vdash(s,t)\in T.
\]

`W` 只限制名称代表的取值范围。`two_step_fiber_l` 证明它仍覆盖解释后 `A` 的所有成员。
不要求 `A,T` 是规范名称，也不要求第二阶段偏序已存在于地模型。

| 接口 | 实际结论 |
| --- | --- |
| [InternalForcingRules](Internal/Forcing/Rules.lean)：`forces_bind_l`、`forces_regular_l`、`forces_mp_l` | 不使用泛型存在假设的代入交换、正则真值与局部蕴涵消去 |
| [TwoStepOrder](TwoStep/Order.lean)：`two_step_l` | 一次构造混合闭名称库 `W`、条件集 `C`、实际关系图 `S`，以及 `Cond_order_d M C S C`；固定库后三者的逐成员定义可直接审计 |
| [TwoStepGeneric](TwoStep/Generic/Projection.lean)：`two_step_lift_l` | 任意第一坐标加强均可提升为二步加强，保留第二坐标名称 |
| `two_step_generic_l` | 二步泛型的第一坐标向上闭包为原偏序上的地模型泛型 |
| `two_step_fiber_l` | 泛型纤维的成员恰好解释为第二阶段条件集的成员 |
| [TwoStepSecond](TwoStep/Generic/Second.lean)：`two_step_factors_l` | 自动提取两阶段泛型、名称解释及第二阶段合法条件序；第二阶段满足全部扩张内稠密要求 |
| [TwoStepComposition](TwoStep/Generic/Composition.lean)：`two_step_compose_l` | 组合原地模型泛型与扩张上的泛型，并精确恢复输入的两阶段滤子 |
| [TwoStepRecovery](TwoStep/Generic/Recovery.lean)：`two_step_recover_l` | 原二步泛型分解后再组合，逐条件恢复原滤子 |
| `two_step_local_l` | 从扩张内任意实际非空预序取得名称、泛型中的首阶段条件及非空二步序 |
| [InternalMixing](Internal/Maximum/Mixing.lean)：`mixing_l` | 对内部可定义、相容重叠处被迫相等的名称族构造实际混合名称 |
| [InternalMaximum](Internal/Maximum/Basic.lean)：`maximum_l` | 一个规范名称同时实现全部正条件上的原公式存在力迫，并返回规范固定点证书；只要求实际有限参数为名称 |
| [InternalUniqueMaximum](Internal/Maximum/Unique.lean)：`unique_maximum_l` | 原存在与唯一性公式被全局力迫时，在 ZF 内直接返回唯一规范见证名称；混合整个有界见证池，不选择极大反链 |
| [InternalCountermodel](Internal/Reflection/Countermodel.lean)：`forcing_zf_countermodel_l`、`forces_zf_l`、`forces_zfc_l` | ZF 与 ZFC 分别反射力迫失败，产生相应理论的真实反模型；每个正条件迫使原理论全部公理与模式 |
| [InternalGenericCriterion](Internal/Reflection/Criterion.lean)：`forces_of_generics_l` | 原模型的实际公式条件与有限参数同时反射；在 ZF 强度下把所有泛型中的名称构造提升为全局力迫证书 |
| [InternalOrderCongruence](Internal/Forcing/OrderCongruence.lean)：`forces_order_l`、`generic_order_l` | 条件域内逐边相同的关系给出相同的全部名称力迫及泛型性；`preord_order_l` 自动构造规范关系并返回这些证书 |
| [CohenNames](Applications/Cohen/Names.lean)：`cohen_names_l`、`cohen_names_unique_l` | 在原 ZF 内对任意添加量名称构造完整的规范名称三元组；原公式规格 `Cohen_names_d` 字面唯一 |
| [TwoStepTop](TwoStep/Top.lean)：`two_step_pointed_l` | 由条件集名称与指定顶名称构造唯一确定的混合闭库，并取得实际二步最大条件 |
| [TwoStepEmbedding](TwoStep/Embedding.lean)：`two_step_embed_l` | 构造首阶段锥到二步偏序的实际完全嵌入图，第一坐标是每个目标条件的约减 |
| [StageEmbedding](Stage/Embedding.lean)：`reg_embed_max_l` | 源极大反链的模型内实际映像仍为目标极大反链 |
| [StageComposition](Stage/Composition.lean)：`reg_embed_id_l`、`reg_embed_comp_l` | 模型内恒等嵌入及复合图；复合保留序反射、相容性和约减 |
| [InternalNameMapConstruction](Stage/NameMap/Construction.lean)：`nmap_exists_l`、`nmap_name_l` | 原 ZF 内构造任意标签关系的名称搬运图；范围约束自动给出目标名称闭支撑 |
| [StageNames](Stage/Names.lean)：`stage_nmap_l`、`stage_nmap_comp_l`、`stage_nmap_id_l` | 阶段图自动搬运名称并给出唯一性；两次搬运等于复合图搬运，恒等图删除零标签后仍与原名称被迫相等 |
| [StageAtomic](Stage/Atomic/Basic.lean)：`nmap_eq_l`、`nmap_mem_force_l`、`nmap_neg_eq_l`、`nmap_neg_mem_l` | 阶段像上的等号、隶属及其否定精确对应；反射由目标条件的源约减证明 |
| [StageGeneric](Stage/Generic.lean)：`reg_generic_l` | 目标泛型沿实际完全嵌入图回拉后，满足全部源模型内稠密要求 |
| [StageExtension](Stage/Extension.lean)：`stage_extension_l` | 源回拉泛型扩张到目标扩张的成员满覆盖单射，逐名称解释交换；保持原 universe 与任意外部非良基适用范围 |
| [InternalNamePair](Internal/Names/PairConstruction.lean)：`npair_l`、`nkpair_l` | 对全部泛型统一、在原模型中唯一的无序对与 Kuratowski 有序对名称；原 ZF 配对保持已迁移到此构造 |
| [TwoStepNameInterpretation](TwoStep/Names/Interpretation.lean)：`two_step_name_l`、`curry_val_entry_l` | 自动把二步名称转换为第一阶段名称，证明其在每个第一扩张内是第二阶段名称，并给出第一次求值后的精确成员与条目方程 |
| [InternalNamePairForcing](Internal/Names/PairForcing.lean)、[TwoStepNameForcing](TwoStep/Names/Forcing.lean) | 规范配对、有序对及转换后的第二阶段名称性均有对全部正条件有效的首阶段力迫证书，只需原 ZF |
| [TwoStepValuation](TwoStep/Names/Valuation.lean)：`two_step_valuation_l`、`curry_value_mem_l` | 一次装配原二步名称在双重扩张中的求值；总性、唯一性和组合滤子下的精确成员递归均已证明 |
| [TwoStepAtomicWitness](TwoStep/Atomic/Witness.lean)：`two_step_eq_pick_l`；[TwoStepGeneric](TwoStep/Generic/Projection.lean)：`two_step_common_l` | 二步等号的匹配见证及第二阶段共同加强均可保留被首阶段泛型接受的坐标；组合泛型的有向性已复用共同加强构造 |
| [TwoStepAtomicPush](TwoStep/Atomic/Push.lean)：`curry_forces_eq_l`、`curry_eq_push_l` | 原模型实际公式的条目归纳证明二步等号向嵌套第二阶段等号传输；只需 ZF，对全部首阶段泛型有效 |
| [TwoStepAtomicPull](TwoStep/Atomic/Pull.lean)：`curry_forces_eq_iff_l`、`curry_eq_pull_l` | 在原模型闭支撑上构造实际双模拟，反射嵌套等号；每个真实二步条件上的等号与嵌套等号精确等价 |
| [InternalNameDepth](Internal/Names/Depth.lean)：`entry_path_ind_l`、`qval_entry_path_l` | 任意固定正深度的内部公式归纳，以及第二阶段条目左坐标的三层原名称代表 |
| [TwoStepFlatConstruction](TwoStep/Flatten/Construction.lean)：`flat_exists_l`、`flat_name_l` | 原 ZF 内任意输入对象的实际摊平递归图；唯一性及目标名称闭支撑均已证明 |
| [TwoStepFlatValue](TwoStep/Flatten/Value.lean)：`flat_value_l` | 任意第二阶段名称的双重值由其原模型摊平名称精确实现，允许先规范化第二阶段关系 |
| [TwoStepIsomorphism](TwoStep/Names/Isomorphism.lean)：`two_step_iso_l` | 自动取得单次二步泛型扩张到双重扩张的成员结构双射，并保留逐名称求值；原部分映射入口已迁移到此同构接口 |
| [CohenIteration](Applications/Cohen/TwoStep.lean)：`cohen_step_l` | 统一构造条件集、关系、顶名称及阶段嵌入；每个泛型解释满足指定添加量的 CCC、基数保持与新实数证书 |
| [IterationStage](Iteration/Stage/Basic.lean)：`row_zero_l`、`row_successor_l` | 实际零阶段及任意名称后继的部分函数条件；顶不变，阶段完全嵌入按原对象给出，前缀及两类支撑保持 |
| [IterationCohen](Applications/Cohen/Successor.lean)：`row_cohen_successor_l` | 添加量为任意前阶段名称的真实 Cohen 坐标后继，自动装配名称、阶段偏序、原样嵌入和支撑保持 |

```lean
obtain ⟨W, C, S, hPool, hStep, hOrder⟩ := Internal.two_step_l O hZF hA hT hb hForced
-- hForced：b 迫使名称 T 在名称 A 上构成预序。

have hFirst := Internal.two_step_generic_l O hZF hStep hOrder hT hV
-- hV 是二步泛型；hFirst 是其第一坐标向上闭包的泛型性。

obtain ⟨e, hval, hmem, hinj, hsurj⟩ := Internal.two_step_iso_l
  O hZF hU hStep hOrder hA_value hT_value hR_eq L₂ hH hb
-- hU、hH 是两阶段泛型，hb : U b；hR_eq、L₂ 由第二阶段关系规范化取得。
-- hmem : ∀ a d, a ∈ d ↔ e a ∈ e d；hval 保留原二步名称的双重解释。

obtain ⟨A, T, t, hNames, hStep, hGeneric⟩ := Internal.cohen_step_l O hZFC hκ
-- hNames 保存三者的名称性、规范性和全局力迫规格；hStep 包含实际阶段嵌入。
```

构造和保持定理不增加外部可数性。只有调用已有 `internal_generic_l` 自动取得泛型时
才需要地模型枚举。名称、集合、序关系和模型均通过实际关系或 Prop 存在证书返回，
不定义全局不可计算实例。

## 继续实施的证明顺序

共同后继步的泛型双向分解、阶段嵌入、名称转换、摊平及完整扩张同构已完成。

给定原公式后继规则的完整内部超限递归存在性、唯一性及前缀方程也已完成。
两类支撑使用同一实际定义域，分别由 `Finite_d I ω S` 与
`CardinalLessOrEqual I S ω` 判断大小。

有限支撑极限的直接并刻画与 CCC 迭代保持已完成。内部主条件、club 版 properness、
CCC 实例、可数支撑主融合及全内部 N[G] 初等提升也已实现。完整区间迭代引理和
真实交集 club 已给出全部阶段的 proper 保持。可数闭迭代也已通过实际极限下界
与内部超限归纳完成全部阶段保持，并有任意内部长度的参数化塌缩实例。

有限支撑／可数支撑的极限规则与相应 CCC／properness 保持路线可参照
[Brendle 讲义第 3–4 讲](https://www.math.uni-hamburg.de/personen/khomskii/ST2013/bogotalecture.pdf)。
有限支撑 CCC 与可数支撑 properness 均已接入完整递归及实际 Cohen 规则。

## 泛型分解的证明边界

`InternalForcingCongruence` 在一个条件以下对全部原公式证明等同名称替换，并由此
把存在见证移入目标名称的内部闭支撑。`TwoStepDensity` 将被迫使的第二阶段稠密集
提升为地模型二步稠密集；`TwoStepDenseImage` 反向构造地模型稠密集的加权名称像。
两方向的泛型证明只对实际公式应用分离与替换，不以任意外部谓词作内部归纳。

第二阶段关系可含条件域外的无关条目。`two_step_factors_l` 自动限制到条件域，
同时返回逐边对应、`Cond_order_d` 及规范化前后的全部公式力迫对应；不额外要求
调用者提供已规范化关系。局部装配
`two_step_local_l` 保留实际 `b` 处的名称预序力迫证书，供后续泛型分解直接消费。

`cohen_step_l` 的后继名称在选取泛型之前统一构造，适用于全部正条件。模型内阶段
序列及支撑极限由后面的 `Row_system_d` 层提供。混合使用 `min_mem_compat_l` 证明相容重叠处的局部等号
力迫，最大值原理再由内部收集把可能见证收紧到一个模型内名称集。

全局有效性通过实际可数初等子模型反射内部力迫公式，再构造其泛型反模型证明。
反射层只要求外延性，并保持原模型满足的任意理论；ZF 与 ZFC 消费者分别保留
自身理论强度。`forces_of_generics_l` 还反射构造所依赖的实际原模型公式，已用于
规范名称配对、有序对与二步名称性；这些端点单独审计为原七条 ZF 证书边界。
原地模型不增加可数性或外部良基性前提。此处选择只出现在 Prop 存在证明中；
商赋值 `qenv_l` 直接取名称商类，不选择商的代表元。顶名称、阶段完全嵌入、
极大反链保持及嵌入复合均已实现。

名称搬运的 `Nmap_d` 以模型内标签关系和部分递归图定义。任意标签关系均可搬运，
因此同时涵盖单值阶段嵌入、零标签消去及多标签展开；存在性与唯一性均使用原
公式的内部条目归纳。两次搬运与标签关系复合严格一致。恒等阶段的零标签消去
另以实际内部双模拟证明等号力迫，未假定零元不属于条件集。

`StageReduction` 把目标条件的源约减写为实际原公式，并证明可同时加强到给定源界
以下。`StageAtomicPush`、`StageAtomicPull` 分离两个方向的内部双模拟，因而原子
等号和隶属的传输不要求阶段像稠密。肯定和否定的对应结合泛型判定，得到商类
等号的精确对应。`reg_generic_l` 通过实际向下像集合验证全部泛型要求。

`stage_extension_l` 自动给出从 `M[Pull_generic_d F V]` 到 `M[V]` 的单射 e，并满足
`y ∈ e(a) ↔ ∃c ∈ a, e(c)=y`，因此名称解释相容且像传递。它没有宣称全部一阶
公式的初等性；第二阶段可以改变 CH 等非有界断言。

两步名称的转换关系 `Curry_d B C σ σ*` 在原 ZF 内已有实际存在唯一性证明。它把
条目 `(τ,(p,s))` 换为以 p 加权的规范名称有序对 `(τ*,s)`；名称配对使用全部首
阶段条件，不依赖预先选取的泛型。第一阶段解释后，子名称与第二坐标分别求值，
且只保留被第一泛型接受的 p。闭支撑的转换值域经实际替换及名称装配，在第一
扩张中给出第二阶段名称的闭支撑。`Curry_val_d` 再通过两个实际泛型商解释该
名称，`two_step_valuation_l` 装配全部原二步名称的求值函数，并证明
`v ∈ e(σ) ↔ ∃(τ,c) ∈ σ, c ∈ U*H ∧ e(τ)=v`。函数只在 Prop 存在证明内取得，
不选取商代表。`curry_value_congr_l` 现已证明等价二步名称有相同双重值；
单次二步商类上的映射因而良定义。`curry_value_eq_l` 另核验双重值相等的反向
来源，摊平构造则给出满射性。`two_step_iso_l` 同时返回逐名称求值对应、
`a ∈ d ↔ e(a) ∈ e(d)`、单射与满射，即 `M[U*H]` 与 `M[U][H]` 的成员结构同构。
`TwoStepIsomorphism` 是统一同构入口。

正向等号传输使用实际 `curry_eq_m` 进行内部条目归纳，结论为
`(p,s) ⊩ x=y → p ⊩ (s ⊩ x*=y*)`。`two_step_common_l` 提升第二阶段共同
加强，`two_step_eq_pick_l` 给出首坐标被接受的子名称匹配；两侧匹配共用源名称
的子名称归纳假设。该证明没有对任意外部关系作良基归纳。

反向等号传输已把实际 `curry_pull_m` 分离为原名称闭支撑上的双模拟集合。
`iter_eq_truth_l` 把第二阶段等号重新给为首阶段条件证书；共同加强提升后，
`source_of_generics_l` 经有限参数反射取得原模型中的匹配见证。该证明仅用原 ZF，
既不假设原模型已有泛型，也不要求第二阶段关系预先去除域外条目。

名称摊平使用如下实际递归：若第一阶段名称 τ 的解释是第二阶段名称，则令其
二步摊平的条目为 `(flat(a),(p,s))`，其中 a 沿 τ 的三条原名称条目下降，
`(p,s)∈C` 且 p 迫使 `(a,s)∈τ`。三层下降来自 Kuratowski 有序对的两层成员
加上其所属名称的一层成员。`entry_path_ind_l` 对任意固定正深度提供原公式
归纳，`qval_entry_path_l` 核验三层代表，`flat_exists_l` 在原模型中收集部分图、
取并并加入新根。`flat_round_force_l` 在根条件以下给出全局还原力迫，
`flat_value_l` 再恢复任意第二阶段名称的双重值。完整超限递归及两种支撑的保持定理见后文。

## 部分函数坐标的实际后继装配

`Row_d α p` 指模型内的函数图 p，定义域包含于 α。`Coord_d p D` 精确表示其
定义域；`Row_supp_d I false ω p` 表示有限支撑，`true` 表示可数支撑。两个
判据都使用原模型内的单射与集合，不把非标准有限性改成外部有限性。

`Row_append_d α t p s q` 在 s 与指定顶名称 t 作为模型对象相等时令 q=p；
否则添加唯一条目 `(α,s)`。旧前缀精确恢复 p，追加结果还唯一确定 p 和 s。
`two_step_rows_l` 沿此编码构造二步偏序的实际集合双射与目标序关系，保序、
反射顺序并保持相容性；有限和可数支撑的保持均只需 ZF。

`row_zero_l` 构造只有空函数的零阶段。`row_successor_l` 从任意被迫为带顶预序
的名称构造下一阶段：旧条件以同一个模型对象进入新阶段，嵌入图逐边等于正
条件上的恒等图，顶条件保持不变。`Row_link_d` 同时返回原样包含、序反射、
实际限制的存在性、条件低于其前缀、限制投影单调，以及保留尾部的前缀加强。
`row_cohen_successor_l` 已提供添加量名称参数化的实际实例。

```lean
obtain ⟨e, B, R, he, hZero, hSupport⟩ := Internal.row_zero_l M hZF
-- hZero 是索引 e（空集）上的实际阶段；空函数 e 同时是其顶条件。

obtain ⟨D, V, G, hNext, hConstruction, hEmbed, hIdentity, hLink, hSupportNext⟩ :=
  Internal.row_successor_l hZF hStage hSuccessor hA hT ht hPreorder hTop
-- hLink.restrict 给出实际前缀；hLink.splice 提升任意旧前缀加强。
-- hConstruction : Row_next_d ...；它由原公式表示并唯一确定 D、V。
-- hSupportNext 对有限、可数两种模式同时成立。
```

对任意旧前缀 q 和条件 p，`Row_splice_d α q p r` 的实际成员方程为
`r = q ∪ {(i,s)∈p : i∉α}`。`row_splice_exists_l` 用原模型中的分离和二元并
构造 r；它的定义域包含于两份原支撑之并。`ZF.countable_union_two_l` 用两个
给定编号分别加零、一标记，再经 ω×ω 的内部计数压回 ω，故无需可数选择。
原可数积定理也已迁至 ZF，全部消费者同步迁移。

对后继阶段，若 `a=p↾α` 且 `q≤a`，`hLink.splice` 给出拼接后 r 仍是新阶段
条件，且 `r≤p`、`r≤q`。证明使用真实二步加强 `(a,s)↦(q,s)`，保留同一末
坐标名称。`row_link_id_l` 给出恒等阶段；`row_link_comp_l` 证明两段阶段链接
可以复合。复合时先替换中间阶段的前缀，再提升其上层尾部；拼接结合律保证
最后得到同一个 r，全部操作仍在原 ZF 内完成。

## 模型内阶段序列与支撑极限

`Row_system_d I δ F H e` 使用原模型中的两张序数序列 F、H，分别记录每个阶段的
条件集和序关系；不是任意外部函数族。所有阶段共用空条件 e，且任意两个按
包含排列的阶段都有 `Row_link_d` 证书。`row_system_extend_l` 只用 KP 即可把
带全部早期投影的实际阶段写入序列。名称后继使用阶段复合自动产生这些投影。

| 接口 | 实际结果 |
| --- | --- |
| [IterationLimit](Iteration/Limit/Basic.lean)：`row_system_zero_l` | 从实际空序列调用统一极限构造，得到只含零偏序的长度一阶段系统，同时提供两类支撑 |
| [IterationSystemSuccessor](Iteration/Stage/SystemSuccessor.lean)：`row_system_successor_l` | 以最后阶段的任意预序名称追加后继，返回模型内新序列、原样完全嵌入和全部支撑保持 |
| `row_system_cohen_l` | Cohen 添加量是最后阶段的名称，可依赖先前泛型；自动延长全部早期阶段链接 |
| [IterationLimit](Iteration/Limit/Basic.lean)：`row_limit_l` | 构造坐标上确界、有限／可数支撑极限偏序及每个旧阶段的完全嵌入与限制投影 |
| `row_system_limit_l` | 在 `δ=⋃δ` 时把该极限写回内部序列，保留全部旧条目和所选支撑，随后可以继续作名称后继 |

具体地，先取 σ=⋃δ，再令极限条件为定义域包含于 σ 的实际部分函数 p，要求
其定义域具有指定支撑大小，且每个 `p↾α` 都属于 F 在 α 记录的阶段。序关系
逐阶段比较这些实际限制。若 δ 有最后一个索引，σ 就是该索引；若 δ 为极限
序数，σ=δ。`false` 选择有限支撑，`true` 选择可数支撑。

实际集合存在性使用两次取并：所有极限条件的每个有序对，都已出现在某个阶段
条件中。因此先取所有阶段条件图条目的集合界，再从其幂集按 `row_lim_m` 分离。
每个旧阶段原样进入极限。替换前缀时，在该阶段以前使用旧投影的单调性，在其后
使用限制与拼接的交换律及旧阶段提升；由此证明极限中的拼接仍是共同加强。
`row_link_embed_l` 进一步构造实际恒等嵌入图，直接接入名称搬运、极大反链保持
及泛型回拉。上述通用构造均只用原 ZF，不要求模型外部良基或外部可数。

```lean
obtain ⟨σ, D, V, hConstruction, hLimit, hStages⟩ :=
  Internal.row_limit_l hZF hSystem hω true hSupport
obtain ⟨hProjection, G, hIdentity, hEmbedding⟩ := hStages α B R hB hR
-- G 是旧阶段到可数支撑极限的实际完全嵌入图。
-- hConstruction.sup、.conditions、.relation 给出精确集合及序关系方程。
```

## 后继与极限的确定构造式

`Name_hull_d B A t S` 表示包含 A、t 的最小闭支撑。先取任一共同闭支撑作为
集合界，再按“属于每个包含 A、t 的闭支撑”的实际公式分离，故 S 在原 ZF 内
存在且唯一。实际后继使用 `Name_pool_d B A t W`，即模型内的 W = 𝒫(S × B)。
S 的闭性给出 S ⊆ W；W 中名称的直接子名称来自 S，因此加权混合仍属于 W。
`name_pool_m` 是这条确定构造的实际原公式，存在性只需 ZF、唯一性只需外延性。
普通二步、带顶二步、Cohen 与完整内部递归均使用此库。`Two_step_d` 显式保存
关系集合的有序对图性质，`two_step_pool_unique_l` 同时确定 W、C、S。

给定具体的原模型名称 A、T、t，`Row_next_d` 唯一确定后继条件集和关系图。
其原公式为 `row_next_m`，唯一性入口是 `row_next_unique_l`，而 `row_successor_l`
及系统、Cohen 消费者直接返回该证书。极限对应 `Row_limit_d`、`row_limit_m` 和
`row_limit_unique_l`，同时确定 σ、D、V。这些存在性来自实际构造；唯一性只需
外延性，且不引入新的选择依赖。

这里的确定性以实际输入名称为参数。下面的规范代表进一步消除了同一全局等号
类中的名称差异；语义规格若有多个不同见证值，仍需额外的确定选择构造。

## 固定前缀的见证选择与混合闭合

`name_pool_mix_l` 混合任意实际公式选出的库内名称族；相容重叠处只须被迫相等。
`mixing_l` 同时保留直接子名称的来源，幂集界因此对混合闭合。没有额外假设
名称库闭合，也不需要扩大内部递归的理论强度。

对任意名称 v，混合所有在某条件上被迫等于 v 的库内名称。重叠处的相容性
来自等号传递；若 p 迫使 v∈A，成员力迫给出的这些代表在 p 以下稠密。等号的
正则性遂给出一个 s∈W，使原条件 p 本身迫使 s=v。此证明只需 ZF，且同一 s
服务于全部这样的 p。一般有界存在式先由最大值原理选择见证，再用上述代表
送回 W；这一步使用 ZFC，但第一条件仍原样保留。

| 入口 | 结论与强度 |
| --- | --- |
| [InternalNamePool](Internal/Maximum/Pool.lean)：`name_pool_exists_l`、`name_pool_mix_l` | 实际构造唯一确定的名称库，证明可定义相容名称族的混合闭合；ZF |
| [InternalNamePool](Internal/Maximum/Pool.lean)：`name_pool_represent_l` | 一个库内名称在每个迫使 v∈A 的原条件上等于 v；ZF |
| [InternalBoundedMaximum](Internal/Maximum/Bounded.lean)：`name_pool_maximum_l` | 一个库内名称同时实现全部正条件上的任意原有界存在式；ZFC |
| [TwoStepWitness](TwoStep/Witness.lean)：`two_step_represent_l`、`two_step_witness_l` | 返回第一坐标精确为输入 p 的真实二步条件；分别只需 ZF、ZFC |
| [TwoStepWitness](TwoStep/Witness.lean)：`two_step_lower_name_l` | 把指定的第二坐标加强名称提升为二步加强，保留指定第一坐标；ZF |
| [IterationWitness](Iteration/Names/Witness.lean)：`row_next_represent_l`、`row_next_witness_l` | 返回实际坐标后继条件 q，证明 q↾α=p，并给出坐标等号／正文力迫；分别只需 ZF、ZFC |
| [IterationWitness](Iteration/Names/Witness.lean)：`row_next_lower_name_l` | 在给定旧条件以下装配后继加强，指定的新前缀 p 精确保留；ZF |

```lean
obtain ⟨s, q, hs, hAppend, hq, hPrefix, hFormula⟩ :=
  Internal.row_next_witness_l hZFC hStage φ ρ i hNames hNext hp hExists
-- ρ.bound i 是迭代条件集名称；hExists 是 p 上的实际有界存在式力迫。
-- hq : q∈D，hPrefix : p=q↾α，hFormula 在同一 p 上成立。

obtain ⟨s, q, hs, hAppend, hq, hLower, hPrefix, hEqual⟩ :=
  Internal.row_next_lower_name_l hZF hStage hNext hT hr ha hOldAppend hp hpa hv hMember hBelow
-- v 是指定的第二坐标加强名称；输出 q≤r，且 q↾α=p。
```

这些接口消费实际 `Row_next_d`，其名称库与条件域由现有递归及 Cohen 装配自动给出。
它们完成后继层的固定前缀步骤；后文的泛型初等提升与主条件递归将其接入完整迭代引理。

## 累积层级与名称的规范代表

`ZF.v_exists_l` 按统一原公式 `V_α = ⋃_{β∈α} P(V_β)` 构造每个内部序数处的实际
层级。`v_successor_l` 核验后继幂集方程，`v_limit_mem_l` 核验极限并方程；
`v_cover_l` 对实际公式作成员归纳，收集成员的层级界并取上确界，证明每个模型
对象属于某层。这里的归纳始终发生在模型内部。

对任意非空的原公式类，`ZF.v_min_exists_l` 在第一个含见证的层中分离全部
见证，`v_min_unique_l` 保证层索引和候选集合都唯一。将此构造用于所有与给定
名称全局被迫相等的名称，再对候选名称图取并，得到 `Norm_name_d`。
`norm_name_l` 用原子力迫的双向匹配证明取并后的名称与输入全局相等；
`norm_name_congr_l` 证明全局等价的输入得到字面相同的规范名称。

```lean
obtain ⟨q, hNormal, hFixed, hq, hEq⟩ := Internal.norm_name_exists_l O hZF ht
-- hNormal 记录 q 是 t 的规范名称，hFixed 记录 q 规范化后仍是自身。
-- hEq 在所有正条件上给出 q 与 t 的原等号力迫。
```

这套规范化只需原 ZF。`maximum_l` 已直接返回规范固定点，`cohen_names_l`、
`cohen_step_l` 及两个坐标系统消费者均传播 A、T、t 的固定点证书；一般最大值
原理仍保留 ZFC 前提。通用 `pred_m`、`binary_pred_m` 及满足关系已从力迫层迁入
`SetTheory.Definitional.Project.Predicate`，模型内类构造与原力迫消费者共用同一
实现，未保留旧命名空间别名。

`witness_pool_l` 用原收集模式构造实际名称，覆盖每个条件上出现的原公式见证，
并保留该条件作为条目权重。一般最大值与唯一见证的装配共用这个池。
`unique_m φ` 是“φ 至多有一个见证”的实际原公式；`forced_unique_l` 实例化两个
名称并取得等号力迫。若所有正条件都迫使存在与唯一性，`unique_maximum_l` 先
混合有界池中的局部见证，再规范化，返回唯一名称及其全局见证性质。这里的
混合相容性来自已证明的唯一性，整个过程只需要 ZF。

Cohen 规格已经补上关系集合的完整有序对图性质。`cohen_spec_unique_l` 和
`cohen_spec_top_unique_l` 只用外延性证明条件集、关系图与顶条件唯一；这些实际
模型定理再通过 ZF 有效性转为原唯一性公式的力迫证书。`cohen_names_l`、
`row_cohen_successor_l` 和 `row_system_cohen_l` 因此全部降低到 ZF。包含 CCC、
基数保持等结论的 `cohen_step_l` 仍使用 ZFC。

`Cohen_names_d` 把名称性、三个规范固定点和全局 Cohen／预序／顶力迫合为完整
规格，`cohen_names_m` 及 `cohen_names_sat_l` 给出其实际原公式。`cohen_names_l`
现在同时返回三元组存在性与字面唯一性；后者依次恢复关系图、条件集和顶的
原存在公式，并消费三次唯一见证混合的结论。存在引入共用只要求向下闭性的
`forces_exists_intro_l`，一般最大值原理也已迁入同一规则。

`Row_cohen_d` 进一步组合该规格与 `Row_next_d`，由给定添加量唯一确定整个
后继条件集 D 和序关系 V。`row_cohen_m` 是其原公式，`row_cohen_unique_l`
证明唯一性；坐标和系统的 Cohen 后继入口均直接返回这个构造证书。

```lean
obtain ⟨D, V, G, hNext, hCohen, hEmbed, hIdentity, hLink, hSupport⟩ :=
  Internal.row_cohen_successor_l hZF hStage hSuccessor hκ
-- hCohen : Row_cohen_d ...；已把规范名称及后继偏序的实际构造一起封装。
```

## 完整内部超限递归

`Row_rule_d I k ω φ ρ` 消费一条实际原公式后继规则及其已证明的存在唯一性、
阶段链接和支撑保持。φ 的参数包括当前长度、整个条件集历史 F、关系历史 H
以及共同空条件 e，因此规则可以读取先前阶段，生成依赖前面泛型的名称。
`cohen_rule_l` 已用现有 Cohen 装配实现一个具体规则；它在每个后继把指定
地模型添加量 κ 转为该阶段的规范名称。

`row_op_s` 以历史中偏序对组成的内部序列作输入。`row_history_exists_l` 通过
原替换模式投影出 F、H，投影与限制交换。合法后继调用 φ；零与极限调用
统一支撑极限。为应用一般递归定理，算子对无效输入取空集；
`row_recursive_good_l` 对实际 `row_invariant_s` 作内部超限归纳，证明所有递归
前缀都合法，故实际轨迹不会进入这个补全分支。

| 接口 | 结果 |
| --- | --- |
| [IterationRecursion](Iteration/Recursion/Basic.lean)：`row_iteration_l` | 从原公式规则一次构造给定内部长度 α 的整个阶段系统，全部阶段都满足所选支撑与前缀链接 |
| `row_iteration_unique_l` | 相同规则、参数和长度得到字面相同的条件集与序关系序列 |
| `row_iteration_step_l` | 任一阶段的历史是同一迭代的实际限制，并满足真实后继或支撑极限方程 |
| `cohen_iteration_l` | 自动取得 ω、空条件和完整参数化 Cohen 迭代，`false` 为有限支撑，`true` 为可数支撑 |

```lean
obtain ⟨ω, e, F, H, hω, hIteration⟩ := Internal.cohen_iteration_l hZF true κ hα
have hSystem := hIteration.1
have hSupport := hIteration.2.1
-- α 是序列长度，阶段索引为 β∈α。κ 是每个后继的地模型添加量。
```

`Row_iteration_d` 同时保存阶段系统、支撑及实际递归历史；`row_iteration_s` 给出
整个迭代的原公式规格。所有存在性和唯一性只用原 ZF，保留外部非良基、内部
非标准地模型的适用范围。有限支撑直接并刻画及 CCC 保持见下节；可数支撑
properness 保持由末节的实际交集 club 与完整区间归纳给出。

## 有限支撑直接并与 CCC 保持

设阶段索引 δ 非空，σ=⋃δ。`ZF.finite_union_bound_l` 对实际有限集合公式作插入
归纳，证明 σ 中的有限坐标集包含于某个 α∈δ。有限支撑极限条件 p 因而满足
p↾α=p，故 p 已属于该阶段。`row_limit_union_l` 同时返回

\[
p\in P_\infty\iff\exists\alpha\in\delta\;p\in P_\alpha,\qquad
p\le_\infty q\iff\exists\alpha\in\delta\;
p,q\in P_\alpha\ \land\ p\le_\alpha q.
\]

这里的序关系只取各阶段条件域内的条目。δ=0 时极限含空条件，因此直接并定理
要求索引非空；完整迭代的零阶段仍由空函数单独核验。直接并和尾部合并仅用 ZF。

| 接口 | 结论与强度 |
| --- | --- |
| [IterationDirectUnion](Iteration/FiniteSupport/DirectUnion.lean)：`row_limit_union_l` | 非空阶段系统的有限支撑极限，条件与序关系精确等于早期阶段直接并；ZF |
| [IterationAmalgamation](Iteration/FiniteSupport/Amalgamation.lean)：`row_amalgam_l` | 指定前缀相容且其外支撑不交时，两个有限支撑条件相容；ZF |
| [InternalCCCPredense](CCC/Predense.lean)：`ccc_predense_l`、`ccc_family_l` | CCC 偏序中任意实际条件族有可数预稠密子族，实际投影图可取可数原始代表；ZFC |
| [TwoStepCCC](TwoStep/CCC/Preservation.lean)：`two_step_ccc_l` | 首阶段 CCC、第二阶段名称被迫 CCC，则真实二步偏序 CCC；ZFC |
| [IterationCCC](Iteration/FiniteSupport/CCC.lean)：`row_limit_ccc_l` | 非零极限前的全部阶段 CCC，则实际有限支撑极限 CCC；ZFC |
| [IterationSystemCCC](Iteration/FiniteSupport/SystemCCC.lean)：`row_system_ccc_l` | 每个后继来自实际被迫 CCC 的名称时，有限支撑系统的全部内部阶段 CCC；ZFC |
| [IterationRecursionCCC](Iteration/FiniteSupport/RecursionCCC.lean)：`row_iteration_ccc_exists_l` | 从原公式后继规则一次构造整个有限支撑迭代及全部阶段 CCC；ZFC |
| [CohenIterationCCC](Applications/Cohen/FiniteSupport.lean)：`cohen_iteration_ccc_l` | 只输入内部序数长度与地模型添加量，自动返回实际 Cohen 迭代及全部阶段 CCC；ZFC |

极限证明先对原阶段序数公式作内部归纳：支撑并的最大坐标只出现在一侧，另一侧
已属于更早阶段；合并早期前缀后，`Row_link_d.splice` 保留剩余尾部。随后对
“某个前缀以外至多 n 个坐标”作内部自然数归纳，同时量化所有前缀。取可数个
前缀预稠密代表，它们的坐标并可数；其余反链元素必须共享其中一个尾坐标。
把该坐标移入更长前缀，尾支撑界降一。最后对 n∈ω 作可数覆盖。

二步证明构造被第一泛型接受的旧反链索引名称，以及映到第二坐标的实际图名称。
第二坐标共同加强经 `two_step_common_l` 提升，保证该图是到第二阶段反链的单射。
索引名称因此被迫可数；最大值原理生成实际单射名称，首阶段 CCC 对每个自然数值
的可能旧原像计数，得到原二步反链可数。两处泛型论证均经实际原公式反射，
不要求原地模型外部可数。

`Row_ccc_rule_d` 记录后继的真实名称、预序与 CCC 力迫以及 `Row_next_d` 编码。
`row_iteration_ccc_l` 从已构造的递归前缀自动提取这些输入，再应用后继和极限定理。
`cohen_rule_ccc_l` 已验证现有规则；其中的添加量名称由现有规范名称构造产生。

```lean
obtain ⟨ω, e, F, H, hω, hIteration, hCCC⟩ := Internal.cohen_iteration_ccc_l hZFC κ hα
have hStageCCC := hCCC δ D V hD hV
-- hD、hV 是 F、H 在索引 δ 的实际条目；阶段索引满足 δ∈α。

obtain ⟨F, H, hIteration, hCCC⟩ :=
  Internal.row_iteration_ccc_exists_l hZFC hω he hα hRule hCccRule
-- 通用规则可以读取整个历史并生成依赖前面泛型的任意 CCC 名称偏序。
```

支撑大小、可数性和超限归纳均在原模型内部解释。所有新构造仍以 Prop 存在证书
返回，允许外部非良基及非标准 ω；没有新增不可计算数据实例。

## 内部主条件、club 与可数支撑融合

`Mstr_d B R z N q` 要求 q 为正条件，且每个属于 N 的实际稠密集 D 都满足
D∩N 在 q 以下预稠密。`mstr_generic_l` 证明任意接受 q 的泛型确实在 N 内遇到
这些 D；`mstr_lower_l` 证明加强保持主条件性。N 始终是地模型中的集合。

`Cc_club_d I ω X C` 的成员是 X 的内部可数子集；无界性对每个内部可数种子成立，
闭性接收模型自身 ω 上的实际递增序列及其并。`Proper_d` 使用 club 主条件刻画：
对每个包含条件域的 X，都有这样的 C，使每个 N∈C 中的正条件可加强为 N 主条件。
`proper_m`、`proper_exists_m` 是相应的实际原公式，可直接进入名称力迫。

`ZFC.cc_hull_l` 实际构造可数多值图的可数闭包：幂集上的一步闭包由分离产生，
沿内部 ω 迭代并取并。`ccc_mstr_hull_l` 为每个稠密集选择可数预稠密子集，
对所得实际图作此闭包。所得 N 包含指定种子，且每个正条件都是其主条件。
这些集合族的闭无界性由 `ccc_proper_l` 完整证明。

| 入口 | 已证明的范围 |
| --- | --- |
| [InternalMaster](Proper/Master/Basic.lean)：`mstr_generic_l` | 泛型中的主条件意义；ZF |
| [InternalMasterCCC](Proper/Master/CCC.lean)：`ccc_mstr_l` | 任意 CCC 偏序及内部可数种子，自动返回实际内部可数主条件集合；ZFC |
| [InternalProper](Proper/Basic.lean)：`ccc_proper_l`、`proper_mstr_l` | 实际主条件 club 证明 CCC ⇒ proper；给定 properness 后自动装配含指定种子的主加强 |
| [CohenProper](Applications/Cohen/Proper.lean)：`cohen_names_proper_l` | 任意添加量名称的 Cohen 后继在所有正条件上被迫满足上述 properness 原公式；ZFC |
| [IterationFusion](Iteration/Fusion/Basic.lean)：`row_fusion_l` | 实际可数共尾前缀图的并是唯一可数支撑极限条件，保留全部前缀并低于它们；ZFC |
| [IterationFusionRestriction](Iteration/Fusion/Restriction.lean)：`row_fusion_restrict_l`、`row_fusion_reconstruct_l` | 从实际极限条件自动构造融合接口的前缀族，并证明取并精确恢复原条件；ZF，重构本身不要求指标可数 |

融合输入 `Row_fusion_d` 包含模型内指标集 J、条件图 Q、共尾性及精确前缀方程。
它不是“存在适当融合序列”的保持性假设。`row_fusion_restrict_l` 已为任意实际极限
条件构造实例；`row_pr_limit_thread_l` 进一步按全部稠密要求实际递归构造主前缀图 Q。

```lean
have hProper := Internal.ccc_proper_l O hZFC hω hCCC
obtain ⟨N, q, hAN, hpN, hN, hqp, hMaster⟩ :=
  Internal.proper_mstr_l (ZFC.models_zf_l hZFC) hω hProper hA hp hpz

obtain ⟨q, hq, hUnion, hPrefixes, hUnique⟩ :=
  Internal.row_fusion_l hZFC hSystem hω hSupport hLimit hFusion hJ
```

**证明边界：**内部集合结构与满足关系编码已由
[SetTheory/Internal](../SetTheory/Internal.lean) 实际构造，含模型内非标准有限公式码。
原 Project AST 已编译到该满足关系；所有内部公式码的可数性已通过内部 ω 递归证明。
内部司寇伦选择图、最小可数闭包和实际初等子模型均已构造。有限支撑把见证闭性
提升到全部内部赋值，原公式归纳证明完整内部初等性，覆盖非标准公式码。
`N[G]` 的实际集合、内部可数性及全部内部公式码的统一初等提升见下节。
实际 proper club 见证已能在包含它的同一个 `N≺H(χ)` 中选择主加强；`H(χ)` 的
泛型对应与 `N[G]` 后继主条件选择见后文。完整 proper 迭代引理及可数支撑
保持已经完成；二步主条件的两个坐标也已完成完整双向分解。
后继名称库的混合闭合、固定条件见证及固定前缀加强均由实际构造证明，
通过内部超限归纳接入一般 proper 迭代引理。
标准主条件提升与极限归纳的目标形式见
[Brendle 讲义引理 4.7、主引理 4.8 与定理 4.9](https://www.math.uni-hamburg.de/personen/khomskii/ST2013/bogotalecture.pdf)。

## N[G] 的集合与存在见证提升

`ng_set_l` 在泛型扩张内部构造实际集合，成员方程为

\[
x\in N[G]\iff\exists\tau\in N\;(\tau\text{ 是名称}\land\tau_G=x).
\]

`ng_name_exists_l` 先分离 N 中的名称，再把每个名称与全部条件配对，因此不要求
偏序有顶。`ng_surjection_l` 收集名称对 `(check(s),s)`，构造扩张内从地名称集合的
规范像到 `N[G]` 的求值满射图。`ng_countable_l` 用原像的最小自然数编号取得单射，
证明内部可数性保持；这些步骤只用 ZF，允许外部非良基和内部非标准地模型。

对指定原存在公式 `∃x φ(x,ρ)`，`ng_witness_data_l` 在泛型之前实际构造加权见证池
W 和判定其非空纤维的稠密集 D。`Ng_witness_d.generic_l` 接收传递环境 X 中的内部
初等 `N`，以及 `W,D∈N`。泛型接受 N 主条件后，在 `D∩N` 中取得条件 p；若扩张
满足该存在式，判定的否定分支与泛型共同加强矛盾。内部初等性随即把 W 中 p 的
纤维见证取回 N，所得名称的泛型值就是 `N[G]` 中满足正文的真实见证。此证明仅需
ZF，N 本身不要求传递。`selem_source_l` 使用共同的内部编译码，确保反射来自已有
完整内部初等性；没有另加外部初等性假设。

[InternalGenericWitnessHull](Proper/Generic/WitnessHull.lean) 的 `ng_witness_hull_l`
从 properness、任意内部可数种子、正条件 p 及原公式 φ，自动构造反射层、可数
初等 N 及 N 主加强 q≤p。同一个 N 支持所有来自 N 的名称参数 ρ；接受 q 后同时
装配实际可数 `N[G]` 和上述见证提升。

通用证明位于 [LevyReflection](../SetTheory/LevyReflection.lean)。`ZF.lr_finite_l`
先对 `ng_data_m φ` 和 `ng_exists_m φ` 两条模板统一构造 V_α；它们分别编码完整
见证池方程和池的存在。`ng_witness_reflect_l` 随后用内部初等性把任意 N 参数下
的 W、D 取回 N，再由反射等价式确认它们满足原地模型中的真实池方程。
`selem_club_hull_l` 在指定 proper club 内构造此 N，故同一个集合同时具有初等性
和主条件。有限反射及池回拉只需 ZF；自动选择 N 的装配层使用 ZFC。

```lean
obtain ⟨X, c, T, N, d, S, q, hTransitive, hSubstructure, hElementary,
    hSeed, hCountable, hqp, hMaster, hLift⟩ :=
  Internal.ng_witness_hull_l O hZFC hω hProper hSeedCountable hp hpz φ
obtain ⟨Y, w, hMembers, hOmega, hYCountable, hWitness⟩ := hLift U hGeneric hq
-- Y 是实际 N[G]；hWitness ρ hParamsInN η hVal 对任意 N 参数把存在见证取到 Y 中。
```

此入口固定原公式 φ，正文在整个泛型扩张中解释。下面的内部初等入口则比较两份
实际集合结构，并统一量化全部内部公式码。

## 全部内部公式码的 N[G] 初等提升

[InternalGenericElementaryHull](Proper/Generic/ElementaryHull.lean) 的
`ng_elementary_hull_l` 只接收 ZFC 地模型、proper 偏序、内部 ω、可数种子和正条件。
它返回实际传递环境 X、内部可数初等 N、主加强 q≤p，并对每个接受 q 的泛型返回
整个 `N[G]≺X[G]` 的 `Selem_d` 证书。两边载体都有精确名称求值成员方程；
`X[G]` 传递，`N[G]` 在扩张内部仍可数。

证明的三个实质步骤如下：

1. `image_fseq_l` 在目标模型的实际公式上作内部 ω 归纳，证明地有限列空间的规范像
   就是目标的有限列空间。`ng_fseq_name_l` 沿实际求值满射回拉任意内部有限参数列，
   再用唯一的 `Nseq_d` 构造整列名称。`image_scode_l` 同样证明全部内部公式码保持。
2. `ssk_mem_s` 统一表达集合隶属结构中的内部司寇伦见证。`ng_operations_l` 实际构造
   判定图与条件下的见证选择图；两图均对内部标签及有限参数列索引。
   `ZFC.fc_club_refine_l` 在 proper club 中依次闭合它们，再构造地模型初等 N。
3. `ng_operation_lift_l` 用主条件取得 p∈N∩G，把 p 追加到原名称参数列，取得 N 内
   见证名称。`ng_elementary_l` 据此建立内部司寇伦闭性并应用完整 Tarski–Vaught。

有限列、名称装配、公式码绝对性和最后的提升都只需 ZF；两张实际选择图以及
自动选择 N 使用 ZFC。内部 ω 可以外部非标准，地模型可以外部非良基；没有新增
选择函数实例、反射公理或全宇宙真值假设。

```lean
obtain ⟨X, c, T, N, d, S, q, hX, hMembership, hSub, hElem,
    hSeed, hCount, hqp, hMaster, hLift⟩ :=
  Internal.ng_elementary_hull_l O hZFC hω hProper hSeedCountable hp hpz
obtain ⟨Y, Z, v, c', T', d', S', hY, hZ, hv, hYTransitive,
    hZCountable, hMembership', hSub', hElem'⟩ := hLift U hGeneric hq
-- hY、hZ 分别精确刻画 X[G]、N[G]；hElem' 覆盖全部内部公式码及赋值。
```

此入口仍保留任意传递环境的用途；实际 `H(χ)` 使用下面的专门装配入口。
指定公式在整个扩张中的见证提升仍使用 `ng_witness_hull_l`。

## H(χ) 对应及固定模型中的 proper 主条件

`SetTheory.Hereditary` 中 `Hmem_d I χ x` 表示 `TC({x})` 单射到某个 `μ∈χ`，
`H_d I χ H` 给出精确成员方程。内部秩像证明该类受 `V_χ` 所界，从原分离公理
构造实际 H；没有把秩界放进定义来缩小 H。`ZFC.h_cover_l` 自动选取包含给定
集合的不可数正则 H，使用 Hartogs 后继，不要求不可达基数。

[HereditaryCorrespondence](Proper/Hereditary/Correspondence.lean) 的 `h_generic_l` 证明：
若 χ 不可数正则、`B∈H(χ)`，则地 H(χ) 中名称的全部泛型值恰好是扩张的 `H(eχ)`，
且 `eχ` 仍正则。证明中两个方向的强度分别为：

- `hmem_value_l` 只用 ZF，把地传递闭包及其序数大小界传给泛型值。
- `h_name_reduce_l` 在 ZFC 中对原名称作实际条目公式归纳。被迫的小传递容器的
  单射值与条件索引子名称，统一选择的像仍小，再重新装配等价名称。
- `small_regular_l` 把反链界推广到条件集的任意大小界，通过新小集合的地覆盖
  排除较大正则基数的塌缩及新短共尾列。

[InternalHereditaryHull](Proper/Hereditary/Hull.lean) 的 `ng_hchi_hull_l` 自动完成
上述选择及全内部初等提升：

```lean
obtain ⟨χ, H, c, T, N, d, S, q, hχ, hωχ, hH, hModel, hSub, hElem,
    hSeed, hCount, hqp, hMaster, hLift⟩ :=
  Internal.ng_hchi_hull_l O hZFC hω hProper hSeedCountable hp hpz
obtain ⟨e, Y, Z, v, c', T', d', S', hCheck, hMembers, hInjective,
    hχ', hH', hY, hZ, hv, hYTransitive, hZCountable, hModel', hSub', hElem'⟩ :=
  hLift U hGeneric hq
-- hH'：Y 是扩张中实际的 H(eχ)；hElem'：整个 N[G]≺H(eχ)。
```

`selem_omega_subset_l` 用内部归纳证明 `ω∈N` 蕴含 `ω⊆N`；
`selem_countable_subset_l` 通过反射实际小单射图证明 `A∈N` 且 A 内部可数时 `A⊆N`。
`selem_club_mem_l` 据此把 `C∩N` 化为内部可数有向族，证明 `C∈N` 时 `N∩X∈C`。
链化依赖通用的 `ZFC.indexed_choice_l`，其序列沿模型自己的 ω 编码。

`pr_base_exists_l` 从 properness 在 `B∪𝒫(B)` 上实际构造 club；
`pr_base_master_l` 在包含这个 club 的固定 N 中取得任意正条件的主加强。
`pr_name_exists_l` 对被迫 proper 的后继一次构造 ω、底集和 club 名称，
[InternalGenericProper](Proper/Generic/Successor.lean) 的 `ng_next_master_l` 将这些
名称加入种子，并自动返回地阶段主加强及每个泛型中的 N[G] 后继主条件选择。

## 实际二步主条件与统一阶段模型

[TwoStepMaster](TwoStep/Proper/Composition.lean) 的 `two_step_master_l` 证明：首阶段的 N 主条件
与它迫使的 N[G] 主条件合成为真实二步 N 主条件。关键的 `ng_member_pick_l`
将 N[G] 中的名称成员取回 N 内的原名称条目；证明先在 H(χ) 内构造实际小支撑
双模拟，再反射原子判定集及条目见证。这里没有假定 H(χ) 满足幂集公理。

`two_step_master_first_l` 只用 ZF 证明二步主条件的首坐标仍是 N 主条件。
`two_step_master_second_l` 进一步在原模型中证明首坐标迫使第二坐标为 N[G] 主条件；
`two_step_master_decompose_l` 自动构造 N[G] 名称并返回完整双向等价，详见末节。
[TwoStepMasterExtension](TwoStep/Proper/Extension.lean) 的自动入口只接收实际二步
装配、地 properness、后继 properness 力迫、种子和旧条件：

```lean
obtain ⟨N, y, hSeed, hCount, hyx, hMaster⟩ :=
  Internal.two_step_master_extension_l O hZFC hω hProper hSeedCount
    hStep hPool L hRelationName hx hForcedProper
-- y 是原二步条件集中的实际条件，y≤x，并且是同一个 N 的主条件。
```

该接口适用于任意外部大小、非良基地模型。证明在可数反射模型中先把每个泛型
中的存在性转成真实力迫，再使用名称库最大值原理；有限参数反射把原集合存在
结论传回地模型。它给出含任意可数种子的主加强，并不单独宣称已经构造 proper club。

[InternalGenericFamily](Proper/Family/Basic.lean) 的 `ng_family_hull_l` 从两张实际
阶段函数图一次构造 H(χ) 与共同的 N。`ng_joint_exists_l` 只生成两张共同运算图；
阶段编号作为内部有限参数列的末项，`ZF.fc_slice_l` 证明含该编号的闭集自动对
该阶段切片闭合。因此同一 N 支持其所有成员阶段和该阶段的任意 N 主条件：

```lean
obtain ⟨χ, X, c, J, N, d, K, hχ, hωχ, hH, hModel, hSub, hElem,
    hSeed, hCount, hF, hG, hδ, hb, hLift⟩ :=
  Internal.ng_family_hull_l (δ := δ) (b := e) hZFC hω
    hSystem.conditions.2.1 hSystem.relations.2.1 hSeedCount
-- hLift i B R q hi hiN hiB hiR O hMaster U hGeneric hq he
-- 返回整个 N[G]≺H(eχ)，保持内部可数性和精确名称求值方程。
```

编号、公式码和有限参数长度都在对象模型内部取值，没有外部标准性要求。
`ng_indexed_club_l` 还允许从给定实际 club 中选择这个共同 N。

## 内部提升力迫与固定前缀的 proper 后继

`Model.SetTheory.Internal.Hereditary` 的 `Hsub_d` 把可数初等 H(χ) 子模型表示为原公式。
[InternalGenericFamilyForcing](Proper/Family/Forcing.lean) 的 `ng_family_forcing_l`
一次构造共同 N 和实际 `Hlift_d`：每个属于 N 的阶段、每个低于共同基点的 N 主条件，
都迫使对应的 N[G] 是 H(eχ) 的可数内部初等子模型。该证书的量词、名称及力迫
全部处于对象语言内，可以用于内部递归模式。证明先在可数反射模型中同时核验
全部阶段，再反射整个存在公式；调用者不提供未证明的提升前提。

[InternalGenericGround](Proper/Generic/Ground.lean) 的 `ng_family_ground_l` 还一次构造
覆盖阶段图传递闭包的规范名称图，并将它加入同一个 N。`ng_ground_trace_l` 据此证明
主条件下的精确回拉：`N[G]∩e(P) = {e(p) | p∈N∩P}`。其中 P 是图所覆盖的旧集合，
特别包括各阶段条件集；证明不要求 N 外部可数或地模型外部良基。

坐标重编码也已保持同一个 N。`row_repr_map_l` 从现有后继表示构造实际集合双射，
`selem_row_map_l` 将此图取到 N 中；`mstr_map_l` 只用 ZF 搬运主条件。
`row_repr_coords_mem_l` 用逆图把 N 内坐标条件的前缀和第二坐标名称取回 N。

[IterationQuotient](Iteration/Names/Quotient.lean) 的 `row_quot_exists_l` 在原 ZF 中构造
任意阶段间的实际商条件名称，条目为 `(check(r), r↾α)`，其中 `r∈D∩N`。
`row_quot_value_l` 精确证明其泛型值就是前缀被接受的旧条件；`row_quot_check_l`
给出每个实际旧条件的规范名称实例。对象模型无需外部良基。

[IterationSelection](Iteration/Names/Selection.lean) 的 `row_select_l` 把随前段泛型变化的
后继条件名称解码成一个坐标名称。决定分支相交时，规范名称忠实性保证旧条件
相同，故混合仍处于已装配的名称库内。混合名称本身可以不属于 N；主条件下
它被迫属于同一个 N[G]，这正是 `hlift_master_exists_l` 现在消费的成员力迫。

[IterationProperSuccessor](Iteration/Proper/Successor.lean) 的 `row_step_proper_name_l`
据此处理任意商条件名称 τ：给定 N 主前缀 p，返回严格保持 `q↾α=p` 的后继
N 主条件 q，并在每个决定分支上加强 τ 的后继坐标。仍需 N 包含相应载体、
顶名称及实际 proper club 名称；不要求 τ 本身属于 N。`row_step_proper_l`
已直接迁移为该入口的规范名称特例，恢复实际旧条件下的 `q≤r`。

[IterationDense](Iteration/Names/Dense.lean) 的 `row_dense_prefix_l` 只用 ZF，在任意实际
阶段链接上将 N 内稠密集投影到前段，再由主性和内部初等性取回同一 N 中的
真实稠密加强。[IterationDenseName](Iteration/Names/DenseName.lean) 的 `row_dense_force_l`
把它转成原条件上的存在力迫；`row_dense_name_l` 使用 ZFC 最大值原理，直接
选择仍属于同一个商条件名称、进入 `E∩N` 且加强输入 τ 的名称，前缀 p 不变。
二者适用于任意阶段间，不仅限于相邻后继；存在力迫另按 ZF 边界审计。

[IterationNames](Iteration/Names/Inclusion.lean) 证明阶段包含的名称搬运逐对象等于原名称，
等号和成员力迫可直接双向传输。[IterationBounded](Iteration/Names/Bounded.lean) 的
`row_delta0_force_l` 扩展到原 Δ₀ 公式，`row_rel_force_l` 处理实际旧关系名称。
通用有界绝对性证明位于 [Model.SetTheory.ProjectBounded](../SetTheory/ProjectBounded.lean)，
只需成员满单射，不要求两边满足 ZF 或外延性；力迫消费者使用原 ZF。

[InternalGenericName](Iteration/Names/Generic.lean) 实际构造泛型滤子的名称，
`gname_value_l` 给出精确泛型值。[IterationGenericName](Iteration/Names/GenericName.lean)
证明早期滤子中的名称在任意后期加强下仍被接受。
[IterationSuccessorGeneric](Iteration/Proper/SuccessorGeneric.lean) 的 `row_step_pil_l`
现返回原公式可表达的 `Row_pil_d`，统一量化全部输入商名称和主前缀。
`row_pil_value_l` 在任意已证明区间给出 `q↾α=p`、同一 N 的主性，以及后段的
`τ∈G∩check(N)` 力迫，滤子和 check(N) 的名称直接构造。
区间结论保留 `Row_quot_lower_d`：在每个决定输入旧条件的分支上，
换入该前缀后的实际条件确实小于该旧条件。`row_quot_lower_step_l` 从后继坐标
比较证明这一性质，`row_quot_accept_l` 对任意阶段将其转成泛型接受力迫，均只需 ZF。
这一强结论适用于任意预序，不从滤子接受反推字面上的序比较。

## 商名称的投影、换段与极限指标

`Row_link_d` 现直接包含条件的坐标性质、拼接的最大下界性质，以及固定尾部
序比较的稠密闭性 `Row_tail_reg_d`。恒等、复合、
名称后继和支撑极限的实际构造均已证明新字段；名称及有界力迫搬运已删除重复
的坐标前提。`row_splice_glb_l` 给出 `u≤splice(q,p) ↔ u≤p ∧ u≤q`，本身不消费
任何集合论公理证书。

[InternalCheckApplication](Internal/Check/Application.lean) 的 `check_apply_l` 在 ZF 中
把实际地函数应用到名称，返回函数关系力迫和每个决定分支上的精确规范名称值。
[IterationProjectionName](Iteration/Names/ProjectionName.lean) 的 `row_project_name_l` 将它
应用到实际限制函数，得到仍属于同一个 N 的前缀商名称。`selem_restriction_l`
证明 N 对这些限制封闭，只需 χ 为极限序数，不要求 χ 正则或 N 可数。

[IterationQuotientTransfer](Iteration/Names/QuotientTransfer.lean) 的 `row_quot_transfer_l`
证明前缀投影被新阶段接受后，原名称自动属于新阶段的商条件名称。
`row_quot_lower_comp_l` 使用决定分支和嵌套拼接等式复合两段实际尾部加强。
这些入口均按原 ZF 强度验证。

[IterationQuotientComparison](Iteration/Names/QuotientComparison.lean) 的 `row_quot_lower_mono_l`
证明：原前缀迫使 σ≤τ 时，低于 σ 的实际尾部加强仍低于 τ。证明先在同时决定
两名称的分支上用 `check_rel_reflect_l` 反射真实旧序关系，再由稠密尾部闭性
回到原前缀。这一步不把被迫的滤子接受替换为字面序关系。

[IterationProperLemma](Iteration/Proper/Lemma.lean) 将整个区间命题编码为 `row_pil_m`。
`row_pil_id_l` 给出恒等区间的实际实例，`row_step_pil_l` 给出名称后继实例，
`row_pil_comp_l` 复合两个已证明区间并自动构造中间商名称。
[IterationProperDense](Iteration/Proper/Dense.lean) 的 `row_pil_dense_l` 在任意这样的
区间上同时保留原主前缀、原名称的实际尾部比较，并接受选自指定 N 稠密集的名称。
区间复合只需 ZF，指定稠密名称选择使用 ZFC。调用普通名称结论可写为：

```lean
obtain ⟨q, γ, ν, hq, hpre, hm, hlower, hγ, hν, hτγ, hτν⟩ :=
  Internal.row_pil_value_l hZF hStage O hLink hPIL hQuot hτ hτQuot hMaster
-- hPIL 来自恒等、相邻后继，或两个已证明区间的实际复合。
```

[IterationModelSequence](Iteration/Proper/Model/Sequence.lean) 的 `row_model_sequence_l` 已
一次构造 `γ=sup(N∩β)`、取值于 N∩β 的非递减共尾阶段列，以及 N 中全部稠密集
的枚举；两列都是定义域为模型自身 ω 的实际函数图。它还证明 N 中可数支撑
β 条件的全部坐标落在 γ 以下。

共尾列的通用构造位于 [SetTheory/CountableCofinal](../../SetTheory/CountableCofinal.lean)：
先反向延拓可数单射，再对内部有限初段取最小上界，由替代得到整列，只需 ZF。
`selem_cofinal_sequence_l` 在任意传递环境中用内部初等性证明 N∩β 无最大元；
`mstr_dense_sequence_l` 的稠密集枚举也只需 ZF。支撑闭包先以 ZF 将唯一坐标集
取回 N，再消费已有的 ZFC 可数集合闭包。

## proper 后继的统一辅助图与共同 N

[IterationProperWitness](Iteration/Proper/Model/Witness.lean) 从每个实际被迫 proper 的后继
构造辅助码，保存顶名称、二步条件集、内部 ω 名称与 proper club 名称。
[IterationProperFamily](Iteration/Proper/Model/Family.lean) 的 `row_pr_family_l` 将它们收集为
一张模型内函数图；定义域恰为后继仍在系统内的索引，值同时保存后继索引。
通用收集后选择位于 [SetTheory/CollectionChoice](../../SetTheory/CollectionChoice.lean)，
无需预给所有见证的秩界，也不使用外部序数枚举。

[IterationProperModel](Iteration/Proper/Model/Basic.lean) 的 `row_pr_prepare_l` 将该图和内部 ω
加入可数种子，再实际构造共同的 `N≺H(χ)`、全阶段 `Hlift_d` 与统一规范名称图。
N 对实际函数求值及有序对坐标封闭，因而每个成员索引的后继索引和所需四项数据
都自动属于 N。`row_pr_family_pil_l` 据此同时给出全部这些相邻后继的 `Row_pil_d`，
调用者无需逐阶段补充名称属于 N 的证明。

[IterationProperRule](Iteration/Proper/Model/Rule.lean) 的 `row_iteration_pr_prepare_l` 直接消费
已有原公式递归及 `Row_pr_rule_d`，自动读取每个后继并完成上述装配。
`cohen_rule_pr_l` 是现有任意添加量 Cohen 规则的实际实例，有限和可数两种支撑均可使用。
这一步使用 ZFC 的实际收集与选择；其输出已经接入下述内部 ω 极限的完整区间证明。

[IterationProperNatural](Iteration/Proper/Natural.lean) 的 `row_pil_nat_l` 已沿原公式作
内部 ω 归纳，证明这些相邻区间给出全部内部有限区间的 `Row_pil_d`。
`Row_pil_stage_d` 统一表达给定终点之前的全部 N 区间，其原公式可继续用于超限归纳。
恒等情形直接保留原条件，后继情形应用已验证区间的复合；归纳只需 ZF，覆盖
外部看来非标准的内部有限阶段。共同模型入口现在还自动返回这条全部有限区间结论。

## 变动前缀比较的保持与极限还原

[IterationPrefixComparison](Iteration/Proper/Prefix/Comparison.lean) 的 `Row_cut_lower_d`
在每个决定原名称的分支上，比较当前前缀与旧条件在当前阶段的限制。
`row_cut_base_l` 给出实际初值，`row_cut_project_l` 从已经构造的投影名称及其
区间迭代引理取得该比较。[IterationPrefixStep](Iteration/Proper/Prefix/Step.lean) 的
`row_cut_step_l` 证明：当前前缀迫使新名称加强原名称时，下一前缀仍保持比较。
证明反射决定分支上的真实旧序，再应用阶段链接的稠密尾部闭性；允许跨越非相邻阶段。

[IterationPrefixLimit](Iteration/Proper/Prefix/Limit.lean) 的 `row_cut_fusion_l` 消费实际融合
条件与各共尾前缀的比较，得到极限阶段的比较；`row_cut_total_l` 再用 N 中旧条件
的支撑界，将它恢复为完整旧偏序中的 `Row_quot_lower_d`。两步均只需 ZF，
前缀序列与融合主性现在由下面的实际递归消费者完成。

## 变动主前缀的内部递归

[ClassChoice](../SetTheory/ClassChoice.lean) 的 `class_indexed_choice_l` 先用 Lévy
见证闭包找到实际累积层，再作集合上的带指标依赖选择，最后以原公式的内部 ω
归纳保持有效性。它不要求调用者预给名称的秩界，不使用全局选择或外部标准性。
[IterationThreadStep](Iteration/Proper/Thread/Step.lean) 的 `row_pr_move_l` 实际构造每一转移：
在原主前缀选择指定稠密集中的加强名称，投影到下一阶段，再应用已证明区间的
迭代引理。新状态保留主性、商成员力迫、精确前缀及对旧条件的阶段比较。

[IterationThread](Iteration/Proper/Thread/Basic.lean) 的 `row_pr_thread_l` 消费这些真实转移，返回
模型内的 ω 函数图。较短区间已有实际实例时可跨任意共尾阶段使用。
[IterationThreadCoherence](Iteration/Proper/Thread/Coherence.lean) 的 `row_pr_coherent_l`
通过原公式内部归纳证明任意两指标的精确限制关系；相同阶段的条件相等。
[IterationThreadOmega](Iteration/Proper/Thread/Omega.lean) 的 `row_pr_omega_thread_l` 已直接
消费共同 N、全阶段提升和实际 proper 后继图，自动生成首个内部极限 ω 所需的
共尾列、完整稠密枚举、初始投影及上述相容主前缀序列。此入口不再要求调用者
另给较短区间或递归初始状态，同样覆盖外部非标准的内部自然数。

## 整列名称比较、主融合与首个内部极限

[InternalCheckOrder](Internal/Check/Order.lean) 的 `check_preord_force_l` 只用 ZF 证明
旧预序的规范名称被迫满足预序公理。[TwoStepClass](TwoStep/Class.lean) 在全部实际
条件名称上证明二步序的自反性与传递性，原 `two_step_order_l` 已迁移为其闭库限制。
通用 [RelationChain](../../SetTheory/RelationChain.lean) 以原公式内部归纳将相邻的
可定义传递关系推广到任意内部指标；原包含链定理也直接使用此接口。

[IterationThreadComparison](Iteration/Proper/Thread/Comparison.lean) 的 `row_pr_bound_l`
先在同一个旧偏序中比较名称，再把成员与序关系反射回当前前缀，从任意初值比较
推出所有后期阶段的比较。初值可以是原始名称，也可以是某步刚选出的稠密名称。
`row_pr_bounds_l` 已统一装配全部这些稠密名称的不变量。

[IterationThreadTail](Iteration/Proper/Thread/Tail.lean) 构造任意内部起始指标之后的实际共尾
前缀族；最小原像编号证明其可数性，只需 ZF。
[IterationThreadFusion](Iteration/Proper/Thread/Fusion.lean) 的 `row_pr_fuse_l` 在实际支撑
极限中构造融合条件，精确保留原递归图的全部前缀。
[IterationThreadRealization](Iteration/Proper/Thread/Realization.lean) 的 `row_pr_total_l`
将相应尾段的比较恢复为旧偏序的完整 `Row_quot_lower_d`。
[IterationThreadMaster](Iteration/Proper/Thread/Master.lean) 的 `row_pr_master_l` 再由实际
稠密枚举证明融合主性：决定所选名称，反射真实旧成员，用拼接最大下界构造共同加强。
比较还原与给定融合的主性只需 ZF；`row_pr_master_fusion_l` 使用 ZFC 自动构造该主融合。
这些证明适用于任意已有相容递归图及支撑界的共尾极限，不限于 ω 终点。

[IterationProperOmega](Iteration/Proper/Omega.lean) 的 `row_pr_omega_l` 已完成内部 ω
终点的全部 `Row_pil_stage_d`，包括非标准内部有限起点。`row_iteration_pr_omega_l`
从原公式 proper 规则、实际可数支撑迭代和可数种子自动构造共同 N 并返回该结论；
调用者不需补充序列、主性或尾部比较。已有参数化 Cohen 规则提供实际规则实例。

## 任意内部长度的完整区间装配

[IterationThreadLimit](Iteration/Proper/Thread/Limit.lean) 的 `row_pr_limit_thread_l` 已推广到
任意 N 中的非零极限 β。构造保留 γ=sup(N∩β)，不要求 γ=β 或 γ∈N；旧 N 条件
的支撑落在 γ 以下也由实际模型序列证明。原 ω 序列入口直接调用这一通用层。
[IterationProperLimit](Iteration/Proper/Limit.lean) 读取原迭代在 γ 处的真实支撑极限，
得到 β 处保留原主前缀、主性及完整尾部比较的区间步骤。

[IterationProperInduction](Iteration/Proper/Induction.lean) 的 `row_pr_induction_l`
以原 `row_pil_stage_m` 公式分离反例集，完成模型自身的序数归纳。后继前驱通过
`selem_predecessor_l` 取回 N，再复合相邻区间；极限步骤使用较短区间的实际归纳结论。
`row_iteration_pr_l` 从 proper 规则、实际可数支撑迭代及可数种子自动返回共同 N
上的全部内部区间；`row_iteration_pr_exists_l` 还自动构造指定内部长度的迭代。
因此所有较短区间前提均已由完整归纳实际满足，不留给自动入口的调用者。

[CohenIterationProper](Applications/Cohen/CountableSupport.lean) 的 `cohen_iteration_pil_l` 只需原 ZFC、
添加量参数 κ 与内部序数长度，就构造可数支撑迭代及上述完整区间接口。
整个过程不要求模型在外部良基，也不把内部自然数或序数替换为外部枚举。

## 完整 club 版 proper 保持

[FinitaryTrace](../../SetTheory/FinitaryTrace.lean) 固定实际运算图，以
`Hull(A∪Y)∩X=Y` 定义交集 club。无界性由最小闭包给出；闭性通过内部递增链的
唯一最小闭包函数及其并证明。整个证明覆盖非标准内部有限参数列。
[FinitaryFamily](../../SetTheory/FinitaryFamily.lean) 把内部可数的实际运算图族
合为一张图，规则编号为“运算图与原规则编号”的有序对；这一步只需 ZF。

[InternalGenericTrace](Proper/Family/Trace.lean) 同时合并司寇伦、泛型判定和
泛型选择三张图。`ng_trace_forcing_l` 返回实际交集 club，其每个成员都有同一个
`Hsub_d` 与 `Hlift_d` 见证；指定 N 的内部提升由
[InternalGenericClosedForcing](Proper/Family/ClosedForcing.lean) 反射实际闭包公式证明。

[IterationProper](Iteration/Proper/Preservation.lean) 的 `row_iteration_proper_l` 对全部阶段证明
原 `Proper_d`：在任意包含条件域的 X 上取上述 club，调用完整区间迭代引理，
将旧条件的 check 名称输入零前缀得到真实主加强，再用交集等式保持主性。
`row_iteration_proper_exists_l` 同时构造任意内部长度的实际迭代。
`cohen_iteration_proper_l` 只需 ZFC、添加量 κ 和内部序数长度；完整保持无需
调用者补充 club、共同模型、融合或额外闭性前提。

## 二步主条件的完整双向分解

[TwoStepMasterDecomposition](TwoStep/Proper/Decomposition.lean) 的
`two_step_master_iff_l` 证明 `(q,t)` 是 N 主条件，当且仅当 q 是 N 主条件且
q 迫使 t 是 N[G] 主条件。`two_step_master_decompose_l` 同时构造规范 N[G] 名称。
环境是实际的 `N≺H(χ)`，两步条件集、序关系及地偏序参数属于 N；不要求地模型
外部可数、良基或标准，也不把后阶段主性当作反向证明的调用前提。

[TwoStepMasterDecision](TwoStep/Proper/Decision.lean) 对每个 N 内名称 F 构造二步
判定集：条件或者迫使第二坐标属于 F，或者以下永远不能命中 F。原子力迫的
H(χ) 绝对性与实际内部初等性使该判定集属于 N。
[TwoStepMasterPull](TwoStep/Proper/Pull.lean) 用二步主性构造首坐标上的真实稠密
原像，使共同加强仍被指定的首阶段泛型接受；该层只需 ZF。
[TwoStepMasterSecondValue](TwoStep/Proper/SecondValue.lean) 用后阶段稠密性排除
不命中的分支，得到 N[G] 中的实际相容见证。
[TwoStepMasterSecond](TwoStep/Proper/Second.lean) 最后反射完整有限参数公式，得到
`two_step_master_second_l` 的全局力迫证书。反向及完整分解使用 ZFC 中已有的
遗传小原子证书，未增加强迫绝对性、泛型存在或外部枚举前提。

## proper 扩张的可数覆盖、ω₁ 与可数共尾性保持

[InternalProperCover](Proper/Preservation/Cover.lean) 的 `proper_name_cover_l` 把单射名称、
规范名称图、X 及 ω 放入实际可数初等 N。每个接受主加强的泛型中，N[G] 包含
全部旧自然数；单射的原像见证由内部初等性取回 N[G]。规范名称精确回拉遂将
名称在旧 X 中的部分包含于旧可数集 N∩X。全泛型判据给出真实的覆盖力迫，
完整有限参数反射消去地模型外部可数的要求。

[InternalCover](Internal/Functions/Cover.lean) 的原公式 `Old_cover_d` 保存实际覆盖集、
其地模型可数性、规范名称与力迫证书。`proper_cover_dense_l` 证明该原公式在
原条件以下稠密，故给定的原泛型确实遇到覆盖见证。
[InternalProperCoverValue](Proper/Preservation/CoverValue.lean) 的 `proper_set_cover_l`
因此对旧集合的每个新可数子集返回真实旧可数覆盖；`proper_countable_cover_l`
还处理任意新可数集合与旧集合的交。全部内部自然数均被覆盖。
[InternalProperInjection](Proper/Preservation/Injection.lean) 的 `proper_injection_reflect_l`
现直接消费上述通用构造：规范名称的覆盖反射为旧集合的真实包含，取得旧可数性。

[InternalProperCountable](Proper/Preservation/Countable.lean) 的 `proper_countable_l`
自动构造同一个规范嵌入，同时返回旧可数性双向等价与新可数子集的旧覆盖。
`proper_omega_one_l` 证明旧 ω 的 Hartogs 序数仍是扩张中 ω 的 Hartogs 序数，
从而精确保留 ω₁。`proper_extension_l` 同时返回 ZFC 模型性、内部 ω、ω₁
以及全部旧集合的可数性对应、上述新可数子集覆盖和下述可数共尾性保持。

[SetTheory/IndexedIteration](../../SetTheory/IndexedIteration.lean) 以实际函数图在
ZF 内完成带指标的确定 ω 递归；原 `ZFC.indexed_choice_l` 先单值化原关系，随后
直接复用此层。[Cofinality/Countable](../../SetTheory/Card/Cofinality/Countable.lean)
将可数共尾集的单射反向延拓为枚举，每次取同时高于当前项和枚举项的最小成员，
构造严格递增的实际 ω 共尾列。`ZF.cf_omega_countable_l` 因而在 ZF 内给出
`cf(α)=ω` 与存在内部可数共尾子集的等价，不要求一般共尾度存在性作为前提。

[InternalProperCofinality](Proper/Preservation/Cofinality.lean) 的 `proper_cf_omega_l`
证明同一规范嵌入下 `cf(eα)=eω ↔ cf(α)=ω`。反向将新共尾集包含于实际旧可数
覆盖，并核验该旧集合仍共尾；正向搬运旧共尾集及其单射。若旧 `cf(α)>ω`，
`proper_countable_bounded_l` 直接返回 β∈α，使每个给定新可数 Y⊆eα 满足
Y⊆eβ。只要求共尾度界，不要求 α 正则；没有宣称任意较高共尾度均保持。

[IterationProperPreservation](Iteration/Proper/Extension.lean) 的
`row_iteration_preserves_l` 固定一次地模型 ω₁，对任意内部长度的可数支撑
proper 迭代的各阶段、各泛型自动装配上述保持结果。
`cohen_iteration_preserves_l` 只接收 ZFC、添加量参数和内部序数长度，直接
构造整个迭代及所有阶段的保持证书。
实际单射名称的公共原公式和解释证书统一位于
[InternalInjection](Internal/Functions/Injection.lean)，CCC 与 proper 两层均直接消费。

## 可数闭后继与精确保留前缀的链下界

[InternalClosedSyntax](Closed/Syntax.lean) 为原 `Chain_d`、下界及 `Closed_d`
提供实际原公式。[InternalClosedSequence](Closed/Sequence.lean) 把同一个条件
下逐项被迫递降的实际函数图装配为完整名称链；泛型求值及有限参数反射覆盖全部
内部自然数。[InternalClosedName](Closed/Name.lean) 的 `nchain_bound_name_l`
在原条件上消去被迫闭性，最大值原理返回同时低于全部坐标的下界名称。
规范索引条目的同条件读取由 [InternalNameSequenceForcing](Internal/Names/SequenceForcing.lean)
证明。名称链装配、坐标读取和内部 ω 的规范名称力迫只需 ZF；选择下界名称使用 ZFC。

[TwoStepClosed](TwoStep/Closed.lean) 的 `two_step_chain_bound_l` 输入真实二步下降链
及一个压住全部首坐标的 p，返回首坐标精确为 p 的实际二步下界。下界名称通过原
混合闭库重新装配；没有加强或替换 p。`two_step_closed_l` 再用首阶段闭性取得 p，
证明“首阶段可数闭且迫使后继可数闭”时，实际二步偏序可数闭。

[IterationClosedSuccessor](Iteration/Closed/Successor.lean) 在已有 `Row_next_d` 的
实际双射表示上回拉、送回下降链。`row_next_chain_bound_l` 精确保留给定旧前缀，
`row_next_closed_l` 返回已有坐标后继的完整闭性；没有改换偏序或只构造稠密替代。
两张投影图由 [SetTheory/FunctionCoordinates](../../SetTheory/FunctionCoordinates.lean)
的 `ZF.function_coords_l` 实际构造，并直接用于二步证明。

[CollapseNames](Applications/Collapse/Names.lean) 接收任意大小界、源集、目标集名称，构造规范的
可数部分函数偏序名称。实际塌缩定理给出预序、顶及 ω 大小界下的闭性力迫。
[CollapseClosed](Applications/Collapse/Closed.lean) 提供三个实际消费者：

- `collapse_two_step_closed_l`：在任意可数闭首阶段后添加参数化塌缩，自动返回名称、
  原二步偏序、顶条件及闭性。
- `collapse_pair_closed_l`：从两组任意地模型集合参数直接构造可数闭二步塌缩。
- `row_collapse_closed_l`：在已有可数闭坐标阶段后实际追加塌缩，返回共同顶、阶段
  链接、原样嵌入、闭性及有限／可数两种支撑保持。

上述固定前缀结论现已接入完整极限构造及内部超限归纳，得到下一节的闭迭代接口。

## 任意内部长度的可数支撑闭迭代

[IterationClosedInterval](Iteration/Closed/Interval.lean) 的 `Row_cl_d` 表示完整闭区间：
每条上阶段的实际内部 ω 下降链，连同一个压住全部投影的旧前缀，均有精确保留
该前缀的整链下界。投影由实际集合函数图完成，恒等和区间复合不使用对象选择。
`Row_cl_stage_d` 及其原公式同时量化全部较早前缀。

[IterationClosedLimit](Iteration/Closed/Limit.lean) 先构造原链的可数支撑并 C。
有界分支把整条链原样视为一个较早阶段中的链。共尾分支分离出旧前缀以上的
支撑，用 ZF 的严格 ω 共尾列构造实际阶段指标；
[IterationClosedThread](Iteration/Closed/Thread.lean) 的类上依赖选择产生每个阶段
压住原链全部投影的真实条件图，相邻限制精确相等。
[IterationClosedFusion](Iteration/Closed/Fusion.lean) 以原公式 ω 归纳传播一致性，
按严格阶段指标重编号，再调用实际并条件融合；原极限序关系给出整链下界。

[IterationClosedRule](Iteration/Closed/Rule.lean) 的规则输入仅保存真实后继名称、
旧 ω 名称和被迫闭性，不假设区间或整个迭代的闭性。
[IterationClosedInduction](Iteration/Closed/Induction.lean) 对实际原公式分离反例集，
内部超限归纳统一零、后继和任意极限，提供：

- `row_cl_induction_l`：全部内部阶段的完整闭区间，精确保留任意适用旧前缀。
- `row_iteration_closed_l`：全部阶段的内部可数闭性。
- `row_iteration_closed_exists_l`：从已实现的原公式规则构造完整迭代及上述全部证书。

[CollapseNameUniqueness](Applications/Collapse/NameUniqueness.lean) 在 ZF 内证明规范塌缩名称
三元组字面唯一；[CollapseRule](Applications/Collapse/Rule.lean) 因此构造确定的实际原公式规则
及其闭性实例。旧 ω、源集和目标集的规范名称每阶段自动构造。
[CollapseIteration](Applications/Collapse/Iteration.lean) 的 `collapse_iteration_closed_l` 只接收
ZFC 模型、两个集合参数与内部序数长度，一次构造整个可数支撑迭代、全部闭区间
和各阶段闭性。`collapse_iteration_preserves_l` 还返回各泛型扩张的 ZFC、内部 ω、
规范嵌入，以及每个扩张实数、任意旧目标上的内部 ω 函数和旧集合的可数子集的实际旧原像。
可数子集的原像同时附有地模型内部可数性。通用规则的相同保持接口为
[IterationClosedPreservation](Iteration/Closed/Extension.lean) 的
`row_iteration_closed_preserves_l`。这些结论允许模型外部非良基及内部 ω 非标准。


## 闭扩张的内部序列及可数子集反射

[InternalFunction](Internal/Functions/Basic.lean) 的 `Fn_name_d` 保存实际名称与原函数公式力迫。
函数和单射共用 `fn_env_l`；`fn_name_index_l` 只要求函数性，并分别保留力迫条件和
规范名称的基点。原单射消费者已迁移到该函数接口。

[InternalClosedFunction](Closed/Function.lean) 的 `closed_fn_dense_l` 从实际
可数闭性证明：存在一张地模型内部函数图、且条件决定其全部旧坐标的谓词是稠密的。
`closed_intersection_l` 只要求各成员在指定条件以下稠密；逐坐标旧值由
[InternalFunctionDecision](Internal/Functions/Decision.lean) 取得，函数唯一性与规范名称
忠实性使原替换模式可收集整个图。

[NoNewFunctions](Closed/NoNewFunctions.lean) 的 `no_new_functions_l` 让给定原泛型遇到这个
实际原公式稠密集，返回 `G : ω → X` 及 `e G = F`。目标 `X` 可以是任意旧集合。
[NoNewCountable](Closed/NoNewCountable.lean) 的 `no_new_countable_l` 对任意扩张内部可数
`Y ⊆ e X` 返回 `A ⊆ X`、地模型内部 `|A| ≤ ω` 及 `e A = Y`。
非空分支反射带默认值的枚举再取实际值域，空集单独处理。

`closed_extension_l`、`row_iteration_closed_preserves_l` 和
`collapse_iteration_preserves_l` 均在同一个规范嵌入上自动返回这些结论。
整个证明只使用内部 ω 图与原公式分离、替换；没有外部自然数枚举或外部良基假设。


## 可数闭预序的 proper club 与塌缩区间实例

[InternalClosedMaster](Closed/Master.lean) 在对稠密加强见证闭合的内部可数 N
中，用实际反向单射枚举 N，再用内部带指标依赖选择构造 ω 下降链。每个 N 内稠密集
都在某个内部阶段被遇到；整链下界因而是 N 主条件。证明只要求预序的自反性和
传递性，不额外要求排除条件的序公理。

[BinaryWitnessClub](../../SetTheory/BinaryWitnessClub.lean) 的 `ZFC.bw_club_l` 对任意
有序对约定、有限固定参数和二输入原公式细化一个真实 club，使其成员承接环境中的
存在见证。选择图由原选择公理实际构造，有限列末两项编码复用已有有限元闭包。
[InternalClosedProper](Closed/Proper.lean) 用它取得稠密见证闭 club，完成
`closed_proper_l`；所有闭包前提都有该实际实例。

[InternalClosedProperName](Closed/ProperName.lean) 的 `closed_name_proper_l`
把真实名称预序及旧 ω 下的闭性转为同条件的 properness 力迫。
[CollapseProper](Applications/Collapse/Proper.lean) 的 `collapse_rule_pr_l` 将原参数化塌缩规则
接入通用 proper 迭代引理。`collapse_iteration_pil_l` 一次返回同一迭代的全部闭区间、
各阶段闭性和 properness，并为任意内部可数种子构造共同 H(χ) 小模型 N 与全部
适用区间的 `Row_pil_stage_d`。

闭扩张及两层全阶段保持装配现在还在原来的同一规范嵌入上返回旧可数性双向对应、
ω 的任意 Hartogs 序数保持、ω 共尾性双向对应，以及旧共尾度大于 ω 时新可数子集的
严格旧序数界。上述结论调用已经证明的 proper 保持层，没有再设置保持性回调。
