# 模型论目录与发展路线

现有模型论源码集中在 `YesMetaZFC/Model/`，直接属于现有 `YesMetaZFC` Lake 库。
模块路径已经迁移，原路径不保留转发文件；数学声明沿用原命名空间。

## 已实现的通用底座

`import YesMetaZFC.Model` 已接入下列实际定义、实例与证明。默认仍使用现有
`FirstOrder.Structure` 和 `Theory.Models`；`Native.background` 给出默认背景，
`Native.model` 给出该背景上的实际模型解释。结构、模型公理与可选能力均未改为 typeclass。

| 层 | 实际接口与已核验范围 |
| --- | --- |
| [上下文语义](Semantics/Algebra.lean) | `Sem_context` 给出上下文映射、谓词、等同和量词，函数与关系解释另行给出；`Sem_algebra` 装配这些数据供公式求值。`Tm_map` 与 `Sem_map` 分开，项保持不消费公式保持条件；最小代数模块不导入原生结构。 |
| [默认实例](Semantics/Instances.lean) | `Native.algebra`、`Native.interpretation` 对任意签名、任意原结构给出实际解释；`Native.tm_eq`、`fm_eq` 精确恢复原项求值及全部公式语义。`Ast.algebra` 精确恢复当前 AST。 |
| [代入](Semantics/Substitution.lean) | `Tm_substitution` 与完整谓词代入分层，已证明标准项、参数列及公式的代入交换；量词下显式使用 `liftBound`。`Sem_action` 的恒等与复合是独立证书，Native 与 Ast 两个实例均已核验。 |
| [相对模型性](Semantics/Background.lean) | `Sem_background` 只给上下文操作与成立判断，`Sem_model 𝒱` 另给当前结构的函数、关系解释，`Sem_model.models` 逐公理解释标准理论。`Sem_rules` 的六规则证书已由 Native 和 Ast 两个实际模型填满；`proof_sound`、`derives_sound` 保留原 Hilbert 核和任意局部上下文。 |
| 原生与相对一致性 | `Native.models_iff` 恢复原模型性，`Native.consistent` 直接从实际模型公理证据得到一致性。`Ast.background U` 以 `Provable U` 判断成立，`Ast.model U` 给出默认符号解释；`models_self` 无外部模型存在前提，`derives_transfer` 在背景理论内回放标准推导。通用出口为 `Sem_rules.consistent_of_models`。 |
| [可选语法与证明码](Semantics/SyntaxView.lean) | `Syntax_view` 保留标准像的注入与代入作用，`Proof_view` 只要求标准证明的前向表示；默认由 `Ast.syntax_view`、`Ast.proofs` 实现。没有总解码器、内部码外部良基性或一般反向证明提取。 |
| [可选谓词域](Semantics/Predicates.lean) | `Predicate_domain` 分离关系对象与背景谓词。`Full` 相对于该谓词域，`Formula_closed` 只要求覆盖标准公式像；两者都不属于基础模型的必填条件。Native 实例直接消费原 Henkin 关系域。 |
| [完整二阶默认实例](SecondOrder/Full.lean) | `Full.structure_of` 使用原载体上的全部谓词，关系域保持 `Type (max u x)`；`predicate_full` 证明其满性，`satisfies_iff` 对所有对象量词、关系量词及联结词连接原 Full 语义。 |
| [普通结构映射](FirstOrder/Morphism.lean) | `Env.map` 只要载体映射，`Fn_map` 只要函数保持，`Str_emb` 另要求单射与关系双向保持；`formula_iff`、`models_iff` 只另消费满射。`Str_iso` 携带显式逆映射，不通过不可计算选择构造逆。 |
| [初等嵌入](FirstOrder/Elementary.lean) | `Str_emb.Elementary_m` 保持任意有限参数下的全部公式；`tarski_vaught_m` 等价于目标见证可取在像中。无需满射、可数性、模型论完备性或选择函数。 |
| [子结构](FirstOrder/Substructure.lean) | `Substructure_m` 给出各排序非空且函数封闭的子集；`structure_m`、`incl_m` 实际构造限制结构和包含映射。其 `tarski_vaught_m` 使用原模型环境及参数归属，直接供 hull 的见证封闭证明调用。 |
| [任意指标闭包](Closure.lean) | `RuleFamily_l` 不依赖逻辑语言，支持任意排序、载体、规则及输入指标 universe；`Closure_l` 是实际归纳闭包。给出最小性、单调性、幂等性、重编号、任意规则族合并及任意生成族的闭包公式。 |
| [Skolem 壳](FirstOrder/Skolem.lean) | `Skolem_m` 显式携带存在成立时的见证函数；`hull_m` 对任意多排序签名、原结构及生成子集构造同层初等子结构。`hull_with_m` 还可同时封闭任意额外规则族，不要求其运算属于原语言。 |
| [约化积与 Łoś](ReducedProduct/Los.lean) | 任意签名及同层结构族的截面商，有限参数无选择地下降。`los_m` 明确消费见证拼接条件，`los_iff_witness_m` 证明此条件恰好必要充分。 |
| [同层超幂](Ultrapower.lean) | 恒定结构族的实际超幂，输入与输出 `Structure` 层级相同；对角嵌入、条件初等性、理论保持及主超幂的显式同构，不限于隶属语言。 |
| [力迫与名称解释](Forcing/README.md) · [目录索引](Forcing/INDEX.md) | 同 universe 的内部名称泛型商，允许外部非良基地模型；参数化 `Add(ω,κ)` 保持旧无限基数并构造互异新实数。自动装配 CH 与 ¬CH 两侧扩张，`ch_independent_l` 在原推导核中给出 CH 独立性。 |

原 `LevyEmbedding` 已直接扩展 `Str_emb`，仅额外保留有界见证回拉；旧层的环境映射、
项与参数列证明已迁走，全部绝对性消费者使用新接口，没有转发证明层。
原值列骨架迁入 [Values](Values.lean)，原关系解释层的值列／赋值／环境转换迁入
[Valuation](FirstOrder/Valuation.lean) 并推广到任意签名 universe；原消费者直接使用迁入定义。

三个角色在接口中明确分开：给定背景 `𝒱`、模型解释 `ℳ : Sem_model 𝒱`、语法视角 `S`，
实际解释映射 `I : Sem_map S.code ℳ.algebra` 按 `𝒱.valid (I.fm (S.code.fm φ))` 检查每条标准
公理。`Sem_map.models_iff` 将它连接到 `ℳ.models`，只比较标准像，不增加内部码反射。

`Proof_view.has_proof` 明确表示“给出一个被检查接受的码”的外部存在性；它不冒充背景
内部量词所表达的证明存在判断。`Semantics.SyntaxView` 的实际默认实例仍是原 AST／证明树，
尚未接入下述集合结构的内部指令码满足关系。相对模型性也不自动反射为外部模型性。

以上数据构造没有新增 `noncomputable`、选择实例、`sorry` 或自定义公理。对象载体与原生
谓词域保持既定 universe；打包这些类型的元层记录不是新的模型载体。

通用底座的 44 个关键接口已做依赖审计，没有 `sorryAx`，仅涉及已有的 `propext`、
`Quot.sound`、`Classical.choice`；后者用于原生经典逻辑可靠性证明。
`Model` 入口的 49 个源码依赖不包含 Henkin 或具体 ZFC 模块；具体集合论模型单独列在下表。

| 内容 | 导入入口 | 目录 |
| --- | --- | --- |
| 任意结构上的一阶语义、环境、可靠性与有界绝对性 | `YesMetaZFC.Model.FirstOrder` | [FirstOrder](FirstOrder.lean) |
| 高阶、无穷及二阶语义 | `YesMetaZFC.Model.HigherOrder`、`YesMetaZFC.Model.Infinitary`、`YesMetaZFC.Model.SecondOrder` | [SecondOrder](SecondOrder.lean) |
| 原有 Henkin 构造及强完备性 | `YesMetaZFC.Model.Henkin` | [Henkin](Henkin.lean) |
| 关系解释、扩张、模型闭包与传输 | `YesMetaZFC.Model.Interpretation` | [Interpretation](Interpretation.lean) |
| 隶属结构及 Project 语义连接 | `YesMetaZFC.Model.SetTheory` | [SetTheory](SetTheory.lean) |
| 原生小图 ZFC 模型与一致性 | `YesMetaZFC.Model.SmallGraph` | [SmallGraph](SmallGraph.lean) |
| 通用布尔值语义及原生对应 | `YesMetaZFC.Model.Boolean.Native` | [Boolean/Native](Boolean/Native.lean) |
| 任意完备布尔代数的标准 ZFC 名称模型 | `YesMetaZFC.Model.Boolean` | [Boolean/ZFC](Boolean/ZFC.lean) |
| ZFC 的 136 个纯模型构造、规格与对应模块 | `YesMetaZFC.Model.ZFC.Pure` | [ZFC/Pure](ZFC/Pure.lean) |

`import YesMetaZFC.Model` 只汇集通用语义入口；Henkin、解释消去和具体集合论层按需导入。
纯 Rosser、Löb、第二不完备与 Tarski 的元数学终点仍由原元数学入口提供，并直接
消费这里的实际模型模块。证明搜索 tactic、语法编码和集合论领域定理按其职责保留。

验证使用 `lake --wfail build`；`bash scripts/check-all.sh --library-only` 覆盖包含本目录在内
的全部独立模块，且不生成或运行扫描器可执行程序。全源检查分批传递同一组模块名，以适配
Windows 的命令行长度限制。
全源脚本默认使用 4 线程，并保留显式设置的 `LEAN_NUM_THREADS`。

已迁移的 185 个模型模块最长为 1,132 行，没有旧模块路径或循环导入残留。
既有四个超长模块及历史构建性能的边界见 [工程指南](../../markdown/ENGINEERING.md)。

## 原 ZF 中的有限公式反射

通用 Lévy 反射入口是 [LevyReflection](SetTheory/LevyReflection.lean)，与
`ProjectReflection` 的外部可数初等反射分开。`ZF.lr_finite_l` 接收任意有限原
公式族及集合 A，实际构造包含 A 的累积层 V_α；同一个 V_α 对各公式的全部
层内参数都保持真值。`ZF.lr_reflect_l` 是单公式入口，自动处理其全部量词
子公式及全称反例。`lr_model_l` 将量词相对化真值接到实际内部隶属结构码。

```lean
obtain ⟨α, X, hLayer, hA, hReflect⟩ := SetTheory.ZF.lr_reflect_l I hZF φ hClosed A
-- hReflect 量化 X 中的所有参数赋值；不是只反射预先选定的一组参数。
```

统一见证界先在实际赋值空间上收集；最早累积层给出唯一增长步，沿内部 ω
递归后取并。整个证明只用 ZF，无额外反射公理或全局选择函数，也不要求模型
外部良基或 ω 外部标准。这里的有限公式族由给定原 AST 索引；不宣称某一个
V_α 初等于整个宇宙，也不把它等同于全部非标准内部公式码的统一反射。

## 模型内部的集合结构与满足关系

入口为 `YesMetaZFC.Model.SetTheory.Internal`，声明位于
`YesMetaZFC.SetTheory.Internal`。地模型中的结构码为有序对 `(X,R)`，其中 X 非空，
R 是 X 上的实际二元关系图。`smdl_structure_l` 用子类型解码同层结构，不选择基点。
`smdl_membership_l` 自动构造任意非空内部集合上的隶属结构码，供后续 H(χ) 使用。

公式是模型内有限指令序列及根行号。四类指令为二元关系、等号、或非、存在量词；
或非的两个子公式及量词的子公式均引用更早行，变量编号和程序长度属于模型自身 ω。
`scode_exists_l` 在一个显式幂集乘积界上分离全部合法公式码，没有把内部有限序列
变成宿主 `List`，也没有要求非标准码可以在外部解码。

赋值空间 E 是模型内的 X^ω。每行真值是 E 的子集；一步算子由实际原公式分离，
整张表由原内部序数递归构造。`seval_exists_l`、`seval_unique_l` 证明其存在与唯一性；
`ssat_rel_l`、`ssat_eq_l`、`ssat_nor_l`、`ssat_exists_l` 给出四类精确 Tarski 方程。
`Satisfies_d ω c a f` 与原公式 `satisfies_m` 只接收结构码、公式码及赋值，解码证书
和真值表都在内部量词下，且 `satisfies_decode_l` 证明中间见证不改变真值。

```lean
obtain ⟨c, R, hModel, hRelation⟩ :=
  SetTheory.Internal.smdl_membership_l I hZF hX
obtain ⟨C, E, S, hCodes, hAssignments, hGraph, hSat⟩ :=
  SetTheory.Internal.smdl_satisfaction_l I hZF hω hModel
-- C、E、S 都是地模型集合；S 记录全部合法内部公式与赋值的满足关系。

obtain ⟨E, H, Y, hE, hH, hY, hSubset, hTruth, hUnique⟩ :=
  SetTheory.Internal.smdl_table_l I hZF hModel hFormula
-- hTruth 将结构码对指定公式的满足关系精确化为 f∈Y。
```

`Smodels_d`、`smodels_m` 描述实际内部理论集合的模型性，开放公式按全称闭包解释。
`smodels_theory_l` 构造给定结构的全部有效公式集合并证明其模型性。全部存在性仅用
ZF，允许地模型外部非良基；这里的满足关系针对集合结构，不是地模型全宇宙的真谓词。

原 Project AST 的编译见 [Compiler](SetTheory/Internal/Compiler.lean)：`source_compile_l`
接收任意有限参数上下文中的 `FreeClosed` 公式，返回实际程序码、规范变量编号及
对全部编码结构的语义对应。定义原子先展开为原正文，因而解码结构不需外延性；
量词在内部取得新编号并更新赋值。`source_satisfaction_l` 自动装配参数赋值与满足等价式。
[FiniteSource](SetTheory/Internal/FiniteSource.lean) 的 `source_finite_compile_l` 进一步把
有限参数装入模型内函数图；零号变量留给候选对象，列外取空集，同一份程序和参数列
对全部包含参数的集合结构、全部候选对象有效。内部 OD 使用这一接口传递唯一性。

```lean
obtain ⟨a, E, f, hFormula, hSpace, hf, hTruth⟩ :=
  SetTheory.Internal.source_satisfaction_l I hZF hω hModel φ hFreeClosed ρ
obtain ⟨C, N, hCodes, hNumbering⟩ :=
  SetTheory.Internal.scode_numbering_l I hZF hω
-- N 是全部内部公式码到内部 ω 的实际单射，不限于原 AST 的标准像。
```

[FiniteSequenceCountable](../SetTheory/Card/FiniteSequenceCountable.lean) 的
`ZF.fseq_countable_space_l` 对任意内部可数字母表构造全部内部有限序列及单射；
编号层沿内部 ω 统一递归，最终把长度与层内编号配对，只需 ZF。
[Countable](SetTheory/Internal/Countable.lean) 将它用于完整公式码集合。

规范编码入口为 [CanonicalCode](SetTheory/Internal/CanonicalCode.lean) 与
[Ord/Code](../SetTheory/Ord/Code.lean)。固定有序对约定后，序数配对 `Oc_pair_d a b c`
取 `(a,b)` 在“最大坐标、第一坐标、第二坐标”典范良序中的位置；端延拓证明
计算结果与方块界无关。它在全部序数上有唯一输出，单射，且将内部自然数对编码为自然数。

有限序数列 `F:n→Ord` 按内部递归计算 `b₀=0`、`bᵢ₊₁=pair(bᵢ,F(i))`，
最终编码为 `pair(n,bₙ)`。`oc_fold_injective_l` 用实际分离公式的 ω 归纳恢复
整个前缀，所以支持模型内部的非标准有限长度。空参数列的代码是内部零。

| 接口 | 已证明的内容 |
| --- | --- |
| `oc_pair_exists_l`、`oc_pair_unique_l`、`oc_pair_injective_l` | 规范序数配对的总性、唯一性及解码唯一性 |
| `oc_seq_exists_l`、`oc_seq_injective_l`、`oc_seq_natural_l` | 全部内部有限序数列的编码与恢复；自然数列的代码仍在 ω 内 |
| `oc_seq_tables_l` | 任意序数字母表的全部有限列与其合法序数码之间，实际存在双向集合编码表 |
| `sc_num_exists_l`、`sc_num_unique_l`、`sc_num_injective_l` | 原内部公式码 `(程序,根)` 的固定自然数编号，无额外编号图参数 |
| `sc_num_tables_l` | 自动构造全部原公式码、合法自然数码集及精确互逆图 |
| [CanonicalSatisfaction](SetTheory/Internal/CanonicalSatisfaction.lean) 的 `sc_sat_decode_l` | 自然数码上的满足关系精确还原为原内部满足关系 |
| `source_nat_satisfaction_l` | 从原 Project 公式与实际模型参数自动取得自然数码、内部赋值和真值等价 |

上述结果均在背景 ZF 中证明，未使用背景选择公理。原 `scode_numbering_l` 与
`scode_countable_l` 已直接调用规范编码。非标准公式的逆解码结果仍是模型内部的
程序与根行号；标准 Project AST 通过已有编译接口进入这套编码。
目前已提供全部原公式图及语义对应。[内部 OD](../SetTheory/InnerModel/OD.lean) 已完成
以 V 层满足关系为基础的无参数定义、标准原公式唯一可定义性对应及单序数解码；
OD 的 Σ₂ 正规形已由 [Complexity](../SetTheory/InnerModel/OD/Complexity.lean) 证明：
有界化固定解码公式，用真实累积层的全称递归证书核验幂集，直接连接既有 OD 定义。
这一结论不自动给出原编码图或原解码图的 Δ₂ 证书。

[内模型进度总览](../SetTheory/InnerModel/README.md) 统一列出其后的 J/L、OD/HOD
研究接口：ZF 背景下 L 满足 ZFC＋GCH，HOD[A] 满足 ZFC，HOD(A) 满足 ZF。
同一套规范码还用于 HOD 的有界序数关系呈现和内部坍塌；
[弱齐性比较](Forcing/Internal/Homogeneous/HOD.lean) 因而恢复扩张 HOD 的地模型 HOD 原像。
这些结论继续使用内部语法与模型自身序数，允许外部非良基及非标准有限长度。

[Skolem](SetTheory/Internal/Skolem.lean) 的 `ssk_hull_l` 在原 ZFC 内构造实际司寇伦
函数图 K 及任意内部可数种子 A 的最小闭包 N。规则域为全部内部公式码与变量编号
的积，输入是内部有限参数列；列外取基点 u，再在被量化变量处更新。存在见证时
K 返回真见证，否则精确返回 u。假公式的零元运算保证每个闭集包含 u，因此空种子
也得到非空闭包。最小性针对固定的 K，不把不同选择图的闭包宣称为同一个集合。

```lean
obtain ⟨u, C, S, T, D, K, N, hSkolem, hHull, hCountable, hu, hWitness⟩ :=
  SetTheory.Internal.ssk_hull_l I hZFC hω hModel hSeedSubset hSeedCountable
-- hHull 给出 A⊆N⊆X、对 K 的闭性及最小性；hWitness 是所有内部有限参数下的见证闭性。
```

通用有限元闭包见 [FinitaryHull](../SetTheory/FinitaryHull.lean)：`ZF.fc_hull_chain_l`
沿内部 ω 构造最小闭包，`ZF.cc_fseq_bound_l` 证明链并中的内部有限参数列落在某个
阶段，因而实际取并保持闭性。`ZF.fc_step_countable_l` 的单步可数性用最小原像
编号证明，保留 ZF 强度；自动司寇伦选择及完整可数闭包装配使用 ZFC。

[SupportBound](SetTheory/Internal/SupportBound.lean) 的 `sbound_exists_l` 证明每个内部
有限程序的全部坐标都有内部自然数界；[Support](SetTheory/Internal/Support.lean)
的 `ssat_agree_l` 证明界内赋值一致就保持真值。`ssk_full_l` 据此把有限参数见证
闭性提升到全部内部 ω→N 赋值。归纳性质均为实际原公式，允许非标准有限程序。

[TarskiVaught](SetTheory/Internal/TarskiVaught.lean) 的 `selem_iff_tv_l` 已证明完整
内部 Tarski–Vaught 等价，只需 ZF。`Selem_d ω c d` 与 `selem_m` 同时量化全部内部
公式码和完整内部赋值，比较大结构码 c 与子结构码 d 的满足关系。`Selem_d.trans_l`
给出复合，`Selem_d.models_l` 保持任意内部编码理论的模型性。
[ElementaryHull](SetTheory/Internal/ElementaryHull.lean) 从实际司寇伦构造自动取得
内部可数初等子模型，输入无需额外闭性或初等性证书。

```lean
obtain ⟨N, d, S, hSubstructure, hSeed, hCountable, hElementary⟩ :=
  SetTheory.Internal.selem_hull_l I hZFC hω hModel hSeedSubset hSeedCountable
-- hSubstructure.target 是实际子模型码，hSubstructure.subset 给出 N⊆X。
-- hElementary 比较全部内部公式与赋值，包含非标准公式码。
```

一般无限基数版本为 `ssk_hull_bound_l`、`selem_hull_bound_l`：额外输入 κ 的
`IsInfiniteCardinal` 证书及种子到 κ 的实际单射，输出的内部初等壳仍可单射到 κ。
原可数入口已经成为 κ=ω 的实例。有限参数列的 `ZF.fseq_bound_l` 与单步闭包的
`ZF.fc_step_bound_l` 仍只需 ZF；完整 Skolem 选择及小并装配使用 ZFC。
[SmallHull](SetTheory/Internal/SmallHull.lean) 的 `s1_hull_l` 将这套实际构造接到
Σ₁ 隶属子结构接口，供 Mostowski 坍塌和 Jensen 凝聚直接调用。

[SourceElementary](SetTheory/Internal/SourceElementary.lean) 的 `selem_source_l` 与
`selem_witness_l` 把完整内部初等性用于原公式保持及实际见证回拉。力迫层已构造
实际可数 `N[G]`，并由主条件和内部初等性提升指定原公式在所有 N 名称参数下的存在见证；
`selem_club_hull_l` 在指定内部 club 中构造初等模型，`ng_witness_hull_l` 据此从
properness 自动取得同一个 N 与主加强 q，见证池闭性由上述有限反射统一证明。
`ng_elementary_hull_l` 已进一步装配整个 `N[G]≺X[G]`：内部有限名称列及公式码精确回拉，
两张实际运算图在 proper club 中同时闭合，再调用内部 Tarski–Vaught。
结论包含全部内部公式码和赋值，允许外部非良基地模型；`X[G]` 传递且 `N[G]` 内部可数。
`ng_hchi_hull_l` 已把环境识别为实际 `H(eχ)`；小名称定理给出双向对应并保持 χ 的正则性。
`ng_next_master_l` 进一步自动选择同一个 N、地阶段主加强及每个泛型中的 N[G] 后继主加强。
二步主条件完整双向分解及全阶段共用的内部初等 N 已完成；原生多排序 AST
仍待完成；完整 proper 迭代引理及可数支撑保持已完成，见 [迭代接口](Forcing/ITERATION.md)。
审计入口为 `python scripts/check_internal_models.py`：ZF 基础逐声明限制在原七条
证书，司寇伦及初等模型装配另允许原选择公理证书，并收紧其中的 ZF 端点；全部数据定义
严格排除 `Classical.choice`，没有新增不可计算数据。

## 后续路线

小图 ZFC 模型、布尔值可靠性、标准布尔名称及任意地模型的内部泛型扩张已经落地。
支撑迭代已完成共同的二步条件构造、泛型双向分解、内部混合与最大值，以及全局
Cohen 后继名称装配，以及阶段名称搬运的存在、唯一性、严格复合与恒等性；
原子力迫双向传输、泛型回拉及扩张间的成员满覆盖嵌入也已证明。
二步名称到第一阶段名称的唯一转换、第二阶段名称性及其全局力迫证书已有证明。
双重求值已具总性、唯一性和组合滤子下的成员递归方程，二步等号与嵌套等号
精确对应。原模型内的名称摊平已补齐满射，`two_step_iso_l` 给出单次二步扩张与
双重扩张的成员结构同构。第二阶段关系的规范化保留所有原公式的力迫。
ZF 反射与全局判据只消费原 ZF；ZFC 消费者另保留自身理论。
零阶段及任意名称后继已有共同的部分函数条件格式，旧条件按原对象完全嵌入，
顶与前缀保持；限制投影保序，旧前缀的任意加强可保留尾部提升，且阶段链接能复合。
有限／可数支撑的限制、追加及拼接保持和参数化 Cohen 坐标后继均已构造。
阶段族已由模型内实际序列编码；`row_limit_l` 构造支撑极限及各旧阶段完全嵌入，
`row_system_limit_l` 可把极限写回序列后继续名称后继。
给定实际输入名称后，混合闭名称库、二步序、坐标后继与支撑极限均有唯一性证明及
原公式构造规格；语义名称的规范化与整个内部递归由后续层统一处理。
`name_pool_represent_l` 仅用 ZF 构造同条件的库内等值代表；有界存在见证使用 ZFC。
`row_next_witness_l` 精确保留指定前缀，`row_next_lower_name_l` 在 ZF 下提升第二坐标加强。
内部累积层级及覆盖定理已给出全局力迫等号类的唯一规范名称；最大值与全部
Cohen 名称入口直接返回规范固定点。规范化仅用 ZF，一般最大值仍保留 ZFC 前提。
唯一见证通过原收集与混合在 ZF 内统一装配；Cohen 规格的完整关系图及唯一性
已经核验，Cohen 名称、坐标后继和系统后继也已降低到 ZF。
完整规范三元组以 `Cohen_names_d` 表示并已证明字面唯一性；`Row_cohen_d` 进一步
唯一确定整个坐标后继，两者均有实际原公式，构造入口直接返回相应证书。
`row_iteration_l` 已从可读取全部历史的原公式后继规则构造任意内部序数长度的
有限／可数支撑迭代；存在性、唯一性和精确前缀方程仅需 ZF。归纳对象为实际
原公式，`cohen_iteration_l` 提供完整的参数化实例。
内部序数索引的阶段系统、极限与保持证明的依赖见
[迭代设施清单](Forcing/ITERATION.md)。真类超幂和不使用元层选择的 ZF 构造仍需各自的实际证明。

## 基础边界

- 基础结构允许任意载体和解释，不要求可构造、传递、外部良基、外部标准或可数。
  也不要求满足 ZF、ZFC、二阶理解或二阶封闭。
- 二阶封闭只作为给定结构上的可选接口。结构、二阶关系域、关系域的封闭性分开表达。
- 模型性相对于显式语义背景，默认取当前 Lean/Tarski 语义。域、等同、量词和真值
  预留相对化接口；相对模型性不自动推出外部模型性，跨背景传输须证明所需范围的对应。
- 另预留内部语法、理论与证明码的可选视角，默认仍是当前 AST 和推导核。内部码可以
  非标准，不要求外部解码或外部良基；标准语法的嵌入、代入保持及跨视角对应须实际证明。
  此能力不作为所有背景的前提；只有实际表示过的签名和内部代码范围才能调用对应接口。
- 对象载体、参数域和具体构造结果保持在预先固定的 universe；公共接口对该 universe
  多态，不通过强制提升载体来完成模型构造。语言及索引族的大小边界须显式说明。
- 一致性证明使用 Lean 元层的实际语义构造与推导可靠性，不以 Henkin 强完备性、
  自然数枚举、quotation 或可计算呈现为前置条件。既有完备性及其消费者保持原用途。
- 继续使用当前类型化一阶 AST 和普通 `Derives`。本路线不增加对象语言公理，
  不另造只供模型论使用的一套公式或推导核。

当前 `FirstOrder.Structure` 用 Lean 的 `Nonempty` 表达每个排序非空，这是默认实例的
边界。相对化版本的非空性由其背景语义解释，不把 `Nonempty` 提升为所有背景的前提；
改变这一解释时须重新核验相应推导规则，不能直接沿用默认可靠性结论。

同层要求针对模型载体及实际操作。打包所有 `Type u` 载体的元类型与单个载体的
universe 必须区别核对；不能把所有同层小集合或名称的总类升到更高层后，仍宣称模型
构造没有升层。小图模型已按下面的实际类型固定载体与小指标。

## 已有基础与实际缺口

| 层 | 当前入口 | 可复用内容与边界 |
| --- | --- | --- |
| 任意多排序结构 | [Logic/Semantics](FirstOrder/Semantics.lean) | 载体族、函数和关系解释、类型化环境、项求值、完整一阶满足关系；没有模型论上的良基性条件 |
| 普通推导可靠性 | [Derivation/Soundness](FirstOrder/Soundness.lean) | `Derives.sound` 对任意签名、结构、环境和局部上下文成立，不依赖公平枚举或完备性 |
| 隶属图数据 | [SetTheory/Model](SetTheory/Structure.lean) | 非空对象域加任意二元关系；`Extensional` 是独立合同 |
| 现有语义连接 | [Project/FirstOrderSemantics](SetTheory/ProjectSemantics.lean) | 一阶纯结构约化为同域隶属图；Project 的外延等同转换为逻辑等号时才要求外延性 |
| 裸 ZFC 目标 | [PureModel](ZFC/Pure/PureModel.lean) | `theory` 是现有原 ZFC 的纯语言像；公理正文和无限参数模式继续复用 |
| 二阶语义 | [Logic/SecondOrder](SecondOrder.lean) | 已有 Henkin 与 Full 语义，现由可选谓词域接口及规范 Full 实例连接；不自动满足任意理解模式 |
| 有界绝对性 | [LevyAbsoluteness](FirstOrder/LevyAbsoluteness.lean) | 一般二元界关系的绝对性已消费普通 `Str_emb` 层；有界见证回拉仅在有界公式证明中消费 |
| 布尔值语义 | [Boolean/Soundness](Boolean/Soundness.lean)、[Boolean/Native](Boolean/Native.lean) | 任意签名、布尔等号与关系、完整代入及等词同余、原 27 类逻辑公理与六规则可靠性；原生语义及模型性逐式对应 |

现有 Henkin / Full 满足关系的存在不代表已有二阶证明演算的可靠性或完备性；
`SemanticsMode.automationSupported` 也不能充当这些定理。

## 通用结构与映射

普通结构继续独立于所满足的理论。映射合同按数学用途拆分：

| 结论 | 所消费的条件 |
| --- | --- |
| 项与参数列的求值保持 | 载体映射与函数解释交换 |
| 正向原子保持 | 相应关系的正向保持；等号的正向保持来自映射本身 |
| 原子及无量词公式的双向保持 | 各排序单射、函数保持、关系双向保持 |
| 同构下全部公式的真值保持 | 上述嵌入条件加各排序满射 |
| 有界量词的双向保持 | 相关有界见证回拉条件；不把它加入普通嵌入的定义 |

已落地 `Fn_map`、`Str_emb`、`Str_iso`，并整层迁移 `LevyEmbedding` 的对应消费者。
正向关系同态、专门的无量词片段接口仍可按实际使用需求添加；不把这些未来接口计为已实现。

初等嵌入及子结构的 Tarski–Vaught 判据已落地。Skolem hull 先通过规则闭包给出实际
非空、函数封闭子结构，再证明 `Substructure_m.WitnessClosed_m`：对该子集内的任意有限
参数，原模型满足的存在公式在子集中有指定见证。`tarski_vaught_m` 即给出初等性；
`term_mem_m` 提供项闭包，`elementary_inclusion_m` 处理同一模型中嵌套的初等子结构。
判据证明中的经典反证只留在 Prop；限制结构、环境和包含映射均不选择数据。
本接口针对原 AST 与默认 Tarski 语义，不声称非标准内部公式码的初等性。
它不作为图模型、布尔值一致性或一般模型存在问题的强制前置。

### Skolem 壳的调用与选择边界

最小导入为 `YesMetaZFC.Model.FirstOrder.Skolem`，数学接口位于
`YesMetaZFC.Logic.FirstOrder.Skolem_m`；底层闭包只需导入 `YesMetaZFC.Model.Closure`，
不依赖 Mathlib、集合论或一阶语法。

- 调用方给出 `F : Skolem_m ℳ`，以及任意生成谓词 `A : ∀ s, ℳ.Carrier s → Prop`。
  `F.hull_m A` 是实际 `Substructure_m ℳ`，`F.hull_elementary_m A` 证明初等性；
  `hull_models_iff_m` 对任意理论传输模型性，不限于 ZF 或 ZFC。
- `F.witness φ ρ h` 只在 `h : ∃ a, ...` 时返回数据；正确性由 `F.satisfies` 认证。
  不从原结构非空性选择默认对象。即使 `A` 为空，各排序仍有真公式的指定见证。
- `seed_mem_m`、`hull_le_m`、`hull_mono_m`、`hull_idem_m` 给出闭包公理；最小性
  针对同一套指定 Skolem 规则，不是说原结构有一个与见证选择无关的最小初等子模型。
- 任意索引生成族可取 `fun s a => ∃ i, A i s a`，`hull_union_iff_m` 连接逐项闭包。
  任意额外运算族先用 `RuleFamily_l.of_operations_l` 装配，再交给 `hull_with_m`；
  `hull_with_closed_m`、`hull_with_le_m`、`hull_with_elementary_m` 分别证明双重封闭、
  最小性和初等性。规则族也可用 `union_l` 任意合并或用 `reindex_l` 重编号。
- 签名的三个 universe、结构载体 universe、额外指标及输入指标 universe 独立多态。
  载体始终是原载体的子类型；合并不同大小的输入族只提升输入指标，不提升模型域。
  底层允许无限元规则，因此没有无条件声称 ω 步闭包或 Löwenheim–Skolem 基数界。
- 没有无条件证明每个结构都有 `Skolem_m`，也没有把该见证数据从 Prop 选择出来。
  调用方需提供显式/可定义的见证系统，或另行证明所需选择原则及存在性。
  此处尚不是任意非标准 ZF 模型内部集合编码的壳构造；内部化须另有内部语法和满足关系。

`python scripts/check_elementary.py` 检查整个闭包、初等子结构与 Skolem 切片的实际声明，
并对闭包及壳的数据定义严格排除 `Classical.choice`；初等性继承 Tarski–Vaught 的 Prop
经典推理。没有新增公理、`noncomputable` 或原生计算可信依赖。

### 超幂与 Łoś 的调用边界

最小导入为 `YesMetaZFC.Model.Ultrapower`；公开接口位于
`YesMetaZFC.Logic.FirstOrder.Ultrapower` 和 `ReducedProduct`。任意签名的排序、函数
和关系均使用原生类型化 AST，模型不要求满足 ZF、可数、传递或外部良基。

- 固定 `I : Type x` 与 `ℳ : Structure.{u,v,w,max x y} σ` 后，
  `Ultrapower.structure_m ℳ U` 的结果仍是同一个 `Structure.{u,v,w,max x y} σ`。
  输入已处于该层，并非输出时才升层；同层指标和较小指标都可直接调用。
  无 `ULift`、`Shrink` 或提高模型载体的隐式包装。任意更高 universe 的指标不在
  此固定域内：其全函数空间通常更大，不能同时无条件承诺“任意更大指标”和“不升层”。
- 只给滤子即可构造约化积，真滤子给出 `diagonal_m`。超滤加 `Witness_m` 给出
  `diagonal_elementary_m` 与 `models_iff_m`。理论可以是任意闭句集合。
- 一般结构族 `ℳ : I → Structure ...` 使用 `ReducedProduct.structure_m`，并显式
  提供 `Nonempty_m ℳ`（逐排序的截面空间非空）。逐点非空在无选择背景下不足以
  自动取得该条件；恒定结构族的超幂已无选择地证明该条件。
- `Germ_l` 以滤子意义下相等为等价关系。有限参数列通过 `map₂_l` 递归装配，函数
  和关系直接商消去；`env_surjective_m` 仅在 Prop 中逐项回拉有限环境，不定义
  全商的代表元函数。因此 `los_m` 的截面环境形式覆盖所有有限商参数。
- `Witness_m` 只要求原公式在大集上逐点存在时，有一个截面在大集上见证。
  `los_iff_witness_m` 证明它与完整 Łoś 等价，不自动从超滤性推出。
  可以传入 `WitnessData_m` 的显式全域见证运算，经 `witness_of_data_m` 获得条件；
  或显式假定本指标及载体上的 `Choice_m`，经 `witness_of_choice_m` 使用。
  未用宿主 `Classical.choose` 或全局选择公理自动填充这些前提。
- 指定点的主超滤 `Filter.point_l i` 无需额外选择条件：`principal_witness_m`
  已证明见证拼接；`principal_iso_m` 实际构造原模型与主超幂的同构，其逆由指定点
  的商求值 `evaluation_m` 给出，不从满射选逆。
- 当前是原 AST 与宿主 Tarski 语义的同层超幂，不宣称完成任意非标准 ZF 模型内部
  编码的超幂，也没有声称任意非主超幂外部良基或自动存在 Mostowski 坍缩。

`python scripts/check_ultrapower.py` 审计全部五个新模块的实际声明与构造性端点，已接入
CI。商数据使用 `propext` / `Quot.sound`，不使用选择；Łoś 和对角嵌入的 Prop 证书
使用经典逻辑，单看整个含证明结构的公理列表不能误判为选择了 Type 数据。

## 可选的二阶接口

在默认 Lean 背景中，固定一阶结构 `ℳ`，给出每个有限排序列 `Γ` 的可量化关系域及其解释：

```text
R Γ : Type u
interpret Γ : R Γ → (Values ℳ.Carrier Γ → Prop)
```

这只是二阶框架，不预设它包含全部谓词，也不预设任何理解模式。复用现有
`SecondOrder.Henkin.Structure` 的实际关系域，避免新增一个内容重复的模型记录。
相对化版本的关系域、解释及封闭性由背景决定；背景内部的 Full 不自动等于外部 Full。

| 可选合同 | 数学含义 |
| --- | --- |
| 关系外延性 | 解释相同的关系对象相等；仅在确实需要关系对象等号时消费 |
| 指定公式类的理解 | 所指定公式类、任意合法对象与关系参数所定义的谓词在关系域中有代表 |
| Full | 对每个 `Γ`，解释映射覆盖全部 `Values ℳ.Carrier Γ → Prop` |

理解模式与 Full 分别登记，不能从“对可定义谓词封闭”推出“包含全部外部谓词”。
模型内部幂集存在性也不能直接提供全部外部子集。

固定载体 universe 后，有限值列、其谓词空间及相应函数空间可保持同层；相关类型
必须由 Lean 实际检查。`Full.structure_of` 已使用谓词本身作关系对象、恒等函数作解释，
并以 `Full.satisfies_iff` 证明它与现有 Full 满足关系逐公式一致。
函数可先由关系图表达；如需原生函数变量，应另给相应实际解释及应用合同。

二阶框架及其封闭性均不进入基础 `Structure` 的必填字段，也不自动导出为全局实例。
Full 语义的保真只在已证明范围内使用，不能把一阶可靠性或完备性直接改称 Full 二阶结论。

## 图模型入口

`import YesMetaZFC.Model.SmallGraph` 已构造默认 Lean 背景中的实际 ZFC 模型。
数学命名空间为 `YesMetaZFC.Model.SmallGraph`，对象语言仍是原纯集合论语言 `ℒ`。

| 层 | 已实现的构造与证明 |
| --- | --- |
| [有根图与双模拟](SmallGraph/Bisimulation.lean) | `SG_graph` 扩展已有 `SetTheory.Structure`，增加一个根；原始图不要求良基。`bs_refl`、`bs_symm`、`bs_trans` 证明等价性，`bs_children` 给出根成员匹配，`mem_congr` 保证商成员关系良定义。 |
| [小图并合](SmallGraph/RootSum.lean) | `root_sum` 在分量不交并上添根；`sum_mem` 精确描述其成员，`sum_wf` 证明分量良基时并合良基。`WF_graph` 是本次模型使用的具体呈现子类。 |
| [图商集合](SmallGraph/Sets.lean) | `SG_set` 是良基有根图按双模拟取商；`mem` 直接商化原成员关系。`ext`、`mem_wf`、`small_presentation` 依次证明外延性、商成员良基性与每个集合的小成员呈现，`small_collect` 收集任意小指标族。 |
| [集合闭包](SmallGraph/Closure.lean) | `separation` 对任意 Lean 背景谓词成立；`power` 以小节点域上的全部谓词为指标构造全幂集。`collection` 覆盖任意二元关系，不要求函数性；`pair`、`union` 直接使用图并合与长度二成员路径。 |
| [无穷图](SmallGraph/Infinity.lean) | `omega_graph` 以单位元列表长度呈现有限序数，另添以全部有限节点为成员的根；`infinity` 证明原公理的空集与后继封闭条件。 |
| [基础与选择](SmallGraph/Choice.lean) | `foundation` 从商成员良基性证明原基础公理；`choice` 对两两不交非空族先选实际成员，再沿小呈现收集，重复呈现保持同一选择。 |
| [原 ZFC 核验](SmallGraph/ZFC.lean) | `sg_project_zfc` 逐条证明原固定公理及任意有限参数的完整分离、收集模式；`sg_models_zfc` 接入既有 `PureModel.theory`，`zfc_consistent` 由 `Native.consistent` 得到裸 ZFC 一致性。 |

`sg_model` 的载体和成员关系由上述图商直接给定，没有现成模型、一致性、大基数或
封闭性合同作为构造参数。`zfc_consistent` 的结论是 Lean 元层命题
`Derives.Consistent PureModel.theory []`，可直接供应现有元数学接口的一致性参数。
原语法、原公理、普通 `Derives` 和已有对象语言不完备性终点保持不变。

节点域与每个图并合的指标在 `Type u`；`SG_graph.{u}`、`WF_graph.{u}` 及
`SG_set.{u}` 从起点固定在 `Type (u+1)`。分离使用节点子类型，幂集使用
`G.Domain → Prop`，并合使用 `Option (Σ i, (F i).Domain)`，都没有抬高小节点层级。
对固定 `I B : Type (u+1)`，`I → SG_set.{u}` 的函数商及
`Σ A : Type u, (A → A → B) × A` 的带标签小图也保持 `Type (u+1)`；这些类型边界
已经检查。后续真类超幂和力迫按此固定载体设计，不重新打包全部 `Type (u+1)` 节点域。
它们的等价关系、解释及 ZFC 保持性仍属于后续构造的证明任务。

38 个小图关键接口的依赖审计显示：图并合、ω 图等数据构造不依赖公理，
`sg_model` 仅依赖商成员关系所需的 `propext`；商证明使用 `Quot.sound`，经典存在性
与选择证明使用 `Classical.choice`。没有新增不可计算数据实例、`sorry` 或自定义公理。
原 ZFC 终点另沿用 `Axioms.{extensionality,emptySet,pairing,union,powerSet,infinity,foundation,choice}`
各一处已有的 `sentence!` 自由闭合性 `native_decide` 依赖，共 8 处；没有新增原生计算可信依赖。

2026-09-11 在 `be4d15d` 上的未提交工作区完成 `lake --wfail build` 的 973 个任务和
`check-all.sh --library-only` 的全部 979 个 Lean 模块，零错误、零警告，未运行扫描器。
小图层共 8 个模块、692 行，最长 122 行，单模块实际构建均低于 4 秒。
识别迁移并忽略行尾差异后，整个未提交 Lean 工作区新增 2,586 行、删除 543 行，
净增 2,043 行，包含此前模型目录迁移与通用底座。
对应源码与工具链配置指纹为
`4d1982887a29f4149907087ac983749f30f12cfbcb844d0a99f0ab1e9247da38`。

## 布尔值模型入口

`import YesMetaZFC.Model.Boolean` 提供通用语义及实际标准名称模型；只需任意签名上的
语义与原生对应时导入 `Boolean.Native`。逻辑验证使用仓库原 AST、Hilbert 公理和六条推导规则。

| 层 | 已实现的接口 |
| --- | --- |
| [序与布尔代数](Boolean/Algebra.lean) | `PO_bot`、`CS_order`、`Sup_order`、`BA_alg`、`CB_alg` 按所需强度分开；`prop_algebra` 是实际实例。任意索引确界通过 `B → Prop` 中的值域谓词形成。 |
| [求值与代入](Boolean/Semantics.lean) | `BV_str` 给出载体、函数、布尔等号和关系；`value` 复用公共公式求值器，`value_substitute` 复用原项及环境代入。 |
| [等词与可靠性](Boolean/Soundness.lean) | `BV_laws`、`value_congr`、`axiom_valid`、`rules` 已证明；证书接入公共 `Sem_rules`。任意结构不默认具备名称的混合或最大值性质。 |
| [原生对应](Boolean/Native.lean) | `native_str`、`native_laws` 是实际装配；`native_value` 和 `native_models` 精确恢复原满足关系及 `Theory.Models`。 |
| [名称与等号](Boolean/Equality.lean) | `BV_graph` 是有布尔边标签的良基小图；`bv_eq`、`bv_mem` 按成员匹配解释，已证明自反、对称、传递、隶属同余及外延性。 |
| [混合与最大值](Boolean/Maximum.lean) | `root_sum`、`mix` 保持小节点层级；链不动点给出不交细化，`maximum` 给出存在量词的实际名称见证。 |
| [集合运算](Boolean/Closure.lean) | 分离重加权根成员，幂集遍历全部小权函数；并集、配对和任意二元关系的收集均有实际名称。 |
| [基础与无穷](Boolean/Foundation.lean) | 基础公理沿呈现图归纳；[Infinity](Boolean/Infinity.lean) 复用原单位元列表 ω 图并赋顶值，证明后继封闭。 |
| [选择集](Boolean/Choice.lean) | `selection` 构造模布尔等同的不交系数，`choice` 在原非空、不交条件下给出选择集，处理重复名称呈现。 |
| [原公理核验](Boolean/ZFC.lean) | `formula_correct` 对应原 `fo_formula`；`separation_core`、`collection_core` 保留全部有限参数；`bv_models_zfc` 核验原 `PureModel.theory`。 |

最终定理的数学参数只有实际完备布尔代数：

```lean
bv_models_zfc {B : Type u} (𝔹 : CB_alg B) : (name_model 𝔹).models PureModel.theory
```

`BV_name B = BV_graph.{u,u} B : Type (u+1)` 固定模型载体；每个图的节点及布尔值域
均在 `Type u`。图并合、不交细化、混合与幂集没有扩大节点 universe。布尔值等号
保留所有真值，不将顶值等同替换为名称的 Lean 相等。该模型没有现成 ZFC 模型、
一致性、大基数或最大值原理作为未实现的前提。

`Boolean.zfc_consistent` 在实际 `prop_algebra` 上调用原六规则可靠性，得到 Lean 元层
裸 ZFC 一致性。没有提取超滤子、泛型滤子或借用 Henkin 完备性。

50 个布尔关键接口及 8 个小图交叉入口已做依赖审计：名称、图并合、混合、ω 和
`name_structure` 的数据构造不依赖公理；一般布尔值可靠性、名称等词、分离、幂集、无穷、
基础的通用证明只涉及 `propext`、`Quot.sound`。不交细化、最大值和收集使用
`Classical.choice`。原 ZFC 终点沿用原八条固定公理已有的句法闭合性 `native_decide`
依赖；无新增公理、`sorry`、不可计算数据实例或原生计算可信依赖。

在 `a911617` 的未提交工作区，`lake --wfail build` 的 998 个任务和
`check-all.sh --library-only` 的全部 1,004 个独立 Lean 模块均通过，零错误、零警告。
布尔层共 25 个模块、2,388 行，最长模块 191 行；整个代码工作区新增 2,396 行、删除
6 行，净增 2,390 行。新模块单次检查均低于 6 秒；全库本次最慢模块为 55 秒。
源码与工具链配置指纹为 `17b05ad24fb8561093da8905373d0474caa8f23a80a8a42a9525db7130f4766e`。
没有运行扫描器或提交 Git。旧 `DefinitionalSemantics` 中的 binder 环境等式已直接公开为
`Semantics.substitute_lift`，原消费者同步改用该名字，布尔适配复用同一证明。

## 不使用元层选择的 ZF 目标

这一目标尚未实现。小图的 `small_collect`、`collection` 仍选择商代表或关系见证；
其经典基础公理证明也使用元层排中律。当前全小图载体支持任意元层谓词分离：对命题 `P`
形成 `{1} ∪ {0 | P}`，原基础公理给出的极小元可判定 `P ∨ ¬P`。这一推导已经在临时
Lean 依赖核验中证明，只涉及 `propext`、`Quot.sound`；Lean 现有 `Classical.em` 的依赖
则包含 `Classical.choice`。该结论针对当前全小图载体与元层解释。

布尔名称的收集证明通过 `maximum` 选取见证。一般力迫的最大值原理与选择公理的关系见
[Miller 的原论文](https://people.math.wisc.edu/~awmille1/res/max.pdf)，特别是定理 2。
无元层选择的 ZF 构造须另证明不依赖最大值原理的见证界及收集；现有 ZFC 端点的
ZF 理论限制仍带元层选择依赖，不能作为该目标的交付。

用户已允许重选架构并开展一小时并行研究。实际候选、无选择的条件秩与对角界、
描述树、普通及稳定观察语义的核验结果见
[研究记录](../../markdown/CHOICE_FREE_ZF_RESEARCH.md)。完整 ZF 仍未完成；研究证明没有
进入默认编译层，也不将各候选分别满足的性质合并声称为一个已完成模型。

## 一致性与交付顺序

一致性走以下两个原生语义出口，理论和语言均不要求枚举：

```text
实际二值模型 + 原 Derives.sound → Derives.Consistent T []
实际非平凡布尔值模型 + 布尔值可靠性 → Derives.Consistent T []
```

“Lean 原生”指由元层定义和证明构造可核验的证明项，不指以 `native_decide`、
新公理或未经验证的语义断言替代证明。现有可信基的边界继续遵守；新增不可计算
构造不因接口规划而自动获得许可。

普通结构接口及其消费者迁移、二阶可选接口、小图 ZFC、布尔值可靠性和标准名称 ZFC
模型均已完成。内部泛型扩张与 CH 两侧模型亦已实现；有限支撑直接并、任意名称
二步 CCC 及完整内部有限支撑迭代 CCC 保持已经证明，参数化 Cohen 规则有一键实例。
内部主条件、club 版 properness、CCC 实例、可数支撑精确融合及 N[G]≺H(eχ) 全内部初等提升已完成；
`two_step_master_extension_l` 自动装配实际二步主加强；`ng_family_hull_l` 一次构造
同一个 N 对全部成员阶段的内部 H(χ) 泛型初等提升。完整可数支撑 properness
保持已通过实际交集 club 装配。`ng_family_forcing_l`
已将共同提升编码为内部力迫证书，`row_step_proper_name_l` 已处理随泛型变化的
后继商条件名称，`row_step_proper_l` 已迁移为其规范名称特例。`row_dense_name_l`
在任意阶段间选择进入指定稠密集的商加强名称，保留原主前缀；`ng_ground_trace_l`
给出 N[G] 中旧阶段条件的精确回拉。`row_step_pil_l` 已完成相邻后继的内部
`Row_pil_d`，`row_pil_value_l` 构造 `τ∈G∩check(N)` 结论所需的实际名称；
`row_pil_comp_l` 复合已证明区间，`row_pil_dense_l` 保留实际尾部比较并满足指定
稠密集。名称不改写的阶段传输保持原子、
有界公式和旧关系力迫。通用 Δ₀ 绝对性位于 `Model.SetTheory.ProjectBounded`，
适用于任意成员满单射，不额外要求两边满足集合论公理。
实际阶段链接已包含规范拼接的最大下界性质及固定尾部比较的稠密闭性；商名称前缀投影、换段后的商成员
力迫及实际尾部加强的复合只用 ZF。`row_model_sequence_l` 已构造内部共尾阶段列
和全部 N 稠密集的枚举，并证明原 N 条件的支撑位于 `sup(N∩β)` 以下；
这些指标列上的相容主前缀递归、整列比较及融合主性已经实现。
`row_iteration_pr_prepare_l` 已从实际 proper 后继规则自动构造统一辅助图、共同 N
和其全部成员后继的迭代引理，包含所需名称属于 N 的证明；Cohen 规则有实际实例。
该入口同时返回全部内部有限区间的迭代引理，使用原公式的内部 ω 归纳。
变动前缀对旧名称的限制比较已经证明延长保持、共尾融合保持及支撑界下的完整还原；
`row_pr_omega_thread_l` 现从共同 N 和真实 proper 后继图自动构造首个内部极限的
相容主前缀列。通用 `class_indexed_choice_l` 使用实际反射闭包界定名称候选，
`row_pr_coherent_l` 以内部 ω 归纳证明所有前缀一致。`row_pr_bound_l` 保持任意早期名称
的全部后期比较；`row_pr_master_fusion_l` 自动构造满足这些比较的实际主融合。
`row_iteration_pr_omega_l` 已从实际 proper 规则、可数支撑迭代与种子自动完成内部 ω
终点的全部区间迭代引理。通用极限构造保留 γ=sup(N∩β)，原公式的内部超限归纳
已由 `row_pr_induction_l` 完成；`row_iteration_pr_l` 自动返回共同 N 上的全部区间，
`row_iteration_pr_exists_l` 同时构造任意内部长度的可数支撑迭代。
`cohen_iteration_pil_l` 给出仅参数化添加量与长度的直接实例。
`fc_trace_club_l` 用最小闭包及内部递增链的并构造实际交集 club；三张闭包图的
共同闭性给出每个指定 N 的内部提升。`row_iteration_proper_l` 已证明全部阶段的
完整 `Proper_d`，`row_iteration_proper_exists_l` 和 `cohen_iteration_proper_l` 自动
构造整个 proper 迭代。`two_step_master_decompose_l` 已自动构造 N[G] 名称并给出
二步主条件的完整双向分解；反向第二坐标证书保持原首阶段泛型。
`proper_countable_l` 进一步对全部旧集合反射可数性，`proper_omega_one_l` 精确保留
第一不可数序数。`row_iteration_preserves_l` 与 `cohen_iteration_preserves_l` 已把
各阶段的 ZFC、内部 ω、ω₁ 及旧可数性对应接入自动装配。
`proper_set_cover_l` 进一步给出旧集合的新可数子集的实际旧可数覆盖；相同规范
嵌入及所有迭代阶段的自动入口均已包含此结论。旧可数性反射已迁移为通用覆盖的推论。
无元层选择的 ZF、真类超幂亦待构造。

每次交付都须满足：实际实例与消费者存在、没有加强数学前提、原接口迁移完整、
无占位公理或隐藏缺口。沿用单模块低于 2,000 行、未提交增量不超过 3,000 行、
单模块类型检查超过一分钟立即诊断优化的约束；不提交 Git，直至用户明确允许。

## 对照资料

同层类型检查参考 [Lean universe 规则](https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/)。
结构映射与初等性可对照 [Mathlib 的 ElementaryMaps](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/ElementaryMaps.html)，
只参考数学接口，不引入其依赖或替换仓库的显式结构约定。
[Han 与 van Doorn 的布尔值模型形式化论文](https://arxiv.org/abs/1904.10570)
包含一阶布尔值可靠性及其集合论应用；本仓库使用自己的 AST、推导核与原 ZFC 公理，
实现采用上述固定层级的小图名称。
