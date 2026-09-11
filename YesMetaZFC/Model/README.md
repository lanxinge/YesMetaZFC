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

原 `LevyEmbedding` 已直接扩展 `Str_emb`，仅额外保留有界见证回拉；旧层的环境映射、
项与参数列证明已迁走，全部绝对性消费者使用新接口，没有转发证明层。
原值列骨架迁入 [Values](Values.lean)，原关系解释层的值列／赋值／环境转换迁入
[Valuation](FirstOrder/Valuation.lean) 并推广到任意签名 universe；原消费者直接使用迁入定义。

三个角色在接口中明确分开：给定背景 `𝒱`、模型解释 `ℳ : Sem_model 𝒱`、语法视角 `S`，
实际解释映射 `I : Sem_map S.code ℳ.algebra` 按 `𝒱.valid (I.fm (S.code.fm φ))` 检查每条标准
公理。`Sem_map.models_iff` 将它连接到 `ℳ.models`，只比较标准像，不增加内部码反射。

`Proof_view.has_proof` 明确表示“给出一个被检查接受的码”的外部存在性；它不冒充背景
内部量词所表达的证明存在判断。当前内部码接口的实际默认实例是原 AST／证明树，尚未
构造非标准码背景的全域满足关系。相对模型性也不自动反射为外部模型性。

以上数据构造没有新增 `noncomputable`、选择实例、`sorry` 或自定义公理。对象载体与原生
谓词域保持既定 universe；打包这些类型的元层记录不是新的模型载体。

通用底座的 44 个关键接口已做依赖审计，没有 `sorryAx`，仅涉及已有的 `propext`、
`Quot.sound`、`Classical.choice`；后者用于原生经典逻辑可靠性证明。
`Model` 入口的 41 个源码依赖不包含 Henkin 或具体 ZFC 模块；具体小图入口单独列在下表。

| 内容 | 导入入口 | 目录 |
| --- | --- | --- |
| 任意结构上的一阶语义、环境、可靠性与有界绝对性 | `YesMetaZFC.Model.FirstOrder` | [FirstOrder](FirstOrder.lean) |
| 高阶、无穷及二阶语义 | `YesMetaZFC.Model.HigherOrder`、`YesMetaZFC.Model.Infinitary`、`YesMetaZFC.Model.SecondOrder` | [SecondOrder](SecondOrder.lean) |
| 原有 Henkin 构造及强完备性 | `YesMetaZFC.Model.Henkin` | [Henkin](Henkin.lean) |
| 关系解释、扩张、模型闭包与传输 | `YesMetaZFC.Model.Interpretation` | [Interpretation](Interpretation.lean) |
| 隶属结构及 Project 语义连接 | `YesMetaZFC.Model.SetTheory` | [SetTheory](SetTheory.lean) |
| 原生小图 ZFC 模型与一致性 | `YesMetaZFC.Model.SmallGraph` | [SmallGraph](SmallGraph.lean) |
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

## 后续路线

以下区分已经落地的小图模型与后续构造。布尔值可靠性、真类超幂和力迫的模型性
仍需各自的实际证明，不能从通用底座或载体层级直接推得。

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
| 布尔值语义 | [上下文底座](Semantics/Algebra.lean) 已预留解释运算 | 仍需实际布尔代数、布尔值等号与量词实例，并核验其规则证书；通用代数本身不算布尔值可靠性已完成 |

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

初等嵌入、子结构与 Tarski–Vaught 等通用工具可在该层上发展，但不作为图模型或
布尔值一致性证明的强制前置。尤其不把一般模型存在问题改道到可数 Henkin 枚举。

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

任意签名的通用层放在 `YesMetaZFC/Model/`，ZFC 专门构造只消费该层。保留当前 AST；
布尔值等号和关系解释取值于布尔代数 `B`：

```text
eqValue s : A s → A s → B
relValue r : Values A (σ.relDomain r) → B
⟦φ⟧ρ : B
```

布尔值等号不能定义成 Lean 等号的真假判定。它需要自反、对称、传递及函数／关系
同余；这些合同支持当前内核的对象等词替换规则。一般布尔值结构不默认要求
`eqValue a b = ⊤ → a = b`，也不默认要求存在量词的上确界能被某个见证取得。
分离性、混合性和最大值原理属于后续各自的接口和定理。

命题部分只消费布尔代数运算及其定律；对象量词另外消费相应值族的上确界与下确界。
完整布尔代数可提供通用的具体装配，但不要把它传播到只需有限布尔运算的引理。
载体、索引族和真值代数的 universe 由同层条件统一检查。

最先攻克的证明是等词同余、代入正确性和完整推导可靠性。若所有背景理论公理的
值都是 `⊤`，则对原内核推导 `T; Γ ⊢ φ` 证明

```text
(Γ 中公式在 ρ 下的值之有限交) ≤ ⟦φ⟧ρ。
```

随后才用非平凡性 `⊥ ≠ ⊤` 排除矛盾推导。这里既不需要选取超滤子获得二值模型，
也不需要 Henkin 强完备性。普通 `Prop` 语义应有实际的特例装配和逐公式对应，
以接入当前结构库；不得只留下没有实例的真值代数合同。

ZFC 专门层随后按指定构造给出载体、布尔值等号与隶属，并验证原公理及无限模式。
命名递归、混合、商模型或 forcing 等具体技术只在相应任务中确定；不预设源结构
外部良基，不用一种受限模型构造替代任意结构上的通用语义。

## 一致性与交付顺序

一致性走以下两个原生语义出口，理论和语言均不要求枚举：

```text
实际二值模型 + 原 Derives.sound → Derives.Consistent T []
实际非平凡布尔值模型 + 布尔值可靠性 → Derives.Consistent T []
```

“Lean 原生”指由元层定义和证明构造可核验的证明项，不指以 `native_decide`、
新公理或未经验证的语义断言替代证明。现有可信基的边界继续遵守；新增不可计算
构造不因接口规划而自动获得许可。

普通结构接口及其消费者迁移、二阶可选接口、原生小图 ZFC 模型与一致性现已完成。
后续布尔值后端仍需完成等词、量词和规则证书，再核验其具体 ZFC 模型；
本文件中的后续规划不计作已实现成果。

每次交付都须满足：实际实例与消费者存在、没有加强数学前提、原接口迁移完整、
无占位公理或隐藏缺口。沿用单模块低于 2,000 行、未提交增量不超过 3,000 行、
单模块类型检查超过一分钟立即诊断优化的约束；不提交 Git，直至用户明确允许。

## 对照资料

同层类型检查参考 [Lean universe 规则](https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/)。
结构映射与初等性可对照 [Mathlib 的 ElementaryMaps](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/ElementaryMaps.html)，
只参考数学接口，不引入其依赖或替换仓库的显式结构约定。
[Han 与 van Doorn 的布尔值模型形式化论文](https://arxiv.org/abs/1904.10570)
包含一阶布尔值可靠性及其集合论应用；本仓库仍须对自己的 AST、推导核、ZFC 公理和
同层约束完成独立实现与验证。
