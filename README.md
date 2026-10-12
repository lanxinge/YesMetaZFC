# YesMetaZFC

[中文](README.md) | [English](README.en.md)

**目标是通用的集合论研究平台。**

YesMetaZFC 在 Lean 4 中发展一阶逻辑、集合论与元数学的形式化基础，
围绕对象语言、形式推导、模型语义和证明自动化积累可复用接口，仅依赖工具链自带的 Lean / Std。
当前已完成裸 ZFC 的具体 Rosser 独立句、D1–D3、Löb 与哥德尔第二不完备定理，
以及使用最终纯公式自身完整 AST 编码的带参数固定点和 Tarski 真不可定义定理。
原生小图双模拟商已实际构造出 ZFC 模型，并在 Lean 元层证明裸 ZFC 一致。
标准布尔名称模型也已对任意完备布尔代数构造并核验原 ZFC，包含全部有限参数模式。
地模型全部内部名称的泛型商已证明原公式真值定理及完整 ZFC 保持，允许外部非良基地模型，
参数化 Cohen 添加与可数闭塌缩分别构造了 ZFC＋¬CH、ZFC＋CH 模型，
并在原推导核中证明 CH 双侧不可证，见 [力迫模块](YesMetaZFC/Model/Forcing/README.md)及其[功能目录与阅读顺序](YesMetaZFC/Model/Forcing/INDEX.md)。
Rosser 独立性与哥二不可证性以裸 ZFC 一致为前提；Tarski 语义版覆盖任意裸 ZFC
模型和每组有限参数赋值。准确的公式范围、编码约定与声明见 [TROPHIES.md](markdown/TROPHIES.md)。

## 内模型与可容许递归

[内模型进度与接口](YesMetaZFC/SetTheory/InnerModel/README.md) 汇总已实现结果及其理论强度：

| 方向 | 当前结果 |
| --- | --- |
| Jensen J 与 L | KPi 中构造闭包、J 层级及实际 L 模型；ZF 背景下同一 L 满足 ZFC＋GCH |
| 集合计算与良序 | C 风格集合 DSL、Δ₀ 判定与 Σ₁ 见证验证；KPi＋V=L 下 Δ₁ 与总 J 搜索等价；各非空 J 层有统一局部 Σ₁ 良序及同层完整初段 |
| OD 与 HOD | 内部规范编码、Σ₂ 成员证书、最小代表；仅需 ZF，HOD[A] 为 ZFC 模型，HOD(A) 为 ZF 模型 |
| 弱齐性力迫比较 | 呈现为 OD 的弱齐性力迫满足 HOD 从扩张到地模型的包含关系；固定参数版和 Cohen 实例均已完成 |

模型可以在外部非良基、ω 非标准；上述对象和良序均按模型内部解释。
普通 J 已实现；L[A]、更强的 OD 图复杂度及无参数 HOD 完整模型接口的归并尚待完成，
集中见[尚未完成](YesMetaZFC/SetTheory/InnerModel/README.md#尚未完成)。

[迭代树](YesMetaZFC/SetTheory/LargeCardinal/Iteration.lean) 已完成 Pₙ 全前驱递归、内部下降反证，
以及返回嵌入失败时的联合尝试树和正则下降秩。nice 后继的背景可数闭性、
[到 j(A) 的完整初等复制](YesMetaZFC/SetTheory/LargeCardinal/ExtenderSetCopy.lean) 已构造，保留支撑端点及有限幂子集上的一致性。
[整棵 nice 树的复制](YesMetaZFC/SetTheory/LargeCardinal/IterationCopyTree.lean) 已通过内部类依赖选择与相容图列取并完成，保留原根嵌入和所有交换方块。
[联合尝试树的完整像](YesMetaZFC/SetTheory/LargeCardinal/IterationAttemptMember.lean) 已由有限真值证书的绝对性及实际有限节点拥有性证明，原节点公式和调用方已迁移。
[移位秩与下降复制树](YesMetaZFC/SetTheory/LargeCardinal/IterationFailureCopy.lean) 已从返回失败自动构造：高度列覆盖内部 ω，每条严格树边上新高度小于旧高度的像，实际正则秩段包含相应扩展器。
[指定超幂证书的读取](YesMetaZFC/SetTheory/LargeCardinal/IterationUltraRead.lean) 已保留原商、常值图、坍塌与复合图，并重新证明完整初等性；容器只需有限闭性，拥有极限秩段提供不要求正则性的实例。
[nice 树返回定理](YesMetaZFC/SetTheory/LargeCardinal/IterationNiceReturn.lean) 与 ω₁ 长弱迭代策略已完成。
[弹性类型的一步伸展](YesMetaZFC/SetTheory/LargeCardinal/TypeOneStep.lean) 已接通原定义的子类型查询、任意内部有限排列及同一扩展器，武丁实例保留精确实现高度。后续采用双树坍缩穷尽的直接决定性路线；L(R) 的 AD 尚未证明。
[局部不可分辨对象](YesMetaZFC/SetTheory/LargeCardinal/LocalIndiscerniblesLeast.lean) 已在 ZF 中实际构造，包含完整内部类型、原公式真值对应及唯一的字典序最小选取。
[有限后继秩层的完整类型搬运](YesMetaZFC/SetTheory/LargeCardinal/LocalTypeTransportTuple.lean) 已接通该最小对：内部任意正有限层高和有限元组均可自动搬运，整个 V(θ+ω) 参数带保持原值，原 κ 型集合与全部内部查询不变。
[类型游戏的图恢复](YesMetaZFC/SetTheory/LargeCardinal/TypeGameDecoding.lean) 已接到实际子类型见证：完整节点、空根和高度查询均自动编译，任意有限排列下恢复原树、末位及函数图的单点延长；重置位置的完整类型也已实际构造。
[dcp 与规则 (7)](YesMetaZFC/SetTheory/LargeCardinal/TypeGameReply.lean) 已接通原语法投影、严格秩界和加二最大序数查询；后继高度刚性只需 ZF。[武丁重置工厂](YesMetaZFC/SetTheory/LargeCardinal/WoodinGameReset.lean) 自动产生任意参数域下界以上、dcp 弹性的实际重置类型。
[完整辅助闭博弈](YesMetaZFC/SetTheory/LargeCardinal/TypeGame.lean) 已装配原七条规则、全部内部有限历史、固定三阶段时序和策略空间。三张编码表在开局前实际构造，裸类型只检查既定查询的字面成员性；已证明首次违规者输、无限合法对局由 I 获胜及收益集闭。[闭博弈决定性](YesMetaZFC/SetTheory/Descriptive/ClosedDeterminacy.lean) 已按 Neeman 4.16 的获胜局面集合证明，并在[类型博弈](YesMetaZFC/SetTheory/LargeCardinal/TypeGameDeterminacy.lean) 中给出某一方的实际获胜策略；5.15 将辅助博弈中 II 的获胜策略经迭代转成原博弈中 II 的获胜策略，这一转移仍待完成。

## 描述集合论基础

[Descriptive](YesMetaZFC/SetTheory/Descriptive.lean) 在任意 ZF 模型内构造 Baire、Cantor
空间及其拓扑，包含非标准有限前缀、无限延拓、实际可数开闭基、Hausdorff 分离和无孤立点。
Cantor 是 Baire 的闭且无处稠密子空间，并与内部自然数幂集等势。规范有理数码的前缀
超度量已实际构造，两空间内部完备；Cantor 紧致，Baire 有具体的无有限子覆盖开覆盖。
内部前缀树、分支与树体已实现；闭集与树体双向等价，规范前缀树唯一，这部分只需 KP。
在内部 Baire 空间上，该规范树没有死节点。
[Borel 码](YesMetaZFC/SetTheory/Descriptive/Borel.lean) 使用内部良基的带标签前缀树，
已构造唯一求值与解释集合、基本柱集码、补码和内部可数并码，并证明开集与闭树体有码。
码的拼接输出唯一；原公式支持模型内部化及既有相对化接口，同一码可限制到内部子空间。
以上构造不超过 ZF，不增添选择公理；可数并的输入是内部码族。
[解析层](YesMetaZFC/SetTheory/Descriptive/Analytic.lean) 按 Borel 关系的内部 Baire
投影定义，支持唯一解释、有实际码族的可数并、余解析补族的可数交和闭树投影。
解析集的闭集／闭树投影正规形已完成：Borel 求值先转为闭证书，再合并实数见证。
直接接口给出“存在内部实数、每个内部长度都有树内前缀”的双向判据及子空间相对版本。
[射影层](YesMetaZFC/SetTheory/Descriptive/Projective.lean) 沿模型自身的 ω 构造
Σ¹ₙ、Π¹ₙ、Δ¹ₙ，已证明零层／第一层对应、后继投影方程、补对偶、单调性及 Δ¹₁=Borel。
单个射影码和全部层次图都有唯一实际解释；Cantor 点类由内部子空间迹给出。
各内部层的补、交替量词、同极性量词合并、升层、连续逆像及二元并交码已完成。
Σ、Π、Δ 的同层可数并交接收实际内部码族；一般情形只要求实数可数选择，
更弱接口只要求当前指标集上的选择，有限布尔运算仍只用 ZF。
标准数码处已证明与相应有限个交替实数量词的 Borel 正规形一致，并保留子空间相对化。
不交解析集的 Borel 分离码、Suslin 定理、通用闭集及各正射影层的通用集均已构造。
对角法给出每个正内部层的 Σ\Π、Π\Σ 见证；Σ、Π 每个后继层严格增长，Δ 从第一层
以后严格增长，Δ₀=Δ₁=Borel。证明只需 ZF，内部层号允许非标准。
解析子空间上的相对 Suslin 定理也已接入，同一相对集合的 Σ¹₁、Π¹₁ 两码可转为 Borel 码。
[Borel 秩](YesMetaZFC/SetTheory/Descriptive/BorelRank.lean) 已区分码树根秩与集合的
标准秩：Σ⁰₁／Π⁰₁ 对应开／闭，Σ⁰₂ 对应 Fσ，高层满足通常的内部超限递归。
有码集合有唯一内部可数标准秩，补集保秩，任意内部子空间的限制不增秩。
[完美集定理](YesMetaZFC/SetTheory/Descriptive/Perfect.lean) 已证明内部解析集及
有码 Borel 集可数，或含实际非空、闭且无孤立点的子集。两类秩及完美集证明
均只用 ZF，允许非标准 ω 和外部非良基模型，不假设可数选择或 ω₁ 正则。
ZF 中未把无统一码族的集合式 Borel 类与有码类等同。闭博弈决定性已在 ZFC 中证明；
一般统一化与 Borel 决定性尚未实现。

## 算术理论

独立算术子库提供 Q、PA、Z₂ 的公理模式与推导、内部有限编码，以及逐程序原始递归的
表示和可证总性。入口为 `YesMetaZFC.Logic.Arithmetic`、`YesMetaZFC.Model.Arithmetic`；
模型配对与反配对采用关系接口，允许命题内经典证明，但不以选择公理构造模型数据。
精确接口、理论边界和来源见 [算术子库](markdown/ARITHMETIC_STATUS.md)。

## 环境与构建

工具链固定为 **Lean 4.33.1**，见 [lean-toolchain](lean-toolchain)。在项目根目录运行：

```bash
lake --wfail build
bash scripts/check-all.sh
```

全源脚本需要 Python 3.11 或以上，覆盖默认入口未导入的独立模块，
warning 会使检查失败。工具链恢复见 [RESTORE.md](markdown/RESTORE.md)。
默认检查全部 Lean 模块；另需原生对象及库时，运行 `bash scripts/check-all.sh --native`。
模型接口及可信依赖见 [model](YesMetaZFC/Model/README.md)；通用入口为 `import YesMetaZFC.Model`，具体入口为 `import YesMetaZFC.Model.SmallGraph` 和 `import YesMetaZFC.Model.Boolean`。

## 获取构建缓存

安装工具链后，在对应提交运行 `python scripts/lean_cache.py get` 获取编辑和证明开发所需缓存；
使用 `python scripts/lean_cache.py get --kind full` 可同时获取原生对象和库。
CI 为 Linux、Windows、Intel Mac 和 Apple Silicon Mac 构建独立缓存，完成后按提交发布。
平台范围、离线恢复和发布条件见 [CACHE.md](markdown/CACHE.md)。

## 基础设施导航

除各级 README 外，仓库文档统一保存在 [markdown/](markdown/)。

| 要做的工作 | 入口 |
| --- | --- |
| 找到终局定理与准确的数学结论 | [TROPHIES.md](markdown/TROPHIES.md) |
| 使用 J/L、OD/HOD、可容许递归与弱齐性比较 | [内模型进度与接口](YesMetaZFC/SetTheory/InnerModel/README.md) |
| 复用替换、内部反射、固定点、纯语言传输与自动化证明 | [ENGINEERING.md](markdown/ENGINEERING.md) |
| 使用自然数证明证书、源 quotation、纯公式自身编码与整树检查器 | [NAT_DECODING.md](markdown/NAT_DECODING.md) |
| 使用纯定义、内部递归、阶段扩张和原规格 | [ELIMINATION.md](markdown/ELIMINATION.md) |
| 查 119 条公理证明、元数学终点、模型对应及可信依赖核验 | [UNIFIED_VERIFICATION.md](markdown/UNIFIED_VERIFICATION.md) |
| 修改源码时的约束和命名 | [AGENTS.md](markdown/AGENTS.md)、[ProofNaming.md](markdown/ProofNaming.md) |

文档按接口职责维护；完成的计划不再逐轮追加，过程记录可从 Git 历史查看。
公共证明复用、规模统计与检查性能的维护方法见 [ENGINEERING.md](markdown/ENGINEERING.md)，
具体工作约束见 [AGENTS.md](markdown/AGENTS.md)。

## 许可证

本项目的原创代码与随附文档采用 [Apache License 2.0](LICENSE)，署名见 [NOTICE](NOTICE)。
第三方材料如有单独声明，仍遵循其原有许可。

轻量证明派生入口为 `YesMetaZFC.Tactic`，包括命题推导、闭合性、理论包含和有限公理基装配。通用搜索证明器已移出主项目，当前模块边界见 [策略说明](markdown/PROVER_SPLIT.md)。
