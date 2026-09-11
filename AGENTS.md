# YesMetaZFC Agent Notes

## 导航

| 工作 | 先读 |
| --- | --- |
| 环境恢复、规范源码和工具链 | [RESTORE.md](RESTORE.md) |
| 合并重复证明、复用公共接口、定位性能热点 | [ENGINEERING.md](ENGINEERING.md) |
| 当前自然数证书、quotation 与对象表示 | [NAT_DECODING.md](NAT_DECODING.md) |
| 纯定义、阶段扩张与原规格 | [ELIMINATION.md](ELIMINATION.md) |
| 原公理覆盖、模型对应、Rosser／Löb／哥二／Tarski 与可信依赖 | [UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md) |
| 成果入口、命名规范 | [TROPHIES.md](TROPHIES.md)、[ProofNaming.md](ProofNaming.md) |

裸 ZFC Rosser 实例已经完成：`PureRosser.agreement` 有实际证明，
`PureRosser.independent` 仅假定裸 ZFC 一致。相关重构必须保留这一终点、
源句子、签名、公理、quotation 与既定可信基；进入对应层时先读上表的使用边界。
本文件维护长期规范，完成的计划改写为接口导航，不追加逐轮日志。
`PureProvability` 已在裸 ZFC 中完成原编码表示的 D1–D3、Löb 与哥二；
纯句子的双向推导及源句子往返所需的对应条件见 `PureSentenceTransfer` 和上述指南。
`ReducedTarski` 已完成原支撑理论的无参数真值不可定义性；`ReducedTarski.Parameters`
进一步排除每组任意有限参数下的开放公式真值定义。实际 liar 构造复用
`ObjectDiagonal` 的原自代入图。`PureTarskiSource` 已把保留原编码的带参数实例落到裸 ZFC；
候选和反例均为纯公式，真值合同按源公式索引。`PureQuotation`、`PureFixedPoint` 和
`PureTarski` 另已完成最终纯公式自身完整 AST 编码、带参数固定点及裸 ZFC 真不可定义性。
开放公式的环境往返和双向推导见 `PureOpenTransfer`，精确边界见成果表和编码指南。

## 元数学内核

- 核心使用普通 `Derives`。不把 `Formula.LevelAtMost` 加回 `Formula.IsLogicalAxiom`、
  推导、演绎、全域化或常用逻辑定理主接口，不重启 `BoundedDerives` 主线。
- 文献的级别、表达式长度等有限护栏只进入显式兼容／审计层；`Formula.level` 和
  `mf1_level` 不阻塞核心自动化，不把纸面提纲限制传播到公共 API。
- Skolem 选择使用 Lean 元层 `Classical.choice` / `Classical.choose` 的证书构造，
  不向对象核心加入 `ε` 公理。
- 精简必须保持公开接口的适用范围、排序、上下文、量词、guard、数据格式和算法行为。
  不通过更强假设、新公理、`sorry`、额外原生计算可信依赖或删除数学内容换取行数。
- 完整 AST quotation 使用 `IntrinsicQuotation`；旧 Hilbert quotation 及其 verifier
  不可直接接入当前表示。有限公理基与原理论是推导等价，不是公理集合逐字相等。
- `RelationalTranslation.derives_sound` 是模型真值结论；正向句法传输使用
  `PureRosser.translate_derives`。不据此宣称一般反向保守性。
- 模型内部 ω 不假定外部标准、有限或良基。内部归纳只应用于实际可分离公式，
  不能将原模型的任意额外谓词直接用于纯分离或归纳。

## 证明与架构习惯

- 参数列骨架复用 `Arguments.listRec`；项和参数列性质优先相互结构递归。
  Hilbert 编译像复用 `Formula.hilbertize_induction`；槽位替换、存在见证块、
  Quine shape、有限轨迹、已检查证明行和环境传输按 ENGINEERING 指路表消费。
- 不按元数复制 binder 展开，不重复维护 `*_of_depth` 已覆盖的递归。
  shape 合同不能代替 scope 和总码域；行表公共装配不能省略实际逻辑行条件。
- 机械 Hilbert 步骤优先改进或复用 tactic。新章节使用 `prove_auto`，不继续使用
  旧 `mf1_fo_core`。通用证明器、预处理和调度放在 `YesMetaZFC.Automation`，
  领域目录只保留领域合同。
- 自动化共用 `Certificate` / `DAGCertificate`，新后端优先映射 checked payload
  到公共 DAG 节点。CoreNormalForm / SourcePreprocessing 提供一阶公共前端，
  Scheduler 组织预处理、Superposition 与 CDCL residual。
- 扩张复合保留新鲜变量、函数界的单调性以及类型与环境条件。FOOL guard、高阶 λ
  同余和 HO bound stack 约束不得在公共化时省略。
- 大模型跨阶段比较复用 `RelationalCongruence.openFormula_congr`、
  `RelationalTransfer`、`RelationalInheritance` 和 `ModelClosure`；
  用 `CoveredExtension.trans` 组合覆盖与旧图保持，不逐层重抄参数映射和规格包装；
  不通过展开整个选择模型或不动点完成定义相等转换。
- 原正文形状与递归参数保持先在抽象源模型证明，再用 `PredicateCongruence`
  接入实际解释。多变量算子优先直接 `existsE` 块与模板接口。
- `PureNaturalInduction.source_induction` 固定早期 `PureDifferenceStage`；
  涉及较新函数时，对最新解释的 `openFormula` 使用 `pure_induction`，再传回源语义。
- 大公式先对公式参数证明联结词保持，再代入实际句子。quotation 外层形状使用
  `ObjectDiagonal.fixedPoint_shape`，码域使用已有接口，不展开巨大一元数码。
- 大模型等式替换先固定参数和目标类型；例如 `PureSyntaxFixedPoint.tag_injective`
  使用 `congrArg (membership ℳ input)`。布尔覆盖可用 `decide +kernel`。
- 注释使用中文。证明通过后清理人类数学可读性；接口迁移按完整模块或层完成，
  同步命名参数调用，不保留旧变量名兼容层。

## 验证

- 正常构建使用 `lake build`；稳定节点用 `lake --wfail build` 和
  `bash scripts/check-all.sh` 检查全部独立模块及扫描工具。
- 不仅凭默认导入图不可达删除模块；`ProveAutoBranchProbe` 由扫描器动态导入。
  `prove_auto_sweep` 仅静态导入 `Automation.HostAvatar.Dispatch`，完整库运行时加载，
  不改回静态导入根模块。工具依赖变化后检查 `--help` 与一次实际目标扫描。
- 已由通用定理证明的性质使用正常内核构建验证，不维护枚举样本、`#eval` 回归
  或仅重复调用定理的 `example` 模块；保留有独立数学内容的规格和正负表示证明。
- 不恢复常开的 `simp.rewrite` 追踪；性能问题先作声明级测量。
  构建和审计证据只标记实际核验过的源码基点，文档减量不计入代码净减量。

## 集合论接口符号约定

- `ℒ` 固定表示纯集合论语言 `SetTheory.PureSetLanguage`，不要把它复用为任意语言变量。
- `ℳ` 表示当前主要结构，`𝒩` 表示第二个或目标结构，`𝒱` 只用于具有 ambient universe
  角色的结构。
- `𝒞` 表示 `OrderedPairConvention`，`𝕀` 表示 `𝒞.Interpretation ℳ`；多结构场景使用
  `𝕀ₘ`、`𝕀ₙ`。
- `α β γ δ ξ η θ` 默认表示序数，`ω` 默认表示满足 `ℳ.IsOmega` 的最小超限序数，
  `κ λ μ` 预留给基数；这些数学性质仍必须由 `hα`、`hω`、`hκ` 等显式假设给出。
- `Ord` 只在文献和注释中表示全体序数组成的类。Lean 接口使用 `ℳ.IsOrdinal`；
  不声明裸 `Ord` 常量，以免与 Lean 核心的 `Ord` 类型类冲突。
- `Γ Δ` 表示理论或上下文，`φ ψ χ` 表示公式，`s t u` 表示项，`F G H` 表示类函数、
  schema 或递归算子。
- 单结构理论假设使用 `hZF`、`hKP`、`hZFC`；多结构场景使用 `hℳZF`、`h𝒩ZF`。
- 结构和可推断的依赖参数默认隐式；有序对解释及模型公理证明默认显式。若 `𝒞`
  不出现在返回类型中，仍应显式传入，避免留下无法推断的 metavariable。
- 不把结构、模型公理、有序对解释、`IsOmega` 或未来的 `IsCardinal` 做成 typeclass，
  也不通过 `Classical.choose` 固定全局模型相关的 `ω`。
- 接口迁移按完整模块或完整层进行，同时更新命名参数调用；不保留旧变量名兼容层。

## 稳定源码与文件维护

- 恢复地址和工具链校验和以 RESTORE 为准。Drive 二进制运行时在根目录，
  不因源码目录或全文搜索无结果就断言不存在。
- 更新规范源码包时保持同一 Drive 文件身份；报告更新保持各自身份和版本历史。
  不创建按日期、轮次、版本号命名的平行包，不以早期来源包覆盖当前工作。
- 源码修改在工作区进行。回写稳定源码前确认正常构建及相关独立模块通过，
  没有新引入未说明的 `sorry`、`admit` 或自定义公理，并更新必要文档。
- 源码包只含源码、配置和文档；排除 `.lake/`、运行时、编译产物、缓存、
  临时日志、探针、兼容 shim、备份和旧压缩包。一次性分析留在 scratch。
- 无法确认原文件、遇到版本冲突或缺少替换权限时保留当前工作并说明阻碍，
  不以另存平行文件绕过。不删除或覆盖来源不明的用户文件；其他历史文件的
  删除需要明确授权。
