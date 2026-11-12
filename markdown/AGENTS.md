# YesMetaZFC Agent Notes

## 导航

| 工作 | 先读 |
| --- | --- |
| 环境恢复、规范源码和工具链 | [RESTORE.md](RESTORE.md) |
| 合并重复证明、复用公共接口、定位性能热点 | [ENGINEERING.md](ENGINEERING.md) |
| 通用模型论、可选二阶接口、图模型与布尔值模型路线 | [YesMetaZFC/Model/README.md](../YesMetaZFC/Model/README.md) |
| 当前自然数证书、quotation 与对象表示 | [NAT_DECODING.md](NAT_DECODING.md) |
| 纯定义、阶段扩张与原规格 | [ELIMINATION.md](ELIMINATION.md) |
| 原公理覆盖、模型对应、Rosser／Löb／哥二／Tarski 与可信依赖 | [UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md) |
| 成果入口、命名规范 | [TROPHIES.md](TROPHIES.md)、[ProofNaming.md](ProofNaming.md) |
| Q／PA／Z₂、内部编码、原始递归表示 | [ARITHMETIC_STATUS.md](ARITHMETIC_STATUS.md)、[ARITHMETIC_PLAN.md](ARITHMETIC_PLAN.md) |

本文件只维护长期工作规则。已完成结果、接口边界和核验方法由上表对应文档维护；
不在这里追加逐轮进度、旧构建统计或临时环境记录。

## 工作约束

- 严格按用户指定路线证明，先解决最难部分；没有实质进展时直接报告，
  不用无效 helper、桥接层或旁路实现充当进展。
- 以高复用、可泛化和数学论文式可读性组织证明；优先信息密度高的代码。
  注释使用中文，证明通过后再做一轮人类数学可读性清理。
- 定理只使用所需的最弱数学前提；参数必须有仓库中已实现的真实实例，
  并能形成可自动调用的接口，不引入虚空参数或伪造实例。
- 证明缺口只能用 `sorry` 明示，不用新公理、虚空假设或占位实例隐藏；
  不把含缺口的结果报告为完成。未经用户允许，不新增不可计算构造实例。
- 范式重构按完整模块或层迁移全部调用方，直接移除旧层，不留下兼容转发层。
- 名称优先采用前缀缩写与下划线，局部变量尽量使用单个数学符号；
  层后缀和数学词根见 [ProofNaming.md](ProofNaming.md)。
- 单模块始终少于 2000 行；相对上次提交基点的工作区代码增量不超过 3000 行。
  如确需超出，先向用户说明并论证额外增量的必要性。
- 单模块编译或类型检查超过一分钟时，立即优化检查开销。
  `smoke` 只用于临时测试，不进入长期编译层。
- 当前 LR⊨AD 专项在目标完成前不执行任何 Git 操作，包括只读查询和提交。
  用户已授权整体重构未提交内容；此授权不解除上述 Git 禁令。

## 元数学内核

- 核心使用普通 `Derives`。不把 `Formula.LevelAtMost` 加回 `Formula.IsLogicalAxiom`、
  推导、演绎、全域化或常用逻辑定理主接口，不重启 `BoundedDerives` 主线。
- 文献的级别、表达式长度等有限护栏只进入显式兼容／审计层；`Formula.level` 和
  `mf1_level` 不阻塞核心自动化，不把纸面提纲限制传播到公共 API。
- 区分现有 Skolem 证书的元层选择依赖与对象理论公理，不向对象核心加入 `ε` 公理。
- 精简必须保持公开接口的适用范围、排序、上下文、量词、guard、数据格式和算法行为。
  不通过更强假设、新公理、`sorry`、额外原生计算可信依赖或删除数学内容换取行数。
- 完整 AST quotation 使用 `IntrinsicQuotation`；旧 Hilbert quotation 及其 verifier
  不可直接接入当前表示。有限公理基与原理论是推导等价，不是公理集合逐字相等。
- `RelationalTranslation.derives_sound` 是模型真值结论；正向句法传输使用
  `PureRosser.translate_derives`。不据此宣称一般反向保守性。
- 模型内部 ω 不假定外部标准、有限或良基。内部归纳只应用于实际可分离公式，
  不能将原模型的任意额外谓词直接用于纯分离或归纳。
- 通用模型底座不要求可构造、外部良基或二阶封闭；二阶封闭是可选接口。
  具体模型构造保持预先固定的载体 universe。一致性走 Lean 元层模型及推导可靠性，
  不把 Henkin 强完备性或自然数枚举作为图模型、布尔值模型路线的前置。
- 模型概念使用显式的相对化语义背景，默认采用当前 Lean/Tarski 语义；相对模型性
  不自动反射为外部模型性。相对化的域、等同、量词和二阶封闭不强制采用默认实例的解释。
- 预留背景内部语法与证明码的可选视角，默认仍用当前 AST 与推导核；不要求内部码
  外部标准或可全部解码为 Lean 语法，也不把内部可证性直接提升为外部 `Derives`。
- 现有模型论语义、解释、模型构造和对应证明统一位于 `YesMetaZFC/Model/`，模块入口
  使用 `YesMetaZFC.Model.*`；数学声明保留其既有命名空间，旧模块路径不留转发层。
- 通用相对接口复用 `Model.Semantics`：`Sem_context`／`Sem_background` 与符号解释
  `Sem_model` 分开；求值代数不能自动导出可靠性。`Sem_rules` 的 Native／Ast 模型
  实例已有完整六规则证书。默认模型性与原接口的
  对应见 `Native.models_iff`，一致性直接用 `Native.consistent`。
- 项保持分别使用 `Tm_map`、`Tm_substitution` 与原生 `Fn_map` 的最弱接口。
  `LevyEmbedding` 已扩展 `Str_emb`，不要把有界见证回拉重新放进普通项求值定理。
- `Proof_view.has_proof` 是给出被接受码的外部存在性，不等于背景内部存在量词；
  标准码的反向读取只在 `Ast.has_proof_iff` 的默认实例中已证明。
- `Predicate_domain.Full` 相对于所选谓词域，不自动意味着外部幂集。
  默认同层二阶实例及逐公式对应见 `SecondOrder.Full.structure_of`、`satisfies_iff`。
- 异质值列与有限赋值转换分别复用 `Model.Values`、`Model.FirstOrder.Valuation`；
  后者保留原消费者的数学命名空间，但已对任意签名 universe 实现，勿另写零层副本。

## 证明与架构习惯

- 参数列骨架复用 `Arguments.listRec`；项和参数列性质优先相互结构递归。
  Hilbert 编译像复用 `Formula.hilbertize_induction`；槽位替换、存在见证块、
  Quine shape、有限轨迹、已检查证明行和环境传输按 ENGINEERING 指路表消费。
- 不按元数复制 binder 展开，不重复维护 `*_of_depth` 已覆盖的递归。
  shape 合同不能代替 scope 和总码域；行表公共装配不能省略实际逻辑行条件。
- 机械 Hilbert 步骤优先复用 `YesMetaZFC.Tactic` 中的 `derive_prop` 等轻量策略；
  数学构造和存在唯一性直接调用已有接口。通用搜索证明器已移出主项目，
  不重新引入其调度、注册属性、证书运行时或兼容转发层。
- 对象编码、反射、固定点等数学模块位于 `Logic.FirstOrder.FormalSystem.Arithmetic`；
  数学声明保留既有命名空间，旧 Automation 模块路径已迁移。
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

## 验证

- 正常构建使用 `lake build`；`lake env` 不会自动构建依赖。
  稳定节点用 `lake --wfail build` 和 `python scripts/lean_cache.py build` 检查全部独立模块。
- 不仅凭默认导入图不可达删除数学模块。全源脚本继续枚举每个独立模块；
  原生验证使用 `python scripts/lean_cache.py build --native`。
- 已由通用定理证明的性质使用正常内核构建验证，不维护枚举样本、`#eval` 回归
  或仅重复调用定理的 `example` 模块；保留有独立数学内容的规格和正负表示证明。
- 不恢复常开的 `simp.rewrite` 追踪；性能问题先作声明级测量。
  构建和审计证据只标记实际核验过的源码基点，文档减量不计入代码净减量。
- 算术切片允许 `Prop` 内经典证明，但不得借选择产生 `Type` 层模型数或函数。
  使用图关系及存在唯一性接口，不添加 `noncomputable`；验证运行
  `python scripts/test_arithmetic_guard.py` 和 `python scripts/check_arithmetic.py`。
  不把证明公理列表中的 `Classical.choice` 一概误判为数据选择，也不据此宣称 ZF 内解释已完成。

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

## 源码与文档维护

- 以当前 Git 工作区、`lean-toolchain` 和实际构建配置为准；环境恢复见 [RESTORE.md](RESTORE.md)。
  开始前检查已有未提交改动，不以旧归档或远端快照覆盖当前工作。
- 文档记录当前接口、数学边界和可复跑命令；完成的计划改为接口导航，
  过程日志交由 Git 历史保存。来源署名和必要的审计基点保留。
- 构建结果只对实际核验的源码有效；报告须说明未完成项，不沿用旧日志宣称本次通过。
- 临时日志、探针、兼容 shim、备份、运行时和编译缓存不进入源码交付。
- 遇到来源不明的文件或版本冲突时保留用户工作并说明阻碍。
