import YesMetaZFC.Model.Interpretation.RelationalDefinitions
import YesMetaZFC.Model.Interpretation.SemanticTransfer
import YesMetaZFC.Model.Interpretation.TotalizedGraph
import YesMetaZFC.Model.Interpretation.RelationalExpansion
import YesMetaZFC.Automation.CoreSyntax
import YesMetaZFC.Automation.CoreNormalForm
import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaSoundness
import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaTraceSoundness
import YesMetaZFC.Automation.CoreNormalForm.FoolTraceSoundness
import YesMetaZFC.Automation.LazyDefinitionRegistry
import YesMetaZFC.Automation.SourcePreprocessing
import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Automation.DAGCertificate
import YesMetaZFC.Automation.DenseDAG
import YesMetaZFC.Automation.HODAGCertificate
import YesMetaZFC.Automation.HOAvatar
import YesMetaZFC.Automation.HOAvatarSoundness
import YesMetaZFC.Automation.HOExtensionalWitnessRegistry
import YesMetaZFC.Automation.HOExtensionalWitnessSoundness
import YesMetaZFC.Automation.SearchMaterialization
import YesMetaZFC.Automation.SearchReplayMaterial
import YesMetaZFC.Automation.HOSearchMaterialization
import YesMetaZFC.Automation.HOSearch
import YesMetaZFC.Automation.CoreNormalForm.HigherOrderProjectionSoundness
import YesMetaZFC.Automation.HORefutationProvider
import YesMetaZFC.Automation.AvatarSplit
import YesMetaZFC.Automation.Avatar
import YesMetaZFC.Automation.DAGCertificate.AvatarRegistry
import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay
import YesMetaZFC.Automation.Data
import YesMetaZFC.Automation.Resolution
import YesMetaZFC.Automation.Resolution.CertificateSlice
import YesMetaZFC.Automation.PropCdcl
import YesMetaZFC.Automation.LogicSoundness
import YesMetaZFC.Automation.Scheduler
import YesMetaZFC.Automation.Completeness
import YesMetaZFC.Automation.Syntax
import YesMetaZFC.Automation.HostReification
import YesMetaZFC.Automation.Request
import YesMetaZFC.Automation.HostNormalization
import YesMetaZFC.Automation.HostNormalization.RuleRegistry
import YesMetaZFC.Automation.HostNormalization.RuleCompiler
import YesMetaZFC.Automation.HostNormalization.RestrictedSuperposition
import YesMetaZFC.Automation.HostNormalization.EqualityClosure
import YesMetaZFC.Automation.HostNormalization.CheckedReplay
import YesMetaZFC.Automation.HostNormalization.CheckedTransaction
import YesMetaZFC.Automation.FirstOrderDerives
import YesMetaZFC.Automation.DerivesClosure
import YesMetaZFC.Automation.HostProp
import YesMetaZFC.Automation.HostRules.Registry
import YesMetaZFC.Automation.HostRules.Frontend
import YesMetaZFC.Automation.HostRules.Backend
import YesMetaZFC.Automation.HostFirstOrder
import YesMetaZFC.Automation.HostHigherOrder
import YesMetaZFC.Automation.HostAvatar.Dispatch
/-!
# 自动化聚合入口
这是后 MF1 阶段的自动化稳定入口。它只导出已经能在新 `Logic` 语义核旁边独立
构建的搜索数据结构、命题/CDCL 基础设施和新 soundness 合同。
`Automation.CoreSyntax` 放置 FOOL / lambda 友好的局部无名核心语法和搜索层 clause AST。
`Automation.CoreNormalForm` 放置 beta / FOOL / connective normal form 和可复算 payload。
`Automation.CoreNormalForm.FoolTraceSoundness` 给出只依赖 `FoolContract` 的
FOOL-only trace replay；原生 `apply/lam` 才进入联合 FOOL/lambda soundness。
`Automation.LazyDefinitionRegistry` 把 checked definitional CNF 的定义谓词双向对齐到
canonical source slots，供 saturation 按需开放 fold/unfold 字句。
`Automation.SourcePreprocessing` 是 source normalization / anti-prenex / local Skolem /
definitional CNF 的唯一公开入口；默认 provider 对严格一阶字句运行 AVATAR/CDCL，
对保留原生 `apply/lam` 的字句运行 HO-AVATAR saturation/CDCL 双核。
`Automation.Data` 放置 ATP 搜索期复用的 packed handle、arena、bitset、sparse set/map、
heap、watch table、signature 和 intern table；它不依赖对象逻辑或 LCF replay。
`Automation.Certificate` / `Automation.Resolution` / `Automation.PropCdcl` 放置可计算的
命题残差证书检查与基础 resolution/CDCL 搜索结构。
`Automation.DAGCertificate` 放置零层级的大型 DAG 证书底座，统一 source / local /
theory-conflict / residual 节点形状。
`Automation.SearchMaterialization` 放置轻量 search-DAG 到新大型 DAG 的材料化入口。
`Automation.SearchReplayMaterial` 在同一拓扑循环中生成富 DAG 与连续 Arena。
`Automation.HODAGCertificate` / `Automation.HOSearchMaterialization` 放置原生高阶
`apply/lam` 子句检查边界与搜索材料化入口。
`Automation.HOAvatar` 放置 persistent HO saturation/CDCL `TheoryResponse` 协调器。
`Automation.HOAvatarSoundness` 放置 HO component 的 typed 支持与 split 覆盖语义合同。
`Automation.HOExtensionalWitnessRegistry` 从 checked HO-DAG 抽取并全局检查显式
`diff` 见证的类型、来源、新鲜性与唯一性。
`Automation.HOExtensionalWitnessSoundness` 提供全部 `diff` 符号的批量模型扩张、
sort 保持、source 解释保持以及 FOOL/lambda 与外延合同保持。
`Automation.HOSearch` 从当前 HO-DAG 自动生成 β/η、同余和外延资源。
`Automation.CoreNormalForm.HigherOrderProjectionSoundness` 与
`Automation.HORefutationProvider` 放置 core-to-HO 语义投影、witness-aware HO 搜索和
checked HO-AVATAR DAG 后端出口。
`Automation.AvatarSplit` 放置搜索层与 DAG checker 共用的 component partition 核心。
`Automation.Avatar` 放置常驻 CDCL 与 guarded first-order saturation 的双核协调器。
AVATAR 数学层统一由 `DAGCertificate.IntrinsicReplay.Avatar` 与
`AvatarSemantics` 提供；旧的空兼容入口已移除。
`Automation.DAGCertificate.AvatarRegistry` 复算 selector registry 的有限结构合同；
`Automation.DAGCertificate.IntrinsicReplay.AvatarSemantics` 在统一 free registry 下提供
component/split 语义，并由 `HostRules` 直接消费 AVATAR 后端出口。
`Automation.LogicSoundness` 放置新 `Logic` 语义核对应的零层级深嵌入 soundness 合同。
`Automation.Completeness` 为实际 `SearchSignature` 建立公平 Henkin 调度，并把
free-closed checked backend success 经强完备性回收到公共 `Derives`。
`Automation.Syntax` 放置直接维护深嵌入 `Logic.Syntax` 对象的构造层。
`Automation.HostReification` 放置多排序、binder-safe 的宿主快照；暂未覆盖的
宿主片段进入 typed opaque 节点，不再让整个目标退出新正规化前端。
`Automation.HostRules.Frontend` 将宿主命题和注册推理规则重化为 proof-carrying
source；`Automation.HostRules.Backend` 只运行公共 AVATAR 并回放 DAG Arena 证书，
不保留 Meta 层 `exact/apply` 闭合旁路。
`Automation.Request` 放置 proof-carrying `GoalRequest`、相继式候选准备和
显式 `CERT/BACKEND/VALID` 请求边界。
`Automation.HostNormalization` 是上下文无关的保守规约核，只负责 β/ι/ζ/投影并
返回普通 Lean `Eq` 证明；它不读取注册规则、不迁移目标/假设，也不调用 provider。
`Automation.HostNormalization.RuleRegistry` 只保存 `prove_auto_norm` 的 proof-free
声明元数据，不再兼任执行器或 simp 扩展。
`Automation.HostNormalization.RuleCompiler` 从 `prove_auto_norm` 独立持久注册表编译
不携带证明项的 Eq/Iff/definition 规则面，供后续等式闭包、叠加正规化和证书回放共享。
`Automation.HostNormalization.RestrictedSuperposition` 用四阶段 discrimination tree 与
定义根索引生成单位 demodulation 候选；索引只负责剪枝，规则成立性仍交给 Lean 回放。
`Automation.HostNormalization.EqualityClosure` 一次性准备稳定规则、受限索引和逐规则
`SimpTheorems`，再按显式候选运行 congruence-aware phase-simp 固定点；每条边由 Lean
产生普通等式证明，最终沿父边回放，不信任搜索图本身。
`Automation.HostNormalization.CheckedReplay` 把闭包结果压缩为 proof-free payload，执行
实际使用声明覆盖、路径拓扑、固定点统计、宿主快照和 Lean 逐边 replay；只有通过后
才生成公共证书节点。
`Automation.HostNormalization.CheckedTransaction` 复用一次 prepared 规则面，把 checked
等式回放通过 `replaceLocalDecl` / `replaceTargetEq` 应用到安全假设和真实目标；任一
固定点、证明或 FVar 不变量失败时整笔回滚，不调用旧正规化器或静默 fallback。
`Automation.FirstOrderDerives` 把 `Derives T Γ φ` 内部的命题模式重化为 FOOL 风格
布尔骨架：未知公式参数保持为原子；纯命题目标先隔离理论事实，经典析取使用排中律
分支和循环剪枝；非空理论中的全称事实优先按目标变量直接实例化，仅在失败后运行
带事实预算的兼容饱和。闭合后直接组合对象语言 `Derives` 构造子，不经过强完备性，
也不向原始公式附加良构性前提。
用户入口 `derive_prop` 只消费局部推导事实；`derive_prop_theory` 额外允许读取并实例化
背景理论，但二者都不会回退到宿主相继式或 provider。
`Automation.DerivesClosure` 提供 `derive_close`，按目标外层 sort 重放有限次全域化；
非空理论只消费显式注册的闭公式证明，纯逻辑开放定理则先闭包再结构弱化。
`Automation.HostProp` 放置普通 Lean `Prop` 的命题骨架重化、显式 `USE` 资源入口和
未来原生 FO/HO term 重化所需的 atom 能力分类。
`Automation.HostHigherOrder` 放置单基础域宿主简单类型、原生 `apply/lam` 快照及
到公共 core/HO checker 的直接投影；checked provider 与模型桥保持独立。
自动化验收直接使用生产定理，不在正式编译图中维护专用回归或 benchmark 模块。
旧 `Core` / `FormulaExpr` / `LCF` / 旧 request 路线已经从仓库移除。
-/
