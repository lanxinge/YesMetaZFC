import YesMetaZFC.Automation.CoreSyntax
import YesMetaZFC.Automation.CoreNormalForm
import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaSoundness
import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaTraceSoundness
import YesMetaZFC.Automation.CoreNormalForm.FoolDefinitionSoundness
import YesMetaZFC.Automation.LazyDefinitionRegistry
import YesMetaZFC.Automation.SourcePreprocessing
import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Automation.DAGCertificate
import YesMetaZFC.Automation.HODAGCertificate
import YesMetaZFC.Automation.HOAvatar
import YesMetaZFC.Automation.HOAvatarSoundness
import YesMetaZFC.Automation.HOExtensionalWitnessRegistry
import YesMetaZFC.Automation.HOExtensionalWitnessSoundness
import YesMetaZFC.Automation.SearchMaterialization
import YesMetaZFC.Automation.HOSearchMaterialization
import YesMetaZFC.Automation.HOSearch
import YesMetaZFC.Automation.CoreNormalForm.HigherOrderProjectionSoundness
import YesMetaZFC.Automation.HORefutationProvider
import YesMetaZFC.Automation.AvatarSplit
import YesMetaZFC.Automation.Avatar
import YesMetaZFC.Automation.AvatarSoundness
import YesMetaZFC.Automation.AvatarRegistrySoundness
import YesMetaZFC.Automation.Data
import YesMetaZFC.Automation.Resolution
import YesMetaZFC.Automation.PropCdcl
import YesMetaZFC.Automation.LogicSoundness
import YesMetaZFC.Automation.LegacyRemoved
import YesMetaZFC.Automation.Syntax
import YesMetaZFC.Automation.HostReification
import YesMetaZFC.Automation.HostSequent
import YesMetaZFC.Automation.HostPropAnalysis
import YesMetaZFC.Automation.Request
import YesMetaZFC.Automation.HostNormalization
import YesMetaZFC.Automation.HostNormalization.RuleRegistry
import YesMetaZFC.Automation.HostNormalization.RuleCompiler
import YesMetaZFC.Automation.HostNormalization.RestrictedSuperposition
import YesMetaZFC.Automation.HostNormalization.EqualityClosure
import YesMetaZFC.Automation.HostNormalization.CheckedReplay
import YesMetaZFC.Automation.HostNormalization.CheckedTransaction
import YesMetaZFC.Automation.HostFocusedSequent
import YesMetaZFC.Automation.HostProp
import YesMetaZFC.Automation.HostFirstOrder
import YesMetaZFC.Automation.HostHigherOrder

/-!
# 自动化聚合入口

这是后 MF1 阶段的自动化稳定入口。它只导出已经能在新 `Logic` 语义核旁边独立
构建的搜索数据结构、命题/CDCL 基础设施和新 soundness 合同。

`Automation.CoreSyntax` 放置 FOOL / lambda 友好的局部无名核心语法和搜索层 clause AST。
`Automation.CoreNormalForm` 放置 beta / FOOL / connective normal form 和可复算 payload。
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
`Automation.AvatarSoundness` 放置 component/split selector 语义、fixed-bound-stack
整图 soundness 与 residual CDCL 空根 contradiction。
`Automation.AvatarRegistrySoundness` 从 checked DAG 全局构造 selector registry、
valuation 与两类 selector 语义合同，并闭合 AVATAR 主线后端出口。
`Automation.LogicSoundness` 放置新 `Logic` 语义核对应的零层级深嵌入 soundness 合同。
`Automation.LegacyRemoved` 放置已经从类型层和调度层删除的旧 route 审计清单。
`Automation.Syntax` 放置直接维护深嵌入 `Logic.Syntax` 对象的构造层。
`Automation.HostReification` 放置多排序、binder-safe 的宿主快照；暂未覆盖的
宿主片段进入 typed opaque 节点，不再让整个目标退出新正规化前端。
`Automation.HostSequent` 放置宿主相继式公共规则；当前 initial/identity rule 统一消费
局部 proof 资源，不再由各搜索器分别实现 `exact`。
`Automation.HostPropAnalysis` 是搜索核心共享但尚未接入调度的宿主命题反射层；它在
单次会话内缓存命题形状与结构投影，以父 frame 增量索引保存局部资源，并按目标发布
proof-free 需求、候选排序和策略信号。
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
`Automation.HostFocusedSequent` 放置裸 `prove_auto` 唯一的 MetaM 聚焦相继式前端，
覆盖 INTRO/SPLIT/APPLY/CASES/CHOOSE/SPECIALIZE/FORWARD/WITNESS/TRANSPORT 等机械
分解，并把剩余叶子交回 checked 一阶叠加演算或命题 provider。
`Automation.HostProp` 放置普通 Lean `Prop` 的命题骨架重化、显式 `USE` 资源入口和
未来原生 FO/HO term 重化所需的 atom 能力分类。
`Automation.HostHigherOrder` 放置单基础域宿主简单类型、原生 `apply/lam` 快照及
到公共 core/HO checker 的直接投影；checked provider 与模型桥保持独立。

自动化验收直接使用生产定理，不在正式编译图中维护专用回归或 benchmark 模块。

旧 `Core` / `FormulaExpr` / `LCF` / 旧 request 路线已经从仓库移除。
-/
