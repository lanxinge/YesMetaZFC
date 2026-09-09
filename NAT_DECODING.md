# 自然数证书与对象表示指路表

## 可计算入口

[ZFC/NatEncode](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/NatEncode.lean)、[ZFC/NatDecode](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/NatDecode.lean) 提供原 `intrinsic_zfc_theory` 上的实际入口：

```lean
intrinsic_zfc_nat_encode : IntrinsicClosedProofCertificate → Nat
intrinsic_zfc_nat_decode : Nat → Option IntrinsicClosedProofCertificate
intrinsic_zfc_nat_check : Nat → SetSentence → Bool
```

| 需要的保证 | 公共声明 |
| --- | --- |
| 接受的闭句有普通推导 | `intrinsic_zfc_nat_check_sound` |
| 恢复整个实际证书 | `intrinsic_zfc_nat_decode_encode` |
| 编码单射 | `intrinsic_zfc_nat_encode_injective` |
| 可推导当且仅当存在被接受的自然数证书 | `intrinsic_zfc_derives_iff_nat_certificate` |

解码保存实际结论和类型正确的证书，覆盖六条核规则。编码沿证书递归，不通过
经典选择从可证性命题抽取证书；检查器不从输入接收理论成员证明。
`none` 只表示该输入不是此格式的合法闭证明，不能推出目标闭句不可证。

## quotation 与公理基

| 需要的接口 | 源码 | 边界 |
| --- | --- | --- |
| 保留完整 AST 的 quotation | [IntrinsicQuotation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/IntrinsicQuotation.lean) 的 `quote`、`unquote_quote`、`quote_injective`、`quote_ne`；[IntrinsicQuotationEvaluation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/IntrinsicQuotationEvaluation.lean) 的 `quote_evaluate` | 十一种公式构造子均保留；使用紧凑树项 |
| 完整公式的实际识别与解码 | [ObjectFormulaSound](YesMetaZFC/Automation/ObjectFormulaSound.lean) 中 `ObjectFormulaSyntax.checked_decode` | 覆盖所有自然数输入，包括失败分支 |
| 当前四种类型化变换、逻辑公理和证明规则 | [ObjectSyntaxTransform](YesMetaZFC/Automation/ObjectSyntaxTransform.lean)、[ObjectLogicalAxiom](YesMetaZFC/Automation/ObjectLogicalAxiom.lean)、[ObjectProofNode](YesMetaZFC/Automation/ObjectProofNode.lean) | 分别连接实际核变换、27 类逻辑公理和六条核规则 |
| 八个固定 ZFC 公理与两个模式 | [BaseAxiomPacketSpec](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/BaseAxiomPacketSpec.lean) 的 `BaseAxiomPacket.presentation` | 精确表示原基础公理像；替换作为派生模式接口存在，不额外加入原证书分支 |
| 与原理论推导等价的完整公理基 | [ReducedAxiomPacket](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedAxiomPacket.lean) 的 `presentation`；[ReducedAxioms](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedAxioms.lean) 的 `derives_iff` | 原 ZFC 像加 119 条有限基；不宣称原无限参数公理成员关系逐值相同 |
| 带上下文与实际结论标注的证明树 | [ProofTreeCode](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ProofTreeCode.lean)、[ReducedProofTree](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofTree.lean) 的 `derives_iff` | 全部六条规则的真实检查器、可靠性与完备性 |
| 固定局部测试到整树对象表示 | [ReducedProofPresentation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedProofPresentation.lean) 的 `nodeTest`、`presentation`；[ObjectProofNode](YesMetaZFC/Automation/ObjectProofNode.lean) 的 `ofNodeTest` | 要求局部可靠性和全部实际编码的接受完备性，不要求非规范外壳与旧算法逐值相等 |
| 内部自然数码域与 Rosser 装配 | [ReducedNaturalProofPresentation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedNaturalProofPresentation.lean)、[ReducedRosser](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/ReducedRosser.lean)、[PureRosserComplete](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean) | 当前实例已完成裸 ZFC 支撑消去及任意原模型对应；精确终点见 [UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md) |

旧 `QuineEncoding.quote` 先 Hilbert 化，会合并不同实际 AST；
[SchemaQuotationAudit](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaQuotationAudit.lean) 给出分离、收集模式的实际冲突。旧 `IntrinsicVerifier`、
`IntrinsicSchemaCertificate`、`IntrinsicGraph` 的 Hilbert 格式不能直接充当当前表示。
`ReducedRosser` 只从旧层复用 quotation 无关的 core 与数码成员事实。

## 模式表示的公共接口

下表的正负表示使用普通 `Derives`；拒绝结论覆盖任意错误候选输出及对象界内见证，
不只覆盖宿主已经解码的数据。这里的 Δ₀ 分类相对于扩展支撑语言。

| 调用方要连接的步骤 | 实际接口与源码 | 保留的义务 |
| --- | --- | --- |
| 标签、元数、参数叶子 | [SchemaEnvelope](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaEnvelope.lean) | 原分离／收集解码器的完整外壳 |
| 正文项与变量作用域 | [SchemaTerm](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaTerm.lean)、[SchemaBodyDerives](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaBodyDerives.lean)、[SchemaObjectGraph](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaObjectGraph.lean) 的 `Body.condition` | 实际 Project 项及正文识别的成功／失败 |
| 自然数传输包到原始树 | [NatPacketLink](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/NatPacketLink.lean) | 实际 `NatPacket.decode`，包含非法包和错误候选树 |
| 正文重命名 | [SchemaRenameDerives](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaRenameDerives.lean)、[SchemaObjectGraph](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaObjectGraph.lean) 的 `Rename.condition` | 实际有限表算法，任意错误输出，六个具体位置 |
| 固定模式模板 | [SchemaTemplate](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaTemplate.lean)、[SchemaTemplateDerives](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaTemplateDerives.lean) | 三种模板；槽位装配不自行验证正文或执行对象重命名 |
| 任意长度参数闭合 | [SchemaClosure](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaClosure.lean) | 精确连接实际模式闭句，无固定量词层数上限 |
| 六张重命名表与中间码连接 | [SchemaTable](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaTable.lean)、[SchemaJoinGraph](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaJoinGraph.lean)、[SchemaJoinDerives](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaJoinDerives.lean) | 三张表、三个正文、核心的实际存在连接 |
| Project 树到当前核 quotation | [KernelQuotation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/KernelQuotation.lean)、[SchemaKernelJoin](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaKernelJoin.lean) | 使用正式交换律，不把两种树码直接认作相等 |
| 完整原始包与实际结论 | [SchemaPacketSpec](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaPacketSpec.lean)、[SchemaPacketDerives](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaPacketDerives.lean)、[SchemaConclusion](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SchemaConclusion.lean) | `SchemaPacket.actual_positive_number`、`actual_negative` 与精确目标 AST 比较，覆盖全部输入分支 |

`NatPacket.encode` 是传输编码，`treeValue` 是内部树值，当前公式 quotation 又有
自己的语法含义；只通过上表正式桥梁传输，不能混用。

### 模板与位置规范

`SchemaTemplate` 标签 0、1、2 分别构造分离、收集、替换核心，使用一个、两个、
三个已经重命名的正文槽。`run_isSome` 精确连接正文检查，非法正文不会被装配修复。
参数数为 `n`，下表的 `j` 遍历 `j < n`：

| 正文位置 | 源深度 | 目标深度 | 索引表 |
| --- | --- | --- | --- |
| 分离 | `n+1` | `n+3` | `[0] ++ [j+3]` |
| 收集前件 | `n+2` | `n+3` | `[0,1] ++ [j+3]` |
| 收集像集 | `n+2` | `n+4` | `[0,1] ++ [j+4]` |
| 替换第一输出 | `n+2` | `n+3` | `[1,2] ++ [j+3]` |
| 替换第二输出 | `n+2` | `n+3` | `[0,2] ++ [j+3]` |
| 替换像集 | `n+2` | `n+4` | `[1,0] ++ [j+4]` |

### 原参数公理的兼容接口

[SyntaxCanonical](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SyntaxCanonical.lean)、[SyntaxParameters](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SyntaxParameters.lean) 提供完整类型化项的规范解码和参数列往返。
[SupportParameterDerives](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/SupportParameterDerives.lean) 的 `SupportParameter.positive`、`negative` 识别参数证书
合法性；仅凭项数不能区分相同元数的不同公理结论。

| 公理族 | 原证书中项的顺序 |
| --- | --- |
| domain、range、converse | relation |
| cartesianProduct | left、right |
| composition | first、second |
| identity、inductiveCore | source |
| mappingCollection | source、target |
| indexOrder | sourceRelation、sourceCarrier、targetRelation、targetCarrier |
| powerSetBijection | natural |
| symmetricDifference | left、right |

参数外壳为 `N(0; L(freeCount), spine)`；项链为 `N(0; term, rest)`，末尾 `L(0)`。
项的束缚上下文为空，自由上下文由外壳指定。
[SyntaxSubstitution](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SyntaxSubstitution.lean)、[SyntaxInstantiation](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SyntaxInstantiation.lean) 实现防捕获代入与实际自由变量抽象；
全称闭合不能只在原始树外添加量词。

[SupportRealization](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/SupportRealization.lean) 的 `assemble_eq`、`assemble_quote`、`run_eq_actual`、
`packet_eq_actual` 连接模板、代入、闭合、实际解码结论与内层参数包。
这些是计算层和交换定理，尚不构成原 11 类无限参数公理及全部外层 union 路径的
统一对象表示。该兼容工作不阻塞已完成的有限基路线和裸 ZFC Rosser 实例。

## 版本 1 数据包

宿主传输格式由 `ProofT.NatPacket` 定义，与旧 `ProofCode` 配数格式分别命名。
目前没有声明两者相同，也没有把旧对象图直接用于新格式。

1. 原始有限树为 `Tree.node tag children`，标签与子树数量均为自然数。
2. token 顺序为版本号 `1`，随后先序遍历每个节点的「标签、子树数、各子树」。
3. 每个 token 使用规范 unsigned LEB128：每字节低七位是数值位；最高位表示后续字节。
4. 若字节列为 `b₀,…,bₖ₋₁`，输入自然数为 `Σᵢ bᵢ·256ⁱ + 256ᵏ`。
   最高位字节 `1` 是终止标记。解码必须恰好消费全部数据。

`NatPacket.decode_encode` 已证明任意有限数据树的传输往返；
`NatEncode.tree_roundtrip` 证明全部六条规则的证书往返，二者组合为自然数往返定理。截断、尾随 token、未知版本和非规范 varint 均拒绝。
字节解析按自然数值递减，树 token 解析燃料取自输入长度；语法和证明解码沿有限子树
直接递归。这些递归都没有固定的证明长度或公式级别上限。

下表以 `N(t; x₁,…,xₙ)` 表示节点，以 `L(n) = N(n;)` 表示数值叶子。
这只是本页的数据记法，不是新增对象语言符号。

## 项、公式与替换

上下文为 `L(n)`，表示 `n` 个唯一排序 `SetSort.set`。
函数与关系编号固定为 `SyntaxDecode.functionSymbols`、`relationSymbols` 数组中的零基位置；
当前分别有 76 与 55 个符号。参数数目严格由 `signature` 检查。

| 项 | 树 |
| --- | --- |
| 束缚变量 | `N(0; L(index))` |
| 自由变量 | `N(1; L(index))` |
| 函数应用 | `N(2; L(symbol), argument₁, …)` |

变量索引从上下文头开始，必须小于对应上下文长度。替换参数列为
`N(0; term₁, …)`，长度必须恰好等于源自由上下文长度；各项在目标上下文中解码。

| 公式标签 | 参数 |
| --- | --- |
| 0、1 | 无参数，分别为假、真 |
| 2 | 关系编号叶子及符合签名的项参数列 |
| 3 | 两个项：相等 |
| 4 | 一个公式：否定 |
| 5、6、7、8 | 两个公式：合取、析取、蕴涵、双条件 |
| 9、10 | 一个公式：全称、存在；解析正文时增加一个束缚变量 |

## 公理证书

顶层 `N(0; zfc)` 是 ZFC 公理像，`N(1; support)` 是原支撑公理理论。

ZFC 固定标签 `0,…,7` 依次为外延、空集、配对、并集、幂集、无穷、正则、选择，
均不带参数。`N(8; L(n), body)` 是分离 schema，`N(9; L(n), body)` 是收集 schema。
它们分别在束缚深度 `n+1`、`n+2` 解码，并检查 `FreeClosed`。

Project schema 项仅允许 `N(0; L(index))` 形式的有效束缚变量。
Project 公式标签 `0、1、4,…,10` 与上表一致，`2` 接收两个项表示成员关系，
`3` 接收两个项表示外延相等，`11` 接收两个项表示子集。

支撑公理严格沿 `IntrinsicAxiomCertificate` 的呈现结构解析：

| 呈现 | 证书树 |
| --- | --- |
| `singleton` | `L(0)` |
| `union` 左、右分支 | `N(0; child)`、`N(1; child)` |
| `insert` | 与 `union (singleton …) …` 相同 |
| `indexed` | `N(0; index, child)`；先解析索引，再解析该索引对应的证书 |

参数化分离族的索引依次是自由上下文和该族全部项参数；项均在该上下文中解析。
支撑呈现层均有对应的可计算解码函数，包括嵌套 `insert` 的各固定公理。

## 逻辑公理与推导规则

逻辑公理节点的标签按 `HilbertBaseAxiom` 构造子顺序固定。

| 标签 | 构造子 | 参数 |
| --- | --- | --- |
| 0 | implication_distribution | 三个公式 |
| 1 | self_implication | 一个公式 |
| 2 | weakening | 两个公式 |
| 3 | contradiction | 两个公式 |
| 4 | classical | 一个公式 |
| 5 | explosion | 两个公式 |
| 6 | case_analysis | 两个公式 |
| 7 | truth_intro | 无 |
| 8 | falsum_elimination | 一个公式 |
| 9、10 | negation_intro、negation_elimination | 一个公式 |
| 11 | conjunction_intro | 两个公式 |
| 12、13 | conjunction_elim_left、conjunction_elim_right | 两个公式 |
| 14、15 | disjunction_intro_left、disjunction_intro_right | 两个公式 |
| 16 | disjunction_elimination | 三个公式 |
| 17 | biconditional_intro | 两个公式 |
| 18、19 | biconditional_elim_left、biconditional_elim_right | 两个公式 |
| 20 | forall_specialization | 一个新增束缚变量下的正文、实例项 |
| 21 | forall_distribution | 两个新增自由变量下的公式 |
| 22 | vacuous_forall | 当前自由上下文的公式 |
| 23 | exists_introduction | 一个新增束缚变量下的正文、实例项 |
| 24 | exists_elimination | 新增自由变量下的正文、当前自由上下文的结论 |
| 25 | equality_substitution | 两个项、一个新增束缚变量下的正文 |
| 26 | equality_reflexivity | 一个项 |

证明树在给定自由上下文中递归解析；公开自然数入口从空上下文开始。

| 规则标签 | 参数及检查 |
| --- | --- |
| 0 | 逻辑公理树 |
| 1 | 顶层理论公理证书树 |
| 2 | 前提证明、蕴涵证明；前提结论必须等于蕴涵左端 |
| 3 | 新增一个自由变量下的证明；输出全称一般化 |
| 4 | 当前上下文的目标公式、增大上下文中的证明；后者结论必须等于目标的 `weakenFree` |
| 5 | 源上下文、替换参数列、源上下文的证明；输出统一替换后的结论 |

所有多余或缺失参数、未知标签、非法作用域以及规则连接错误均返回 `none`。
公式连接检查使用已有结构码的可计算相等判定及其单射定理。

## 核验

格式往返、检查器可靠性与完备性、实际解码器一致性和对象正负表示由上述通用定理
保证。执行 `lake --wfail build` 和 `bash scripts/check-all.sh` 检查正式源码；
不另设只重复这些定理的枚举样本模块。入口从
`YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory` 导出。
当前源码核验与既有可信依赖边界统一见 [UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md)。
