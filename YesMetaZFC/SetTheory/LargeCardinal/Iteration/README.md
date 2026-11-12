# 迭代树、复制与返回

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [ActivityRead](ActivityRead.lean) | 原关系模型之间的实际扩展器活动边；实际坍塌超幂给出同一条原关系活动边；给定活动系统及其隶属目标读取 |
| [AttemptCoordinates](AttemptCoordinates.lean) | 可枚举原关系图列的实际初等像；移动模型坐标下的同一有限尝试值 |
| [AttemptLift](AttemptLift.lean) | 末结点嵌入确定唯一的联合行图 |
| [AttemptMember](AttemptMember.lean) | 迭代树上的实际模型图与嵌入图；迭代树序和完整初等图列的原公式；整条有限树枝的联合初等尝试；从末结点嵌入实际构造联合尝试节点 |
| [AttemptRank](AttemptRank.lean) | 内部无限尝试链确定共尾树枝；联合枝各行解码为完整初等嵌入；联合尝试枝解码出相容的完整初等嵌入列；失败的返回嵌入产生联合尝试秩 |
| [AttemptRegular](AttemptRegular.lean) | 反例的实际联合尝试树与正则下降秩 |
| [Branch](Branch.lean) | 对象模型内的迭代树序及后继添枝；序数上的实际自反线性迭代序；共尾树枝及其实际指标序 |
| [BranchSchedule](BranchSchedule.lean) | 内部共尾枝序列的 host 读取；内部 ω 的外部可数枚举；外部单调共尾分支序列 |
| [BranchTail](BranchTail.lean) | 树枝的实际直接极限及全部规范初等嵌入；极限投影的规范集合图；共尾多个根图的固定性传到良基极限；回拉图表的子集关系在同一锥中保持 |
| [Coherence](Coherence.lean) | 下降递归的前驱一致性 |
| [CopyAnchor](CopyAnchor.lean) | 原生复制历史中的共同秩段；活动边沿低秩方块搬运档案共同层；档案共同层与工作共同层的识别；共同秩段中的严格极限切片 |
| [CopyCollapseCommon](CopyCollapseCommon.lean) | 同一原后继的塌缩逆图给出完整共同层 |
| [CopyExtend](CopyExtend.lean) | 实际原生复制步装配完整活动历史 |
| [CopyFixedBound](CopyFixedBound.lean) | 固定 nice 树的活动前缀与共同端点；固定 nice 树中本次支撑严格高于真实历史界 |
| [CopyHistory](CopyHistory.lean) | 保留全部前驱和实际超幂的有限复制历史 |
| [CopyNice](CopyNice.lean) | 已实施复制步的原生支撑证据；完整复制树仍为 nice 树 |
| [CopyOriginalPad](CopyOriginalPad.lean) | 原树与复制历史的同步恒等延伸 |
| [CopyOriginalResult](CopyOriginalResult.lean) | 原树实际延长时保留整份旧复制历史；同一次继续与回答的完整两步复制结果 |
| [CopyOriginalStep](CopyOriginalStep.lean) | 共同原秩段搬运完整函数图及精确定义域；原生继续及回答的两步同步复制 |
| [CopyPadding](CopyPadding.lean) | 复制历史的恒等延伸 |
| [CopyPastRound](CopyPastRound.lean) | 原活动支撑确定档案共同层的工作解释；经旧活动共同层施加的已选回合 |
| [CopyQuality](CopyQuality.lean) | nice 树的强度与支撑列编码；同一工作扩展器的所属模型、不可达支撑及最大强度 |
| [CopyRawStep](CopyRawStep.lean) | 指定原生施加证书的自动工作复制 |
| [CopyRoundSyntax](CopyRoundSyntax.lean) | 实际共同层在当前原模型中的有限高度界；原生高度界下的全部旧前驱更新；实际复制历史界的对象语言；已选原回合对实际复制历史的保持 |
| [CopyRow](CopyRow.lean) | 工作共同秩段的实际复制方块；原关系后继到完整工作超幂的一步复制；原关系模型到工作秩段的实际复制行 |
| [CopyStart](CopyStart.lean) | 从实际操作图读取唯一支撑列；给定根嵌入实际生成复制初帧 |
| [CopyTree](CopyTree.lean) | 固定复制因子在实际共同秩层上的交换；固定活动步的有限幂复制交换；实际复制行的规范源与同一活动系统；给定原后继与所属源的共同支撑秩段 |
| [CountableCover](CountableCover.lean) | 原关系 ω 树的公共可数载体 |
| [CountableLimit](CountableLimit.lean) | 可数模型列的实际可数极限与返回因子 |
| [CriticalBound](CriticalBound.lean) | 原关系模型内的统一临界点下界 |
| [CutPull](CutPull.lean) | 同一壳中的正则秩段列与严格下降回拉 |
| [Descent](Descent.lean) | 内部有限下降历史；nice 复制的实际下降一步；原树的严格秩段自动接入下降复制；实际秩段列上的有限下降历史延伸 |
| [Enumeration](Enumeration.lean) | 从公共可数载体实际编号整列模型 |
| [Fork](Fork.lean) | 实际扩展器施加接入迭代树的后继构造；迭代树后继与所属模型超幂之间的一致性；真正分叉的三结点迭代树 |
| [FrameBranch](FrameBranch.lean) | 共尾有限框架的当前节点枝 |
| [FrameStage](FrameStage.lean) | 共尾有限框架中的首次出现阶段 |
| [FrameUnion](FrameUnion.lean) | 有效后继步自动扩张整棵迭代树；原树操作列的实际支撑列；单根迭代树及恒等延长的实际实例；nice 支撑证书及实际空树实例 |
| [HullReturn](HullReturn.lean) | 可沿可数壳搬运的分支下降见证；下降见证排除任何传递返回锥；避开指定不良基枝的实际可数返回 |
| [InitialPull](InitialPull.lean) | 下降历史的实际模型行及全前驱公式；下降递归的初始行；可数壳的根秩段自动给出下降递归的初始行 |
| [KeepTransfer](KeepTransfer.lean) | 弱迭代的可数线性模型列及相容返回列；反射壳固定原有限历史中的全部内部箭头；线性模型列的返回因子随实际新结点延长；弱迭代历史保留所有此前列图 |
| [LimitDiagram](LimitDiagram.lean) | 在极限长度上沿共尾树枝添入新顶点；极限处新增的整列嵌入图；极限添枝后的完整初等图与交换律 |
| [LocalAgreement](LocalAgreement.lean) | 内部所属短扩展器直接延长实际迭代树；内部所属扩展器的两侧实际后继保持子集一致性 |
| [NiceReturn](NiceReturn.lean) | 所属短扩展器、不可达性和有限幂一致性的回拉；初等图回拉部分列；Skolem 回拉后指定超幂边的完整恢复；反射壳中原指定超幂边的回拉 |
| [Overview](Overview.lean) | 迭代树、后继扩张与极限添枝的公共入口 |
| [OwnerQuality](OwnerQuality.lean) | 原关系树的实际所属强度证书 |
| [Padding](Padding.lean) | 极限处的迭代树扩张；任意原关系模型上的真实恒等填充核心；从良基共尾树枝自动完成极限扩张；任意非空内部序数长度的 padding 树 |
| [RawReturn](RawReturn.lean) | 同一原共同层的严格切片与返回施加 |
| [Reflection](Reflection.lean) | 下降递归所用模型及其实际初始实例；整树复制中的可数闭工作模型；可数闭工作模型的实际 nice 后继；有限原公式族的两层反射上下文 |
| [ReturnFactor](ReturnFactor.lean) | 可数共尾长度上实际选择一条共尾树枝；由实际相容实现证明树枝良基；共尾枝的完整初等因子与实际传递极限；返回因子落实到同枝的指定实际极限 |
| [Step](Step.lean) | 后继结点的整列嵌入由替代实际收集；添枝后完整初等图的交换律；一条实际超幂边及其所属模型 |
| [StepSyntax](StepSyntax.lean) | 原迭代树核心及求值源证书；可数根的 ω 长迭代树全部模型可数；整棵 ω 树的模型列与全初等嵌入列回拉；树的极限条件给出实际直接极限证书 |
| [System](System.lean) | 树枝上各模型的带标号并；原模型与带标号分量的完整内部同构；树枝上的实际定向系统 |
| [TreeSyntax](TreeSyntax.lean) | 原关系迭代树共同核心的一阶编码；带真实源证书的原迭代树及其后继保持编码 |
| [Weak](Weak.lean) | 弱迭代状态属于同一个实际集合包络；同一集合上的实际应答选择函数；应答函数驱动的唯一超限运行；运行的唯一性与前缀重放 |
| [WeakAnswer](WeakAnswer.lean) | 线性模型列沿实际返回方块的后继；弱迭代在可数极限处的完整延长；弱迭代后继步由可复制原关系树的返回定理自动产生；任意极限长度的相容弱迭代历史取并 |
| [WeakAnswerTreeSyntax](WeakAnswerTreeSyntax.lean) | 原树枝、带标号系统与规范极限的纯公式；强返回极限证书的公式层；定向系统初等性的公式层；线性状态、历史与全前驱保持的一阶编码 |
| [WeakBranch](WeakBranch.lean) | 弱迭代极限到良基树枝的严格装配 |
| [WeakTree](WeakTree.lean) | 强实际应答请求及其选择器公式 |
| [WorkingApply](WorkingApply.lean) | 双模型迭代的实际 nice 后继 |
