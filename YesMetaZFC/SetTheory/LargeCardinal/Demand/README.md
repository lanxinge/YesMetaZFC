# 深度调度与 demanding 构造

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [AlphabetGround](AlphabetGround.lean) | demanding 树沿历史收缩的实际逆像；历史逆像关系的有界定义；历史逆像进入实际泛型扩张；泛型扩张中的实际最小辅助域 |
| [AlphabetImage](AlphabetImage.lean) | 实际原边保持同一树的两个最小字母域 |
| [AnswerArchive](AnswerArchive.lean) | 同一次原回答实际登记新档案 |
| [AnswerTransport](AnswerTransport.lean) | 同一原表项与 23 槽完整回答装配规则 7.1(6)；原生 23 槽回答与已发请求的固定表装配；固定 Q 行的三条码进入同一个原回答；指定后继中的固定 Q 行与合法回答 |
| [ArchiveCode](ArchiveCode.lean) | 档案函数及原树对应的对象语言 |
| [ArchiveHistory](ArchiveHistory.lean) | 合法回答与下一实数落子中的档案维护 |
| [ArchiveSyntax](ArchiveSyntax.lean) | 奇深度表和完整字母枚举的可分离公式；demanding 档案的完整一阶表示 |
| [ArchiveUpdate](ArchiveUpdate.lean) | demanding 原历史中的请求与回答对应；幂集代码产生 demanding 字母枚举；demanding 原回合的实际档案；demanding 档案与同一原迭代树的对应 |
| [AuxGrowth](AuxGrowth.lean) | 奇父边上的辅助图延长和待填字母入图 |
| [BranchDepth](BranchDepth.lean) | 实际奇父边与深度更新的一阶表示；完整原回合后继的可定义响应关系；全部原输入共用的一张内部响应表；同一原响应表上的内部全 ω 运行 |
| [BranchOdd](BranchOdd.lean) | Claim 7.9：demanding 偶数枝的实际直接极限不良基；良基枝中的实际奇档案共尾 |
| [BranchProjection](BranchProjection.lean) | 任意源行的枚举行沿实际奇枝永久保留；Neeman 7.8 (iii)：实际奇枝的内部深度覆盖；同一极限锥中的辅助图延长；同一奇枝锥中的最小辅助字母域 |
| [ContinueFirst](ContinueFirst.lean) | 双图节点名字列沿同一完整前驱图的运输；demanding 非重置第一施加的实际生产 |
| [ContinueInput](ContinueInput.lean) | 最大序数查询的数值程序；原四十七槽请求实际生成二十九槽继续输入 |
| [ContinueNative](ContinueNative.lean) | 非重置回合的两个实际原树后继 |
| [ControlPlusContext](ControlPlusContext.lean) | 同一 II 原策略与 demanding 更新核的实际初始反射层；同一参数域中的 reset/issue 控制合取；原控制与 reset/issue 控制的同一记录 |
| [ControlRecord](ControlRecord.lean) | 随 demanding 控制记录搬运的实际三表证书；demanding 历史中的原实数字母与 II 策略回复；原 II 胜策的完整有限控制记录 |
| [CopyReset](CopyReset.lean) | demanding 已选重置回合的完整工作复制 |
| [Corollary712](Corollary712.lean) | 同一收缩变换沿原模型与实际初等腿运输；7.4：原 I 胜策产生扩张中 a(¬S) 的实际 I 胜策；7.4 在原 Col(ω,δ) 名称扩张中的实际出口；逆像树的反 demanding 胜策回到合法树 |
| [CounterGround](CounterGround.lean) | 扩张中同一反策略的有限回复回收 |
| [Depth](Depth.lean) | 奇祖先深度上的内部调度 |
| [FirstLetter](FirstLetter.lean) | 原 I 胜策自动给出一个实际实数字母 |
| [GeneralProjection](GeneralProjection.lean) | 良基 demanding 极限固定原字母；同一 demanding 并树的全部活动临界点；7.8 的广义 demanding 投影 |
| [GenericAvoid](GenericAvoid.lean) | 捕获高度与同一实际 counter 控制历史；demanding 继续请求的实际合法性；有限坍缩条件中实际出现 demanding 继续走法；原模型内的稠密集及实际泛型命中 |
| [GenericReply](GenericReply.lean) | 实际双图记录的无界继续类型；同一反策略的实际回复驱动双图继续类型；任意原回答的实际下降与同一反策略继续 |
| [HistoryConstruction](HistoryConstruction.lean) | demanding 类型游戏的增长与继续规则；7.1 的第二方走法：双图节点、域增长、重置和继续；7.1 的第一方回答：原 subtype 与三个固定查询；双图继续请求与稠密命中的原公式 |
| [ImageAbsolute](ImageAbsolute.lean) | demanding 回答的同次证书从反射秩层向上还原 |
| [IterationState](IterationState.lean) | 原 II 胜策的 demanding 迭代初态；demanding 内部运行的统一有限状态 |
| [IterationStep](IterationStep.lean) | 原 II 胜策产生统一内部运行初态；统一状态的实际两分支后继 |
| [IterationSyntax](IterationSyntax.lean) | 六十六项 demanding 状态的可分离公式 |
| [LevelTable](LevelTable.lean) | 双图请求的实际实现高度；原模型内的双图有界高度表 |
| [NodeProgram](NodeProgram.lean) | 双图节点查询的数值程序和实际名字列 |
| [OldView](OldView.lean) | 旧 demanding 回合的共同层视图 |
| [Parameters](Parameters.lean) | demanding 类型游戏的实际走法与双图元数 |
| [PowerRead](PowerRead.lean) | 计数回合读取原 Woodin 参数 |
| [ProjectionSpace](ProjectionSpace.lean) | 第一辅助坐标满射的 demanding projection；补树胜策、实际满射与 demanding projection；a(¬S) 的实际原对局收益集及两种反策略出口；外部点否定 projection 后的实际 counter control |
| [RankStep](RankStep.lean) | 合法 demanding 请求的实际 24 槽载荷；已落下的原 demanding 请求及其真实程序载荷；合法有限历史中旧回答的回读；原控制实际产生完整请求 |
| [RawContinue](RawContinue.lean) | 非重置请求的完整原回合 |
| [RawPool](RawPool.lean) | 7.1 完整回答从传递证书层向上读取；23 槽 demanding 回答沿同一代表池进入原后继；完整双图回答回到同一有界证书层；同一次有界塌缩中的完整 demanding 回答 |
| [RawReset](RawReset.lean) | demanding 重置回答的实际双后继；demanding 重置请求的完整原生回合 |
| [ReadyStep](ReadyStep.lean) | 任意下界以上的 demanding 游戏实际重置走法；demanding 辅助轮的实际准备状态与合法请求；demanding 游戏中原 I 策略控制下的三步推进 |
| [RealTrace](RealTrace.lean) | 原关系中的实数短图与完整历史 |
| [ReplyBase](ReplyBase.lean) | demanding 固定回答查询的低参数基底 |
| [ReplyCatalog](ReplyCatalog.lean) | 完整回答直接读取开局已选定的原查询行 |
| [ReplyDomain](ReplyDomain.lean) | 有限读写层中的 demanding 元数；原固定查询行的双池在原生反射层中的读取 |
| [ReplyQueries](ReplyQueries.lean) | 同一完整回答中的三条实际查询 |
| [ResetControl](ResetControl.lean) | 原零轮走法生产同一类型的 demanding 更新输入；原零轮走法到同一 43 项输入的完整控制句 |
| [ResetRequest](ResetRequest.lean) | 已落下重置请求产生同一原生回合 |
| [ResetRound](ResetRound.lean) | 重置请求的局部回答与历史对应 |
| [RetractionFrame](RetractionFrame.lean) | 收缩树变换的有限对象组 |
| [RetractionTree](RetractionTree.lean) | 第一层补全精确恢复原双辅助字母域；历史逆像的前缀封闭性；同一满射辅助图沿历史收缩运输；7.12 使用的实际变换树 |
| [RoundReal](RoundReal.lean) | 原回合实数图的函数性及低秩归属 |
| [RoundRecovery](RoundRecovery.lean) | 非重置回合的原类型与同高度双图恢复；已运输旧回合的无额外不交假设恢复 |
| [RoundScope](RoundScope.lean) | 同一次任意排列实现的双图恢复句子；demanding 回合所用的纯高度刚性句子；原排列下的完整弹性 demanding 回答；7.8 的双图回答与实际一步扩展器 |
| [RunPlay](RunPlay.lean) | 每个实际后继保留原对局的已落实数字母；同一原对局条目沿内部全部阶段保持；从真实内部历史唯一构造完整原实数对局 |
| [SeparatedGame](SeparatedGame.lean) | Neeman 7.1 的完整辅助闭博弈；原 demanding 游戏的最弱历史规则证书；原回答实际追加到 II 胜策的同一历史；原 II 胜策实际产生下一 demanding 请求 |
| [Setup](Setup.lean) | demanding 游戏两种元数的实际固定查询包；7.1 的固定查询表；双辅助坐标游戏的固定查询行；demanding 游戏的实际固定参数 |
| [StateReal](StateReal.lean) | 已发请求中的完整实数前缀；同一原对局的实数条目；当前原历史的实数字母：存在与唯一 |
| [UntagGeneral](UntagGeneral.lean) | 标签重编码进入实际泛型扩张；实际初等根腿运输标签树与最小字母域；demanding 投影去标签，保留同一原实数；同一迭代树上逐枝去标签 |
