# 博弈与策略

本目录按依赖次序组织相关定义、构造与证明。公开声明保留原命名空间，调用时直接导入下列模块。

| 模块 | 数学内容 |
| --- | --- |
| [AnswerAdvance](AnswerAdvance.lean) | 用原历史位置与原表项装配规则 (7)；已发出的辅助走法得到回答后的实际历史；同一反射层中的回答、实数落子与下一辅助走法 |
| [AnswerNativeInput](AnswerNativeInput.lean) | 原关系模型实际产生回答事件与下一请求；所属模型内把完整回答送回实际控制层 |
| [Archive](Archive.lean) | 完整原档案行及其当前共同图视图 |
| [ArchiveEdge](ArchiveEdge.lean) | 原奇数边上的实际存档延伸 |
| [ArchiveGraph](ArchiveGraph.lean) | 当前低层对象沿实际共同图回到原档案；给定实际共同图上的原档案求值 |
| [ArchiveGrowth](ArchiveGrowth.lean) | 同一锥目标中的原继续边 |
| [ArchiveImage](ArchiveImage.lean) | 真实原档案在指定锥中的五坐标像 |
| [ArchiveImageSyntax](ArchiveImageSyntax.lean) | 同一原档案五坐标像的完整一阶公式 |
| [ArchivePlayNative](ArchivePlayNative.lean) | 同一原请求中的短图事件与实际背景前缀 |
| [ArchiveSyntax](ArchiveSyntax.lean) | 共同有限状态中基底、历史界与原局的完整编码；同一原存档、事件与实数前缀视图的完整编码；全部原档案行、根名字与当前视图的一阶编码 |
| [Basis](Basis.lean) | 原秩层在实际根图上的完整解释；根锚点给出实际字母表满像；原关系反射层之间的固定低层公式传输；初值、运行状态和原档案共用的固定根基底 |
| [CatalogRead](CatalogRead.lean) | 只按元数固定的子类型程序表；一轮所需的固定节点与端点查询包；节点和端点查询的实际统一表；类型游戏的实际走法与表项读取 |
| [Continue](Continue.lean) | 从当前继续输入读取唯一高度；实际下一走法的全部节点参数留在共同低层；全部存档的实数前缀保持在同一原历史中；两种实际树后继共用的完整回答证书 |
| [ContinueAssemble](ContinueAssemble.lean) | 当前原结构内装配继续输入 |
| [ContinueNative](ContinueNative.lean) | 当前原关系中的实际继续选择 |
| [Control](Control.lean) | 原查询表覆盖全部合法新参数；随原策略搬运的有限历史控制记录 |
| [ControlCard](ControlCard.lean) | 原控制记录中的武丁界在实际工作源内不可达 |
| [Corollary610](Corollary610.lean) | 实际运行终点提供并树的逐节点呈示；实际最小请求编号的无界性与首达时刻；泛型策略的原对局与辅助实数坐标一致；6.6：稠密条件在指定旧轮之后被实际捕获 |
| [DigitsImage](DigitsImage.lean) | 原辅助博弈的三阶段时序；三阶段字母图的唯一性与实际地模型像 |
| [Elastic](Elastic.lean) | 类型游戏中 dcp 的弹性条件 |
| [EvenLimit](EvenLimit.lean) | 旧运行的原控制坐标在实际锥中的像列；控制参数在偶数极限中相同；偶数分支的直接极限不良基 |
| [GeneralProjection](GeneralProjection.lean) | 实际传递根的原生自然数及完整数字图；任意原根的实际规范呈示；实际传递隶属根的字母载体与严格秩界；真实隶属根中的临界点下界读出 |
| [GenericPreparation](GenericPreparation.lean) | 三阶段历史中的原字母图追加；地模型稠密集与真实泛型性调用；首达时刻的实际请求捕获；任意参数域下界以上的原游戏重置走法 |
| [GenericRun](GenericRun.lean) | 原 I 策略下三步响应保持可继续状态；地模型中的可继续轮状态集合；扩张中的最小编号响应仍产生真实地状态；扩张内部的最小请求递归 |
| [ImageAbsolute](ImageAbsolute.lean) | 整份回答证书从反射秩层回到所属模型 |
| [ImageValue](ImageValue.lean) | 实际初等图中的目标函数值回拉 |
| [IssuedReset](IssuedReset.lean) | 任意已发出重置走法的实际更新输入 |
| [IterationArchivePlay](IterationArchivePlay.lean) | 每份原档案在足够晚的实际阶段与给定对局逐点对应 |
| [IterationCopy](IterationCopy.lean) | 选中旧档案后的两次复制与下一有限状态；从非空请求及原档案列直接执行继续轮；从同一原请求记录实际执行两类后继；完整状态码直接调用实际后继 |
| [IterationNextSyntax](IterationNextSyntax.lean) | 同一原奇数边上的完整三图方程编码；实际选行和原奇数边的一阶编码；同一次两步延伸、原局追加和新档案的一阶编码 |
| [IterationReset](IterationReset.lean) | 重置工厂的同一次实际落子与下一有限状态 |
| [IterationStep](IterationStep.lean) | 原字母表输入、实际落子与同一次下一请求；原树、工作复制、请求与原对局的共同有限状态；同一两步树延伸与实际落子闭合下一有限状态 |
| [IterationStrategyPlay](IterationStrategyPlay.lean) | 同一指定分支中的唯一档案像及实际增长；原关系运行的偶数枝及同一锥中的控制像；实际原关系偶数枝的极限不良基；原关系运行的实际极限固定根低层 |
| [IterationSyntax](IterationSyntax.lean) | 原请求及整列档案不变量的一阶编码；原树、复制历史、档案与原局的七十五项状态码 |
| [LevelReply](LevelReply.lean) | 旧请求的实现高度沿实际回答严格下降 |
| [NativeEntry](NativeEntry.lean) | 完整原前缀随同一次真实落子精确追加；同一原控制历史中的求值唯一性 |
| [NativePlay](NativePlay.lean) | 从原历史恢复继续分支的查询与候选；原三阶段历史的旧事件与域增长；原模型内部的完整游戏查询秩界；旧轮与当前原策略历史的有界对应 |
| [NativeRecord](NativeRecord.lean) | 两类实际原记录沿原树边保持严格界 |
| [OddBranch](OddBranch.lean) | 规则 (6) 实际选中同一旧轮；从同一旧轮和原继续规则装配伸展输入；原已发出请求自动完成继续轮；统一历史自动驱动非空继续分支 |
| [Padding](Padding.lean) | 重置轮的 padding 与回到偶数枝的实际超幂 |
| [PastEvents](PastEvents.lean) | 完整存档与三阶段历史逐轮对应 |
| [PastRoots](PastRoots.lean) | 历史行的共同根图与固定低层 |
| [PreparedResult](PreparedResult.lean) | 同一原边上的完整存档与 subtype 返回目标反射层；同一完整代表池把子类型送入实际原后继；同一次原继续选择生成原生后继；同一档案行的完整准备与两步复制结果 |
| [QueryTransfer](QueryTransfer.lean) | 原节点查询沿固定秩层传递 |
| [Rank](Rank.lean) | 原规则 (7) 自动延伸策略控制历史；原实数落子与下一轮的控制位置；原重置走法自动成为更新输入；重置输入的原公式总构造 |
| [RawAnswer](RawAnswer.lean) | 原回答、实际落子与完整下一请求 |
| [RawArchive](RawArchive.lean) | 原游戏的十一项档案及选定共同图列 |
| [RawArchiveEdge](RawArchiveEdge.lean) | 十一项原档案上的实际父边几何 |
| [RawArchiveImage](RawArchiveImage.lean) | 真实原档案在指定锥中的五坐标像 |
| [RawArchiveSequence](RawArchiveSequence.lean) | 同一锥目标中的原继续边；原档案索引与真实新增节点的严格次序；同一原档案五坐标像的完整一阶公式；同一指定分支中的唯一档案像及实际增长 |
| [RawArchiveSyntax](RawArchiveSyntax.lean) | 十一项原档案及所选共同列的一阶编码 |
| [RawBranchProjection](RawBranchProjection.lean) | 每份原档案在同一晚阶段读回原对局字母；原档案第一图是原对局沿根腿逐字母搬运所得的有限图；同一良基锥中的原根树名；任意良基原枝中的同次三图并 |
| [RawContinueCandidate](RawContinueCandidate.lean) | 同一原共同层中的完整候选；原模型中的秩比较给出实际最大序数查询；第一次原后继中的实际候选与根查询 |
| [RawContinueFinish](RawContinueFinish.lean) | 固定第二原后继中的完整回答收尾 |
| [RawContinueMove](RawContinueMove.lean) | 非空原请求的同次两步核验；一般原游戏的完整继续后继 |
| [RawContinueRenewal](RawContinueRenewal.lean) | 目标原关系模型内部构造查询池并取得低层实现；固定第一次原后继中的恢复、重启与再次施加 |
| [RawContinueStep](RawContinueStep.lean) | 固定继续工厂的第一次原树延伸 |
| [RawCritical](RawCritical.lean) | 原请求确定背景中的完整有限对局前缀；同一背景原前缀跨实际原树边保持；原对局前缀的一阶编码；原根中的实际秩切片及完整关系解释 |
| [RawFirst](RawFirst.lean) | 一般原游戏的完整重置后继；非空请求的第一个实际原后继 |
| [RawImage](RawImage.lean) | 给定原关系模型中的实际回答生成原生后继 |
| [RawInput](RawInput.lean) | 原字母输入与同一次完整原请求后继 |
| [RawIterationCodeStep](RawIterationCodeStep.lean) | 原生有限状态的两分支实际后继；六十六项原状态码的实际后继总性 |
| [RawIterationNext](RawIterationNext.lean) | 六十六项原生状态的精确后继几何 |
| [RawIterationNextSyntax](RawIterationNextSyntax.lean) | 十一项原档案的父边与重置方程编码；十一项实际选行及原父边的一阶编码；原生两步延伸、原字母追加与十一项档案的一阶编码 |
| [RawIterationState](RawIterationState.lean) | 原树、请求与原对局的六十六项状态 |
| [RawIterationSyntax](RawIterationSyntax.lean) | 每条实际操作的原根临界点证书编码；原请求的完整一阶编码；原迭代六十六项状态的完整对象语言 |
| [RawIterationUnion](RawIterationUnion.lean) | 原迭代全部输入共用的响应表；同一原响应表上的内部全 ω 运行；原生六十六项运行的内部并树 |
| [RawPrepare](RawPrepare.lean) | 非空原请求自动选择真实档案；非空原请求的实际继续准备 |
| [RawPrepareRoot](RawPrepareRoot.lean) | 原根切片上的完整查询回读；所选共同图识别两端的原根切片 |
| [RawReply](RawReply.lean) | 辅助类型游戏的固定参数；规则 (4)–(6)：域增长、重置与较早轮的继续；第二方辅助走法：原规则 (2)–(6)；玩家 I 的回答：原规则 (7) 及唯一新增的空根条件 |
| [RawReplyInput](RawReplyInput.lean) | 同图完整回答进入实际目标请求层 |
| [RawReplyTransport](RawReplyTransport.lean) | 完整原回答的同图输运数据 |
| [RawRequest](RawRequest.lean) | 一般原模型中的实际请求 |
| [RawResetChecked](RawResetChecked.lean) | 一般原请求的同次重置核验 |
| [RawResetFactory](RawResetFactory.lean) | 一般原请求的同次重置工厂 |
| [RawResetReply](RawResetReply.lean) | 同一次原重置的完整回答与查询表 |
| [RawRestartLink](RawRestartLink.lean) | 原继续中的三图严格衔接 |
| [RawReturnReply](RawReturnReply.lean) | 第二原后继中的同次完整回答 |
| [RawRootContinueStep](RawRootContinueStep.lean) | 实际工厂的低秩方块推进原根切片；同次重置工厂的根切片与字母双射；不同原前驱的活动边推进当前根切片 |
| [RawRootSyntax](RawRootSyntax.lean) | 原根切片及保存时下界的完整对象语言 |
| [RawSavedBase](RawSavedBase.lean) | 原档案保存时的源根切片 |
| [RawShiftedStrategy](RawShiftedStrategy.lean) | 一般原根中的全部良基枝推送策略 |
| [RawTurnStrategy](RawTurnStrategy.lean) | 辅助游戏 II 获胜迫使原树含空根；同一原控制记录的真实零轮；原辅助游戏直接生产共享零轮控制实例；同一控制记录的完整首请求 |
| [Recovery](Recovery.lean) | 同一反射结构中的实际实现核调用；继续树边目标中的真实低层实现；在实际目标反射层内恢复一张图 |
| [RecoverySyntax](RecoverySyntax.lean) | 类型游戏的一张图恢复；回答查询只使用 ω 的共同基底；游戏查询的共同低参数基底；一张图恢复的原语言句子 |
| [RelativeStart](RelativeStart.lean) | 给定地模型内部的初始反射上下文；给定根上的恒等图和共同低层实现；实际首行与零轮请求构造共同有限初态；给定地模型中的实际零轮游戏记录 |
| [ReplyDescent](ReplyDescent.lean) | 规则 (7) 的完整类型约束及实际读取；在真实低层前缀后添加回答末位；泛型 I 方向：任意排列下的原标签恢复与严格高度下降 |
| [ReplyPool](ReplyPool.lean) | 同一有界池中的完整规则 (7) |
| [ReplyReflect](ReplyReflect.lean) | 同一个规则 (7) 回到后继反射层 |
| [RequestState](RequestState.lean) | 下一原请求与实际档案列的共同状态 |
| [Reset](Reset.lean) | 类型游戏重置位置的实际完整类型 |
| [ResetNative](ResetNative.lean) | 目标表中的原查询回到完整回答层核验；首次原生重置的实际字母与目标前缀；空标签请求在原模型中生成重置轮 |
| [ResetResult](ResetResult.lean) | 原生重置的完整两步结果 |
| [Restart](Restart.lean) | 恢复节点后在同一反射层重新启动 |
| [RestartLinkSyntax](RestartLinkSyntax.lean) | 同一恢复记录中的三图延伸方程；原继续方程在传递目标中的精确像；同一恢复记录的三图方程句法 |
| [ReturnBranch](ReturnBranch.lean) | 奇数尾枝上唯一的实际节点列；原返回节点列直接使用统一的三图取并；三张并图沿初等图给出目标树中的共尾分支 |
| [ReturnSyntax](ReturnSyntax.lean) | 奇数存档的实际有限树节点；奇数边上的三张坐标图在返回极限中相容；原恢复图、共同极限证书及一阶公式 |
| [ReturnTree](ReturnTree.lean) | 并历史中每份实数存档仍是同一原对局的前缀；极限中的共同树及其实际初等像 |
| [RigidAssemble](RigidAssemble.lean) | 由同一旧回答和当前候选调用高度刚性核 |
| [Rigidity](Rigidity.lean) | 超过关系与 dcp 定义域固定唯一高度对象 |
| [RootSquare](RootSquare.lean) | 已选共同图与两条原根图的交换 |
| [Round](Round.lean) | 后继反射秩段中的回答证书成为实际超幂；反射回答沿共同秩段进入跨模型树边；原回答的正则界与共同极限秩段；内层更新产生实际跨模型迭代轮 |
| [RoundNativeScope](RoundNativeScope.lean) | 全部内部有限历史上的逐步检查；原游戏固定参数的自动构造；Neeman 5.13 的完整辅助闭博弈；两种类型游戏共用的原低点句法 |
| [RoundParity](RoundParity.lean) | 原模型轮号与外部档案索引；同一外部轮号与反射层中的回合条件 |
| [RunMove](RunMove.lean) | 实际后继层中的原回答查询；实际超幂回答通过原游戏的查询表；跨模型回答实际推进原策略历史；当前辅助历史唯一确定完整原实数前缀 |
| [SavedCopy](SavedCopy.lean) | 实际旧活动行的共同层及当前反射层所属；同一次原继续结果完成两步复制；从实际旧回答推进原树与复制历史 |
| [SavedNameSyntax](SavedNameSyntax.lean) | 原关系存档的五十四个回答坐标；原档案中的树名与同一个根对象；原保存码中根树名的一阶编码 |
| [SavedNative](SavedNative.lean) | 完整原回答使用自身支撑保存同一份存档 |
| [SavedNode](SavedNode.lean) | 历轮回答的完整原模型记录；统一历史中的全部旧回答；同一存档的树、长度及三张坐标图；原超幂更新同时推进整列回答历史 |
| [SavedView](SavedView.lean) | 保存时的完整代码与当前共同图视图 |
| [ShiftedProjection](ShiftedProjection.lean) | 实际有限节点列的三图统一取并；同一有限节点列的三图合成为共尾分支；三坐标树的投影博弈；固定有限序列空间的投影博弈数据 |
| [ShiftedStrategy](ShiftedStrategy.lean) | 任意非偶数良基极限固定原局低层；指定共尾分支上的实际恢复图；任意良基极限中的共同移位树与原第一坐标；统一对局在任意共尾良基分支上的移位投影 |
| [StrategyPlay](StrategyPlay.lean) | 所有原实局共用的实际后继函数；从统一响应表构造原博弈的实际策略；服从所构造策略的任意原对局与递归前缀逐轮一致 |
| [Subtype](Subtype.lean) | 同一完整回答对原查询表的所有合法代码为真；原回答证书已经给出首个临界点的下界；工作模型中的有限反射秩段；完整原共同层中的语言与查询域 |
| [TraceImage](TraceImage.lean) | 原树边上的全部旧事件及后续历史 |
| [Tracked](Tracked.lean) | 四元组代码的实际地模型像；泛型 I 方向的无界继续类型；继续请求在全部后续合适局面中的实际合法性；有限坍缩条件中强制出现可继续请求 |
| [TreeImage](TreeImage.lean) | 原关系中的有限空间与树沿实际图进入传递目标 |
| [TreeStep](TreeStep.lean) | 原获胜策略的实际反射初值；从 II 原策略直接构造有限递归的迭代根；在任何原实数落子之前装配统一递归的零轮 |
