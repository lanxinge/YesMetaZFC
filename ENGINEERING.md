# 工程维护记录

## 第一批清理（2026-09-08）

基点为 `b36e2434459fa71bd6d5ff91f0882058a9746399`。该提交的
[Lean CI](https://github.com/lanxinge/YesMetaZFC/actions/runs/34211156386)
成功完成 796 个任务。CI 中 `PureSyntaxFixedPoint` 用时 154 秒，
`PureFinalSyntax` 93 秒，`PureLogicalSchemaSets` 84 秒；这些是模块构建时间，
不能直接视为内核类型检查时间。

### 已实施的改动

- 删除四个无声明、无调用方的兼容入口：`AvatarSoundness`、
  `AvatarRegistrySoundness`、`ExpressionEncodingSupport`、`LogicalRuleEncodingSupport`。
  AVATAR 的实际数学接口仍在 `DAGCertificate.IntrinsicReplay`。
- 删除 14 个无引用私有声明及 `ResolutionTraceStep` 辅助结构，包括两条已退役的
  resolution 回放实现。当前 `compactResolutionCursorProof` 路径保留。
- 移除 `IntrinsicQuineCarrier` 中常开的 `simp` 重写追踪。
- `PureSyntaxFixedPoint.tag_injective` 明确列出九种标签比较，并使用
  `congrArg` 固定隶属关系的替换参数。元组单射性调用显式传入种类与字段。
- `PureLogicalSchemaSets.constructor_natural` 按九种实际语法树组合封闭性证明，
  移除 `repeat' first` 对构造子和参数槽的试探。
- 固定公式的符号覆盖检查使用 `decide +kernel`，由 Lean 内核计算并检查证明；
  没有增加 `native_decide` 或新的可信公理。
- 修正 README、恢复说明及自动化入口中的过时状态。

修改涉及的 150 个公开声明的类型签名未变；源公理、Rosser 句子及 quotation
定义未修改。上述私有声明的删除同时经过引用检查与构建验证，不能仅凭名字出现
次数决定任意声明是否可删。

### 性能证据

本地对 `PureSyntaxFixedPoint` 直接运行 Lean，优化前约 162.5 秒，优化后约
2.0 秒，均包含导入时间。优化前 tactic 累计约 161 秒、内核检查约 0.086 秒；
优化后分别约 0.615 秒和 0.082 秒。主要改善来自 elaboration，非削弱内核检查。

`constructor_natural` 的声明级抽样由约 6.0 秒降至约 0.17 秒。
这些是同一环境的局部测量，并非独占机器基准；不得将其比例推广到全库或 CI。
并行声明的累计耗时也不能直接相加作为墙钟时间。

### 验证与范围

- 默认 `lake --wfail build`：796 个任务成功，零错误、零警告。
- `bash scripts/check-all.sh`：799 个源模块对应的 801 个任务全部成功；
  扫描器可执行目标的 316 个任务也全部成功，零错误、零警告。
- 26 个接口的依赖审计无 `sorryAx`；原有 20 个终局接口的公理依赖集合逐项相同。
- 扫描器 `--help` 正常；对 `Ordinal.transitive` 的单目标扫描正常返回
  `not_closed`，原因是缺少适用的 `GoalRequest` 提供器。本检查验证启动与诊断路径，
  没有把该目标误记为自动证明成功。

当前保留 799 个 Lean 源文件。`ProveAutoBranchProbe` 由扫描器生成的源码动态导入；
`HigherOrderNativeReplay`、`QuineEncoding.PureSet`、
`QuineEncoding.SwapBoundStructuralCorrectness` 是有实质内容的独立模块，
本轮保留并由 `scripts/check-all.sh` 覆盖。默认根入口不可达并不等于死代码。

## 架构精简：槽位代数与 quotation 归纳（2026-09-08）

用户要求通过底层复用将 Lean 源码压到 200,000 行以下，排除空行压缩等操作；
远端提交暂缓到下一次迭代里程碑。本轮从前述第一批清理后的本地工作树继续。

### 已实施的公共抽象

- `Derivation.Substitution.Algebra`：类型化槽位映射的后复合、首尾分配、弱化后
  读取尾映射，以及无自由槽项的替换不变性。适用于任意签名、排序与上下文，
  没有把参数个数固定为一至四，也不展开对象公式正文。
- `FormulaTemplate` 的实例化、打开 binder 与应用的传输改由这些组合律完成。
  具体 arity 接口保留；其证明只计算槽位，不重新归纳语法树。
- `Automation.QuotationInduction.FormulaClosure`：只归纳一次实际 Hilbert quotation，
  调用方提供关系原子、等式、否定、蕴含与全称构造的封闭性。
  普通识别与带符号集的识别均已接入；后者把自然数码域证据并入归纳不变量，
  保留原构造要求。
- 当前深度的项、参数列与公式识别直接实例化已有任意合法深度定理。
  移除被覆盖的第二套递归，以及仅为旧四槽证明服务的两个私有替换辅助定理。

现有数据定义没有改动，包括源公理、quotation、Rosser 句子与纯 Δ₀ 参数矩阵。
所有既有公开定理保留；仅 `instantiate_substituteMapped` 的结论把原来的匿名
变量映射写成定义等价的 `postcompose`。没有以新的大规模搜索替代重复证明。

### 实际减量

| 范围 | 重构前行数 | 重构后行数 |
|---|---:|---:|
| `IntrinsicFormulaTemplate` | 854 | 499 |
| `IntrinsicQuineCarrier` | 1,693 | 1,236 |
| `IntrinsicQuineFormulaCarrier` | 1,202 | 844 |
| `FormulaStructuralCorrectness` | 1,619 | 987 |
| `OccurrenceStructuralCorrectness` | 1,904 | 1,850 |
| `StructuralCorrectness` | 1,608 | 1,108 |
| `TransformStructuralCorrectness` | 396 | 153 |
| 两个新公共模块 | 0 | 156 |
| 全部 Lean 源码 | 241,759 | 239,316 |

七个原模块净减 2,599 行，计入公共抽象后全库净减 **2,443 行**。
非空行从 228,757 降到 226,284，净减 2,473 行；空行实际增加 30 行。
统计包括注释，排除缓存和临时审计源码，源文件数为 801。
这一步验证了实质复用的减量，但距离严格低于 200,000 行仍需至少减少 39,317 行，
目前不能据此保证全库一定能达到目标。

### 下一批架构候选

下表是相关源码的规模，**不是预计可删除的行数**。各层仍需先验证公共合同，
再以迁移后的实际净减量决定目标是否可达。

| 候选范围 | 文件数 | 当前行数 | 拟共用的内容 |
|---|---:|---:|---|
| `ProofT` 序列家族 | 25 | 10,119 | 轨迹前缀、取值、终值与行规格的统一装配 |
| 纯模型阶段及 `PureFinal` | 32 | 5,533 | 符号覆盖与阶段规格继承的共同接口 |
| 规范化语义与可靠性 | 17 | 10,363 | 局部改写经过语法上下文的传输归纳 |
| 证书回放及 AVATAR | 44 | 23,060 | 图拓扑与回放不变量，保留各后端语义合同 |

序列层的自然数码、对象项码与证明行码有不同的行前提，不能只把它们当成名字不同
的同一证明。应将公共轨迹容器、编码递推和实际行规格分开；唯一性、负表示和内部
自然数边界仍是正式数学内容。自动化各语法层也应先统一回放合同，再判断哪些结构
递归可以合并，不能直接把不同排序约束或环境语义等同起来。

### 本轮验证

- 默认 `lake --wfail build`：798 个任务成功，零错误、零警告。
- `scripts/check-all.sh`：全部 801 个源模块的 803 个构建任务通过；扫描工具的
  316 个构建任务通过，零错误、零警告。
- 38 个接口的公理依赖审计通过，无 `sorryAx`；上一批 26 个接口的依赖集合
  逐项完全相同，包括 `PureRosser.agreement`、`PureRosser.independent` 及纯 Δ₀ 边界。
- 新 quotation 归纳定理不依赖公理；槽位代数仅使用既有的 `propext` / `Quot.sound`。
- 现有数据定义逐项比对未发现变化；现有公开定理均保留。
- 仅更新本地源码与工程记录，没有创建提交或写入远端。

## 架构精简：有限序列与轨迹（2026-09-08）

本轮从 239,316 行的本地工作树继续，集中处理序列构造的共同推导。

### 公共接口与迁移

- `IntrinsicQuantifier.bounded_forall_of_bound_eq` 统一替换有界全称的集合界，
  保持主体 binder 不变；编码构造和 `IntrinsicCheckedSequence` 共用该接口。
- 新增 `FiniteSequenceConstruction`：统一规范有限图的列表查找、映射后求值、
  逐位置全称引入、值域成员传输，以及轨迹和输入之间的后继定义域关系。
  自然数码、证明行码、对象项码分别保留实际行规格，只共用有限图层。
- `nat_sequence_code_step_of_values` 从左右项的已知取值统一推出配数递推值；
  自然数序列和证明行轨迹不再分别展开同一组等式合同。
- 两种原递归轨迹分别证明等于 `List.scanl`，对象项折叠证明等于 `List.foldl`。
  长度、前缀查找和下一步性质复用标准库定理，原数据定义及计算方程不变。
- 对象项编码把自然数域与初值下界组成一个折叠不变量。前缀界由列表的
  `take` / `drop` 拼接推出，轨迹自然数域由前缀折叠推出，移除重复递归。
- 删除三组已无调用方的私有成员公式 beta 辅助定理；实际 binder 计算在公共
  值域接口中验证，不靠删除规格或增加公理减量。

这些构造处理外部有限列表，列表中的对象项可表示任意内部自然数。
没有把任意模型的内部 ω 当成外部良基序，也没有更改 `Agreement` 的量化范围。
本轮受影响的 160 个公开声明签名保持一致，31 个既有数据定义正文逐项相同；
Rosser 句子、quotation、源公理与纯 Δ₀ 参数矩阵均未改动。

### 实际减量

| 范围 | 重构前行数 | 重构后行数 |
|---|---:|---:|
| `SequenceCodeConstruction` | 668 | 347 |
| `ProofSequenceCodeConstruction` | 681 | 454 |
| `StructuralSequenceCodeConstruction` | 1,140 | 918 |
| `ProofCode` | 1,123 | 1,092 |
| `IntrinsicCheckedSequence` | 350 | 326 |
| `IntrinsicQuantifier` | 406 | 434 |
| `NatSequenceInversion` | 1,375 | 1,389 |
| 新公共模块 `FiniteSequenceConstruction` | 0 | 93 |
| 全部 Lean 源码 | 239,316 | 238,626 |

计入公共接口后净减 **690 行**。非空行从 226,284 减到 225,583，减少 701 行；
空行增加 11 行。当前 802 个 Lean 源文件共 11,414,456 字节，包含注释，
排除构建缓存及临时审计文件。

两轮架构精简累计从 241,759 行降到 238,626 行，净减 3,133 行。
严格低于 200,000 行还需减少至少 38,627 行。本轮完成的是有限图与轨迹的公共层，
不是整个序列家族的重构完成；不能据此保证全库一定能达到 20 万行。
后续仍需检查规范化语义、证书回放等更大范围的共同归纳。

### 本轮验证

- 默认 `lake --wfail build`：799 个任务通过。
- 最终 `scripts/check-all.sh`：全部 802 个源模块的 804 个任务通过；扫描工具
  的 316 个任务通过，零错误、零警告。
- 54 个接口的公理依赖审计通过，无 `sorryAx`；上一轮 38 个接口的依赖集合
  逐项相同，新接口也没有增加此前集合之外的可信依赖。
- 初次严格全库检查发现原前缀接口的索引界未被引用；已通过实际前缀长度与
  剩余列表的拼接证明使用该界，保留原参数名，并重跑上述零警告检查。
- 公开声明与既有数据定义的比对通过；仅删除已由公共接口覆盖的六个私有
  binder 辅助定理。
- 仅更新本地工作树，没有创建提交或写入远端。

## 架构精简：规范化的上下文与类型归纳（2026-09-08）

本轮从恢复后的 238,626 行基点继续，接回规范化重构草稿。
裸 ZFC Rosser 实例已经完成；本轮处理其下层自动化设施的重复证明。

### 公共接口与迁移

- `RewriteTyping` 汇集环境、类型分解与语义相等接口，原有名称及对外签名保留。
  上层证明通过 `inferSortWith_*_parts` 读取类型检查结果，不重复拆解相同计算。
- `RootRewriteSemantics` 分别要求根部项规则、根部公式规则的可靠性，以及允许
  高阶语法时的 λ 同余。`ContextualRewriteSoundness` 对公式、项、参数列完成
  一次公共互递归，把局部规则传输到任意合法语法上下文。
- FOOL 实例固定 `Config.foolOnly` 并保留源、目标的实际片段限制；高阶实例使用
  原 `FoolLambdaContract` 的 λ 同余。没有给 FOOL 增加高阶模型假设，
  也没有把 λ 的受类型限制同余改成对整个载体的无条件同余。
- `HigherOrderTyping` 仅在片段允许高阶项时要求应用和 λ 的类型保持。
  `Term.eval_mem_of_inferSortWith_fragment` 统一两种项求值的类型归纳，
  包括进入 binder 时的环境提升。两种既有类型保持定理改为该接口的实例。
- 共同联结词分支共用证明块；三种公共改写入口展开为可读的多行签名。
  没有更改可计算改写器、配置、语法数据或 checker，也没有通过增大搜索预算减量。

### 实际减量

| 范围 | 重构前行数 | 重构后行数 |
|---|---:|---:|
| `FoolLambdaTraceSoundness` | 1,946 | 992 |
| `FoolTraceSoundness` | 1,445 | 607 |
| 新公共模块 `RewriteTyping` | 0 | 291 |
| 新公共模块 `ContextualRewriteSoundness` | 0 | 588 |
| 全部 Lean 源码 | 238,626 | 237,713 |

两种上层证明共减少 1,792 行，计入 879 行公共基础设施后净减 **913 行**。
非空行从 225,583 降到 224,617，减少 966 行；空行增加 53 行。
当前 804 个 Lean 源文件共 11,367,128 字节，包含注释，排除缓存和临时审计文件。
本轮只改变上述四个 Lean 模块；既有数据定义及终点接口另由编译环境审计核对。

三轮架构精简累计从 241,759 行降到 237,713 行，净减 4,046 行。
严格低于 200,000 行仍需减少至少 37,714 行。本轮消除了上下文与类型归纳的
重复义务；具体根规则的数学可靠性仍由各实例证明，不把这些义务隐藏为新公理。

### 本轮验证

- 默认 `lake --wfail build`：801 个任务通过；`scripts/check-all.sh`：全部 804 个
  源模块对应的 806 个任务通过，扫描工具的 320 个任务通过，零错误、零警告。
- 从编译后的 Lean 环境比对 125 个既有声明：102 个规范化声明和 23 个集合论终点
  及相关接口的类型逐项相同，公理依赖集合逐项相同，无 `sorryAx`。
- 8 个既有数据定义的表达式在忽略绑定变量显示名后逐项相同；其中 7 个原始表达式
  也完全相同，另一个仅因文件内声明顺序改变而产生不同的 hygienic binder 名称。
  本轮未修改其他 Lean 文件，源公理、quotation、Rosser 句子与纯 Δ₀ 矩阵保持不变。
- 上一轮 54 个接口的公理依赖集合全部保持一致；10 个新公共接口的依赖审计无
  `sorryAx`，只使用既有 `propext`、`Classical.choice`、`Quot.sound` 范围内的公理。
- 扫描工具 `--help` 及实际单目标扫描正常退出；`Ordinal.transitive` 仍因缺少适用的
  `GoalRequest` 返回 `not_closed`，与前一轮一致。该检查验证启动和诊断路径，
  不把它记为自动证明成功。
- 仅更新本地工作树，暂未创建提交或推送远端。

## Quine 构造公共接口（2026-09-08）

在现有 `TransformStructuralCorrectness` 中补充四个参数化构造定理：
`syntax_transform_constant_shape`、`syntax_transform_application_shape`、
`syntax_transform_nil_shape`、`syntax_transform_cons_shape`。

操作码、深度、变量位置与替换项均为参数；这些定理不枚举具体操作。
目标理论 `T` 和自由上下文为空的假设列表 `Γ` 也可任意选择。常量符号不再限于
标准 numeral，而由任意闭项及其内部 ω 成员证据给出。公共构造只负责 shape，
原有作用域、操作合法性、总码域和实际 quotation 均保持。

`abstractFreeTop`、`openBound`、`weakenBound`、`swapBound` 四个实现删除
16 个私有 shape 证明，24 处实际调用直接消费公共定理，没有留下操作专属包装。
调用方只提交符号、元数和子项/参数列的变换证明，不再复制见证引入与四槽替换。

| 模块 | 修改前 | 修改后 |
| --- | ---: | ---: |
| `TransformStructuralCorrectness` | 153 | 341 |
| `AbstractFreeTopStructuralCorrectness` | 876 | 690 |
| `OpenBoundStructuralCorrectness` | 861 | 663 |
| `WeakenBoundStructuralCorrectness` | 1,551 | 1,355 |
| `SwapBoundStructuralCorrectness` | 1,558 | 1,362 |
| 五个模块合计 | 4,999 | 4,411 |
| 全仓 Lean 源码 | 237,713 | 237,125 |

四个调用模块减少 776 行，计入公共模块新增的 188 行，净减 **588 行**。
非空行减少 **577 行**至 224,040 行；删除重复证明同时减少 11 个空行，没有进行
独立的空行压缩。全仓仍有 804 个 Lean 文件，11,340,066 字节，净减 27,062 字节。
另有 837 行 Python/Shell，全部代码为 237,962 行；严格低于 20 万仍需净减 37,963 行。
相对 241,759 行的架构精简起点，累计净减 4,634 行。

### 验证

- `scripts/check-all.sh`：全部 804 个 Lean 源模块对应的 806 个任务通过；
  扫描工具 320 个任务通过，零错误、零警告。包括默认根及独立的 swap-bound 模块。
- 对全部 Quine 子模块的 117 个既有公开声明，加上 `PureRosser.agreement` 与
  `PureRosser.independent`，共 119 项编译环境比对：类型表达式逐项相同，
  公理依赖集合逐项相同。无接口消失。
- 四个新定理均无 `sorryAx`；nil 构造无公理依赖，其余只依赖既有 `propext`、
  `Quot.sound`。未修改对象公理、编码、识别图或 Rosser 句子。
- 与本轮前逐文件哈希比较，源码变动严格限于上述五个 Lean 文件。
  没有新增源码模块、样本回归证明或可信公理。
- 检查日志和临时接口审计位于工作区父目录 `quine-refactor/`，不进入仓库。
  本次没有提交或推送。

下一步在公共构造内部提取任意长度见证块，随后迁移其他 Quine 公式节点和 ProofT
证明行装配；本次 588 行实测收益只归入 Quine 已完成批次，不再重复计入后续预算。

## Quine 类型化见证块（2026-09-08）

新增 `Derivation/QuantifierBlock.lean`，在一阶语法层复用已有 `Arguments`：

- `Arguments.substitutionWith` 将类型化见证列接到任意尾替换前面。
- `Formula.existsFreePrefix` 只关闭指定前缀，保留外部自由参数；列表头对应最内层见证。
- `Formula.instantiateFreeTop_substituteFree_liftFree` 统一证明穿过 binder 的替换合成。
- `Derives.existsFreePrefix_intro` 对槽位列表归纳，任意长度、混合排序、任意目标理论、
  假设列表和外部自由参数共用一次存在引入规则。

22 处实际构造改用这一接口：项/参数列识别 2 处、公式识别 5 处、变量出现 6 处、
公共项/参数列变换 2 处、公式变换 7 处，覆盖一至四个见证。
各节点提交见证和原有合取前提，公共层负责量词装配；闭项的弱化消去直接复用
`Substitution.Algebra`。删除 3 个不再使用的私有闭项辅助引理，保留既有公开接口。
新公共规则不依赖 Quine 专用的二、三、四槽替换定理。

| 模块 | 修改前 | 修改后 | 净变化 |
| --- | ---: | ---: | ---: |
| `Derivation/QuantifierBlock` | 0 | 72 | +72 |
| `QuineEncoding/StructuralCorrectness` | 1,108 | 959 | −149 |
| `QuineEncoding/FormulaStructuralCorrectness` | 987 | 649 | −338 |
| `QuineEncoding/OccurrenceStructuralCorrectness` | 1,850 | 1,347 | −503 |
| `QuineEncoding/TransformStructuralCorrectness` | 341 | 287 | −54 |
| `QuineEncoding/FormulaTransformStructuralCorrectness` | 579 | 443 | −136 |
| 合计 | 4,865 | 3,757 | −1,108 |
| 全仓 Lean 源码 | 237,125 | 236,017 | −1,108 |

五个调用模块减少 1,180 行，扣除公共模块的 72 行成本后，净减 **1,108 行**。
当前 **805 个 Lean 文件、236,017 行、222,920 个非空行、11,288,858 字节**。
非空行减少 1,120 行，空行增加 12 行；原始字节减少 51,208。
计入未改动的 837 行 Python/Shell，全部代码为 **236,854 行**，严格低于 20 万还需
净减 **36,855 行**。Quine 两批累计净减 1,696 行；相对 241,759 行的架构起点累计
净减 5,742 行，均不重复计入后续预算。

### 验证与边界

- `scripts/check-all.sh`：全部 805 个源模块对应的 807 个任务、扫描工具的 320 个
  任务均通过，零错误、零警告。实际重建覆盖完整 ZFC 下游和独立 Quine 模块。
- 123 项既有声明（121 个 Quine 公开声明及两个裸 ZFC Rosser 终点）的编译类型与
  公理依赖集合逐项相同。此前四个公共 shape 定理也纳入本次基线。
- 四个新增接口中，两项数据定义无公理依赖；两个通用定理仅依赖 `propext`、
  `Quot.sound`，没有 `sorryAx` 或新增原生可信依赖。
- 逐文件哈希确认：只修改上述五个既有 Lean 文件并新增公共模块；既有公开声明头
  保持。对象公理、quotation、识别图、作用域条件和 Rosser 句子未修改。
- 临时基线、差分、构建日志和编译环境审计在父目录 `quine-blocks/`，未加入源码；
  未增加样本证明，没有提交或推送。

本批完成 1b 的通用见证引入及 Quine 构造迁移。见证块消去、码域伴随结果和 ProofT
证明行尚未迁移。下一落点是 `IntrinsicLogicalTranscriptRows` 的单行条件：复用既有
行规格，把良构性、内部 ω 成员和理论弱化组织为共同结果，再接到单行序列装配。
该文件的主要重复是这些伴随事实，不能把本次见证块收益直接外推为整文件可删量。

## ProofT 逻辑证明行去重（2026-09-08）

本批把逻辑行的数学条件与两列序列装配分开，实际迁移特化、全称分配和混合逻辑行
三个 transcript 家族。单行 specialization 直接调用特化 transcript 的单元素实例，
不再重新证明公式码域、证书码域、取值坐标和完整行条件。

### 公共接口与数学复用

- `IntrinsicCheckedSequence.intro_of_mapped_rows` 在既有行支撑合同上，接受任意行类型、
  verifier、目标理论、自由上下文及两个编码函数。它统一证明双列长度、成员映射和
  逐索引取值；调用方消费两个坐标等式，提交实际行条件。原非空和长度码域前提保留。
- `IntrinsicLogicalTranscriptSupport` 新增五个接口：`intrinsic_zfc_quote_formula_mem`、
  `intrinsic_zfc_quote_formula_code_at`、`intrinsic_zfc_quote_formula_mem_omega`、
  `intrinsic_zfc_quote_term_mem_omega`、`intrinsic_zfc_logical_certificate_mem_omega`。
  它们复用实际 quotation 正确性并统一提升到目标上下文，封装证书外壳的内部自然数界。
- 特化、全称分配、等式替换和等式自反的公式码直接按实际源公式取得良构性及载体
  成员，不再分别重建形式识别和 related 识别树。五类分支证书均直接消费源项或源公式
  的内部自然数界；五类完整证书共用外壳接口。
- 空泛全称继续显式证明正文在深度 1 的识别。其原有源码形状、理论前提和深度条件
  保持，只清理重复中间装配。没有借助模型内部 ω 的外部标准性。

| 模块 | 修改前 | 修改后 | 净变化 |
| --- | ---: | ---: | ---: |
| `IntrinsicCheckedSequence` | 326 | 371 | +45 |
| `IntrinsicLogicalTranscriptSupport` | 76 | 128 | +52 |
| `IntrinsicLogicalTranscriptRows` | 1,550 | 466 | −1,084 |
| `IntrinsicLogicalTranscript` | 371 | 294 | −77 |
| `IntrinsicLogicalTranscriptEquality` | 432 | 164 | −268 |
| `IntrinsicLogicalTranscriptReflexivity` | 212 | 124 | −88 |
| 六个模块合计 | 2,967 | 1,547 | −1,420 |
| 全仓 Lean 源码 | 236,017 | 234,597 | −1,420 |

四个调用模块减少 1,517 行，扣除公共接口增加的 97 行，净减 **1,420 行**。
当前 **805 个 Lean 文件、234,597 行、221,503 个非空行、11,219,711 字节**。
非空行净减 1,417 行；随重复证明删除减少 3 个空行，没有单独压缩空行。
原始字节减少 69,147。Python/Shell 仍为 837 行，全部代码 **235,434 行**，严格低于
20 万还需净减 **35,435 行**。相对 241,759 行的架构精简起点累计净减 7,162 行。

### 验证与边界

- `scripts/check-all.sh`：807 个全源构建任务、320 个扫描工具任务通过，零错误、
  零警告，覆盖全部 805 个源模块及裸 ZFC 下游。
- 189 项既有声明的编译类型和公理依赖集合逐项相同；其中 53 项数据定义的编译
  表达式也逐项相同。包含全部受改模块公开声明、此前 Quine 公共接口及裸 ZFC
  `PureRosser.agreement`、`PureRosser.independent`。
- 六个新定理无 `sorryAx`，各自公理依赖均包含于对应旧证明路径的依赖集合。
  通用装配依赖既有 `propext`、`Classical.choice`、`Quot.sound`；ZFC 接口继承原理论
  构造使用的七项原生公理验证依赖，没有增加原生可信依赖或自定义公理。
- 哈希比较确认仅改动上述六个既有 Lean 文件，没有新增模块、删除公开声明或改变
  对象公理、quotation、证书码、verifier 定义及 Rosser 句子。
- 临时源码基线、差分、构建日志和编译环境审计位于父目录 `proof-row-refactor/`，
  不进入源码。没有新增样本证明、提交或推送。

本批完成逻辑证明行的公共装配与 quotation 码域复用，尚未覆盖所有 ProofT 序列家族。
下一落点是 `NatSequenceInversion` 的前缀唯一性、函数外延和整体唯一性：先核对现有
有限序列接口能消去哪些重复归纳，再决定公共规则；其声明跨度不直接计为可删预算。

## 自由清理：统一归纳与公共证明合同（2026-09-08）

本轮以 **234,597 行**的工作树为基线，目标是实质净减超过 5,000 行。此前 Quine
构造、见证块和逻辑行的三批减量均不计入本轮。实际修改 30 个既有 Lean 模块，
文件总数仍为 805；没有通过删去公开数学接口、加强假设或压缩空行达标。

### 公共接口与迁移

- `Arguments.listRec` 只对参数列骨架归纳；当头项性质已有定理时，调用方不再同时
  承担一遍完整项归纳。Henkin 消去、Quine 识别及四种变换进一步改为项/参数列的
  相互结构递归；每种构造只保留一份证明。Henkin 函数的依赖匹配直接分解
  `HenkinFunc.base` / `witness`，避免额外转换妨碍结构终止检查。
- `Formula.hilbertize_induction` 将编译像的证明归约为关系、等式、否定、蕴含、全称
  五种构造；真、假和派生联结词统一在底层处理。四种 quotation 变换已消费这一归纳。
  `hilbertize_renameMapped` 与 `quote_hilbert_hilbertize` 连接类型化重命名及实际编码；
  它们是新定理，既有 Hilbert 编译和 quotation 数据定义保持。
- `FormulaStructuralCorrectness` 公开通用的数码、项、参数列、公式码域与深度事实，
  七个变换模块删除私有副本。自由变量出现证明复用这些事实，并在分支选择后只装配
  一次构造合同。
- `Derives.existsFreePrefix_intro` 再迁移八处 ProofT 语法承载构造，覆盖一至三槽见证。
  删除重复的逐槽 beta、闭项弱化和中间公式等式；保留外部自由参数及原承载理论。
  `IntrinsicCheckedWitness` 用既有有界存在消去，并从参数类型提取 let 定义。
- `Substitution.Algebra` 增补自由槽/约束槽的尾映射定理，三个序列模块复用通用
  弱化与开槽合同。替换语义统一在入口分派恒等/显式映射；量词分支直接使用环境提升。
  Henkin 公式消去、支持集和 Project 重命名复用项级合同及推广上下文后的归纳。
- 搜索完备性通过精确编码等式连接 `SyntaxNatCoding` 的通用单射性，删除第二套
  编码单射归纳。二十类命题公理共用任意公式参数列的查询完备性。其通用实例先固定
  参数再匹配目标，避免类型推断提前展开检查器；原心跳预算没有增大。
- `UniformFrameExtension.refl` / `trans`、`UniformSoundExtension.refl` 统一 Skolem 模型
  扩展的恒等和复合。复合明确消费新鲜变量与函数界的单调性，保留环境、类型及
  FOOL/高阶合同，合取和析取不再分别装配相同结构。

### 实际减量

下表只统计本轮修改模块；新增公共接口的行数已计入相应分组。

| 分组 | 模块数 | 修改前 | 修改后 | 净减 |
| --- | ---: | ---: | ---: | ---: |
| 一阶语法、Henkin 与替换 | 8 | 7,060 | 5,814 | 1,246 |
| Quine quotation 与变换 | 12 | 9,181 | 7,161 | 2,020 |
| ProofT 承载与见证 | 7 | 6,411 | 5,041 | 1,370 |
| 自动化与 Skolem 扩展 | 3 | 3,167 | 2,721 | 446 |
| 修改模块合计 | 30 | 25,819 | 20,737 | **5,082** |
| 全仓 Lean 源码 | 805 | 234,597 | 229,515 | **5,082** |

非空行从 221,503 降到 216,425，净减 **5,078**；原始源码字节从 11,219,711 降到
10,984,013。Python/Shell 仍为 837 行，全部代码为 **230,352 行**；严格低于 20 万还需
净减至少 **30,353 行**。相对最初 241,759 行的架构精简起点，Lean 累计净减 12,244 行。

### 验证、审计与归档

- 最终 `scripts/check-all.sh`：807 个全源任务、320 个扫描工具任务通过，零错误、
  零警告；包含全部独立模块和 `PureRosserComplete`。初次检查暴露的查询实例推断超时
  已通过固定实例边界修复，沿用原 1,000,000 心跳预算，修复后该模块构建为 8.7 秒。
- 基线中的 **13,501 个既有源码公开声明**均保留：13,485 项编译类型的原始表达式相同，
  16 项只因相互递归分组而改变自动生成的 binder 名称；仅去掉绑定变量显示名后，
  类型表达式逐项相同。**6,949 项既有数据定义**的原始编译表达式全部相同。
- 13,500 项既有声明的公理依赖集合相同；`term_two_weakenBound_substitute_newest`
  因复用通用槽位代数，从无公理依赖变为引用既有 `propext`、`Quot.sound`。没有增加
  对象语言公理、Lean 公理常量或原生验证公理；审计范围内全仓公理并集保持。
  `PureRosser.agreement`、`PureRosser.independent` 的类型、依赖集合逐项保持。
- 最终审计共 13,662 项，另外包含 17 个本轮新增公开接口和 144 个补充纳入的既有
  声明；均无 `sorryAx`。后两组不冒充拥有逐项旧编译基线。类型规范化仅忽略 binder
  名称，不删除常量、类型参数、前提、量词或元数据来制造相等。
- 没有新建样本证明模块。所有实际定义、定理和消费者均通过正常 Lean 构建验证。
  `git diff --check` 按仓库 CRLF 约定通过。

本轮临时基线、逐文件统计、全库构建日志与编译环境审计位于父目录 `cleanup-5000/`，
不进入源码包。最终从实际工作树打包源码、配置和工程文档，排除 Git 元数据、构建产物、
运行时及临时文件；按用户要求原位更新 Google Drive 的 `YesMetaZFC-source.zip`。
没有创建 Git 提交或推送。

本批停止于 5,000 行里程碑。后续仍可检查有限算术轨迹的统一递推合同、序列前缀唯一性
与函数外延、scope 构造组合以及 CNF 扩展复合；这些候选未计作已完成减量。

## 自由清理第二轮：有限图、环境传输与状态不变量（2026-09-09）

本轮从上一轮已验证的 229,515 行重新计数，持续清理至净减 **5,006 行**；上一轮
5,082 行不计入本轮收益。修改 45 个既有 Lean 模块，新增一个被实际消费者使用的
`FiniteSequenceExtensionality` 模块，没有删除源码模块。

### 公共接口与实际迁移

- `ArithmeticTrace` 提供任意标准数码数组的取值、映射和逐步规格接口
  `standard_numeral_trace_value`、`standard_numeral_trace_mapping`、
  `standard_numeral_trace_step`。加法、乘法、幂轨迹共用有限索引枚举与见证块装配。
- `FiniteSequenceExtensionality` 中的 `function_equality_of_finite_values` 从原函数性、
  有限定义域和每个标准位置的取值推出与规范序列相等。原公开函数外延定理保留名称，
  移到公共模块；自然数序列和证明序列的 replay 都消费同一有限图接口。
  `NatSequenceInversion` 的前缀唯一性强化归纳结果，一次携带前缀编码与末项；
  `nat_sequence_step_value_elim` 统一逐步枚举消去，`sequence_trace_numeral_data`
  统一从定义域、编码界及末值条件提取有限取值事实。原内部自然数条件和编码均保留。
- `guarded_conj_congr_m` 统一带 guard 的双向合取传输；无序对并集规格共用成员
  条件转换。`IntrinsicQuantifier` 复用开槽与弱化代数，见证检查的双层/四层消去
  复用已有量词块接口，保留原公开陈述中的局部参数定义。终端不匹配证明依次
  复用标准序列、证明行和行列表的公共结果，不重复做末位置取值与等式上下文传输。
- Henkin 的项与参数列真正相互归纳；降低/嵌入往返、公式语义、规范模型求值
  共用同一结构证明。Hilbert 公理降低按共享参数形状分组，具体公理构造仍分别验证。
  `SyntaxNatCoding.formula_encode_injective` 统一标签区分与载荷单射性；编码定义不变。
- `CoreNormalForm.Env.ext` 与高阶环境外延接口把完整环境语义合同归结为环境相等；
  `skip_push`、`drop_push`、`insertAt_push` 集中处理量词下的槽位变换。
  scoped 环境一致性、自由参数一致性及函数覆盖保持性共享项/公式/参数列归纳。
  自由参数支撑的成员刻画和最大编号界的等价刻画，将数值界保持性接到同一环境
  一致性定理；原 `maxFVarSucc` 消费者不再另做一次语义归纳。
- `Definition.BuildState.buildCore_invariant` 将新定义步骤的状态不变量推广到
  完整构建，定义包含性与新鲜性成为实例。`buildCore_from_empty_sound` 一次给出
  根引用与生成子句的语义合同。`clauseOfRefsAux_satisfies` 和 `clausesOfRefs_satisfies`
  覆盖任意长度的引用列，原一/二/三引用定理保留并复用这些接口。
  CNF、反前束化与 FOOL 变换算法的数据定义均未因证明合并而改写。
- 规范化的空操作语义直接按公式结构终止，删除私有大小度量及重复终止义务；
  DAG 编译、替换、重命名及 Avatar 语义按连接词/量词家族共享递归证明。
  仍使用明确的递归重写控制展开成本，没有提高证明心跳预算。
- `FirstOrderDerives` 增强现有上下文消费：纳入合法的局部命题 let，先消费表头，
  共用弱化和消去步骤，逐级增加搜索深度至原有上限。类型视图保留原表达式隐参数，
  只在需要时做定义展开对齐。Quine 的 scope 构造、有限序列语义和见证检查实际消费
  改进后的 `derive_prop`；没有把未闭合的批量试验或测试样本留在源码中。

### 实际减量

| 分组 | 修改/新增模块数 | 修改前 | 修改后 | 净减 |
| --- | ---: | ---: | ---: | ---: |
| 自动化与规范化 | 16 | 13,056 | 10,968 | 2,088 |
| 一阶/高阶逻辑与基础集合规格 | 9 | 8,074 | 7,334 | 740 |
| Quine 构造 | 7 | 4,327 | 3,940 | 387 |
| ProofT 序列、轨迹与见证 | 14 | 7,128 | 5,337 | 1,791 |
| 合计 | 46 | 32,585 | 27,579 | **5,006** |

新增公共代码的成本已扣除。全仓为 **806 个 Lean 文件、224,509 行、211,291 个
非空行、10,733,382 字节**；非空行净减 **5,134**。Python/Shell 仍为 837 行，全部
代码 **225,346 行**，严格低于 20 万仍需净减至少 **25,347 行**。相对最初 241,759 行
的架构精简起点，Lean 累计净减 **17,250 行**。没有把文档、空行压缩或源码移出统计
范围作为达到里程碑的手段。

### 验证与归档

- 最终 `scripts/check-all.sh`：808 个全源任务、320 个扫描工具任务通过，零错误、
  零警告，覆盖全部独立模块与 `PureRosserComplete`。最终源码冻结后重新运行完整
  检查，恢复的公开接口和终端公共证明均已验证；没有增加证明心跳预算。
- 基线中的 **13,662 个既有源码公开声明全部保留**。13,658 项编译类型原始表达式
  相同；4 项仅因相互递归分组而改变自动 binder 名称，忽略绑定变量显示名后类型
  逐项相同。未删除类型常量、前提、量词或元数据来制造相等。
- **6,955 项既有数据定义中，6,953 项原始编译表达式相同**。`HilbertBaseAxiom.lower`
  的装配表达式改变，但已将旧函数复制到临时审计中，用 Lean 对任意输入逐构造证明
  新旧返回的完整 `Lowered` 证书相等（每个分支 `rfl`）；并非只比较输出公式。
  另一项为按计划改进的自动化入口 `FirstOrderDerives.try_close`。
  没有改变对象理论、quotation、规范化算法或 Rosser 句子的数据含义。
- 13,602 项既有声明的公理依赖集合相同；60 项因复用公共接口而新增对项目既有
  `propext`、`Quot.sound`、`Classical.choice` 的部分引用，未引入新的原生验证公理。
  审计范围内全仓公理并集保持，`PureRosser.agreement`、`PureRosser.independent`
  的类型及完整依赖集合逐项相同。没有新增对象语言公理、Lean 公理常量或 `sorryAx`。
- 最终审计共 **13,893 项**，另外覆盖 27 个本轮新增公开接口与 204 个补充纳入的
  既有声明；这些新增覆盖项没有冒充拥有旧编译基线。选择器补充覆盖相互归纳块内
  的缩进声明。审计曾发现一个误删的公开行码辅助定理，已按原声明和证明恢复，
  最终无缺失声明，净减统计已扣回恢复成本。
- `prove_auto_sweep --help` 与一次实际目标扫描正常运行。目标
  `YesMetaZFC.SetTheory.Ordinal.transitive` 仍返回 `not_closed`、`backend=unknown`，
  原因是尚无可用 `GoalRequest`；这是既有前端覆盖边界，不计作自动证明成功。
  没有新建永久样本证明模块；`git diff --check` 按仓库 CRLF 约定通过。


本轮的原始基线、逐文件统计、构建日志和编译环境审计位于父目录
`cleanup-5000-next/`，不进入源码包。源码包从实际工作树生成，包括全部未提交的
已验证修改及工程文档；排除 Git 元数据、运行时、构建产物及临时审计文件。
达到里程碑后，按用户要求原位更新同一个 Google Drive 源码包一次；无 Git 提交或推送。

### 后续边界

有限轨迹、前缀唯一性、有限函数外延、scope 组合和 CNF 状态合同已有本轮成果，
后续不得再次作为未实施整组收益累加。下一轮先检查公共合同在其余消费者中的
实际覆盖，按净收益决定是否继续迁移；量词引入和大型纯扩张语义仍须保留明确的
变量、类型与模型阶段边界。扫描器对部分集合论终点的前端接入问题另行处理，
不能把扫描未闭合误报为目标不成立。

## 发布累计工程精简节点（2026-09-09）

用户已授权将当前稳定节点发布到 `lanxinge/YesMetaZFC` 的 `main` 分支。此前暂缓
提交的工程清理、槽位代数、Quine、ProofT、规范化及两轮自由清理一并纳入，父基点为
`b36e2434459fa71bd6d5ff91f0882058a9746399`。上文“未提交或推送”均记录对应批次
完成时的历史状态，不再表示当前发布节点仍须暂缓。

发布前核对全部 823 个文件与已验证的 Drive 源码包一致；随后仅更新 AGENTS.md、
RESTORE.md 和本记录的发布状态。806 个 Lean 文件、配置及脚本均未改变，沿用
最终 808 个全源任务、320 个扫描工具任务和公开声明审计的验证结果。

## 性能优化的后续事项

1. 将 `PureLogicalSchemaSets.condition_bounded` 的语义形状转换与具体扩张分开，
   减少 `change` 比较大型具体表达式。
2. 优化 `PureFinalSyntax` 中求值公理的参数顺序转换，复用一般模板语义接口。
3. 对 `PureLogicalSchemaStage`、`PureSyntaxTransform`、`PureFinalConstructions`
   等剩余高耗时模块做声明级测量，再决定重构边界。
4. 检查扫描器对集合论语义终点的 `GoalRequest` 接口覆盖，区分前端未接入和搜索未闭合。

逐模块测量可运行：

```bash
time lake env lean --profile -Dprofiler.threshold=50 \
  YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSyntaxFixedPoint.lean
```

只需声明级标签时，可附加 `-Dtrace.profiler=true`
`-Dtrace.profiler.threshold=1000000 -Dtrace.Elab.async=true`。
不要在日常构建中开启完整 `Meta.isDefEq` 或 `simp.rewrite` 追踪；
大型公式会使诊断输出自身成为明显负担。
