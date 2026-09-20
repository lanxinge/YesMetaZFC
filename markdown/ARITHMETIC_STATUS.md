# 算术子库接口与来源

本文件记录 Q/PA、Z₂ 核心、已验证的 PA→Z₂ 桥及首批一般算术；其余算术／编码按 [工作规划](ARITHMETIC_PLAN.md) 推进。
验证状态在本文件末尾单列；文件存在本身不是构建通过的证据。

## 入口与理论边界

- `import YesMetaZFC.Logic.Arithmetic`：Q/PA、数码计算、Z₂ 理解与全公式归纳、PA→Z₂ 推导翻译。
- `import YesMetaZFC.Model.Arithmetic`：任意结构、PA/Z₂ 可定义归纳、标准模型、元层一致性及 PA 数域约化。
- 共享语言放 `Logic/Arithmetic/Signature` 与 `Syntax`，不归属于 PA 公理层。
  Q 独立放 `Q/`，实现时据实际复用关系调整了规划中的 `PA/Robinson` 路径。
- 全部模块属于现有 Lake 库，当前全源枚举脚本会覆盖它们；没有嵌套桥工程或独立工具链。

主要公开接口的命名空间及精确作用：

| 命名空间 | 接口 | 范围 |
| --- | --- | --- |
| `Logic.Arithmetic` | `signature_m`、`zero_m/succ_m/add_m/mul_m`、`numeral_m` | 单排序、仅四种函数；没有非逻辑关系 |
| 同上 | `numeral_subst_m`、`numeral_rename_m` | 任意合法 bound/free 上下文和替换／重命名 |
| 同上 | `succ_congr_m`、`add_left_congr_m`、`add_right_congr_m`、`mul_left_congr_m`、`mul_right_congr_m` | 任意理论、任意局部上下文的纯逻辑同余 |
| `Logic.Arithmetic.Q` | `template_m`、`sentence_m`、`theory_m` | 七条实际 Q 公理；模板参数完整闭合 |
| 同上 | `derives_m` 及七个公理实例 | 目标理论显式包含 Q；任意项、自由参数和局部假设 |
| 同上 | `numeral_add_m`、`numeral_mul_m`、`numeral_ne_m` | 对每组外部给定数码产生对象推导；不消费 PA 归纳 |
| `Logic.Arithmetic.PA` | `induction_m`、`theory_m`、`extends_q_m` | Q 加任意带有限数目参数的算术公式归纳模式 |
| 同上 | `induction_derives_m`、`induction_rule_m`、`induction_term_m` | 真正的 `Derives` 结论；规则显式弱化局部上下文，可在任意项处实例化 |
| 同上 | `next_weaken_m` | 后继替换不改变原自由参数 |
| 同上 | `zero_add_m`、`succ_add_m`、`add_comm_m`、`add_assoc_m`、`add_right_comm_m` | 任意 PA 扩张中任意项的一般加法规律 |
| 同上 | `zero_mul_m`、`mul_one_m`、`one_mul_m` | 同范围的乘法左零律与左右单位律 |
| 同上 | `succ_mul_m`、`mul_comm_m`、`mul_add_m`、`add_mul_m`、`mul_assoc_m` | 同范围的一般乘法后继、交换、双侧分配与结合律 |
| `Model.Arithmetic.PA` | 十二条运算定理 | 由对象推导的可靠性得到任意 PA 模型全数域上的等式 |
| `Model.Arithmetic` | `num_l`、`zero_l/succ_l/add_l/mul_l` | 任意预定 universe 的结构，不默认满足 Q/PA |
| 同上 | `next_sat_m`、`induction_sat_m` | 后继替换与归纳模式的逐公式语义对应 |
| 同上 | `induction_m`、`induct_m` | 任意 PA 模型全数域上的可定义归纳；需真实公式及环境 |
| 同上 | `standard_m`、`numeral_eval_m`、`q_models_m`、`pa_models_m` | 实际标准自然数结构和公理模式满足性 |
| 同上 | `q_consistent_m`、`pa_consistent_m` | Lean 元层由标准模型和可靠性得出的无矛盾性，不是对象自证一致性 |
| `Logic.Arithmetic.Robinson` | `base_m`、`parameters_m`、`template_m` | 对任意签名 universe、给定数排序及项构造建立七条数目公理；Q 和 Z₂ 共用 |
| `Logic.Arithmetic.Z2` | `signature_m`、`insert_m`、`next_m` | 最小双排序语言及保留全部原参数的新集合槽／后继替换 |
| 同上 | `number_m`、`extensionality_m`、`set_induction_m`、`comprehension_m`、`theory_m` | 实际闭公理和完整理解模式；没有 BMS 语言检查前提 |
| 同上 | `comprehension_derives_m`、`induction_derives_m`、`induction_rule_m` | 任意 Z₂ 扩张、混合自由参数和局部上下文中的对象推导 |
| 同上 | `induction_congr_m` | 任意理论中，逐点可证等价传输归纳实例；不要求 Z₂ 公理 |
| `Model.Arithmetic.Z2` | `ext_m`、`insert_sat_m`、`comprehension_sat_m`、`comprehension_m` | 任意集域的外延性、见证槽独立性、理解的精确语义与内部集合见证 |
| 同上 | `induction_sat_m`、`induction_m`、`induct_m` | 模型全数域上的公式归纳；宿主谓词版本仍要求实际公式定义 |
| 同上 | `standard_m`、`models_m`、`consistent_m` | Nat 与全部 Nat→Prop 的标准模型；Lean 元层一致性 |
| `Logic.Arithmetic.PA.Translation` | `context_m`、`variable_m`、`term_m`、`arguments_m`、`formula_m` | 保持变量位置及逻辑联结词，数量词只译为数量词 |
| 同上 | `term_rename_m`、`formula_rename_m`、`term_subst_m`、`formula_subst_m` | 任意合法 bound/free 上下文之间的重命名与同时替换保持 |
| 同上 | `formula_instantiate_m`、`formula_abstract_m`、`formula_forall_m`、`formula_close_m` | 实例化、抽象、量化、全称闭包保持；自由顶部实例化和存在量化也有对应接口 |
| 同上 | `logical_m`、`provable_of_axioms_m`、`derives_of_axioms_m` | 原逻辑公理的实际目标证书；给定各公理像可证，可传输任意源数目理论推导 |
| 同上 | `number_image_m`、`induction_image_m`、`axiom_derives_m`、`derives_m` | 已构造 PA 公理像证明，最终定理直接输入 PA 推导，输出 Z₂ 推导；不是未填条件接口 |
| `Model.Arithmetic.Z2` | `reduct_m`、`environment_m`、`term_eval_m`、`formula_sat_m` | 任意双排序结构的整个数域约化，以及逐项／逐公式语义保持 |
| 同上 | `reduct_models_m` | 显式给定 Z₂ 模型性后，得到 PA 全部公理及归纳模式的模型性 |

所有命名空间均带前缀 `YesMetaZFC`。任意模型接口没有标准性或外部幂集假设。
核心不导入 BMS、Mathlib 或集合论模型。PA→Z₂ 桥已经实现；尚无原始递归总性断言。

## 迁移来源与修改

来源仓库：[BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean)。
采用本地 `bm4v` 工作树，Git 基点 `013b0edbb7808bbefa2f2aaa5fc6d700196b3016`；
不假定整个工作树与该提交相同。下列为实际读取文件的原始字节 SHA-256。
来源目录均为 `ConstructibleBridge/BMSConstructibleBridge/`。

| 文件 | SHA-256 |
| --- | --- |
| `SecondOrderSyntax.lean` | `6204ccd8bf29e924a70c679d55170bc281f663ae8c007bc0933bc76c1af63429` |
| `SecondOrderArithmetic.lean` | `e2afb09cc8318a6c15bbfdf8650dff2f878834da53f6b5a1f70311a8ddc6497e` |
| `SecondOrderModel.lean` | `7e9fb58b74ffc73d4ed40ca04a6cc4570fa602a063b43140cdfc380e822f16b1` |

本批不是原文件直接复制：重建独立单排序语言，删除 BMS 扩张符号；用开放模板统一 Q 公理实例化；
将数码结论从固定 Z₂ 背景降低至任意 Q 扩张；将一般归纳独立呈现为 PA 模式；
分离纯逻辑同余与算术公理，模型对应移入 Model；按公开判断重新判定层后缀。
保留原库 Apache-2.0 贡献者通知，见根目录 NOTICE。旧仓库及其公开接口未修改。

Stage 2a 继续改写同一 `SecondOrderArithmetic.lean` 的理解与归纳证明，其来源 SHA 已重新核对。
以 `existsFreeTop/forallFreeTop` 直接构造理解，省去旧版本的独立 bound 替换及等式转换层；
删除原先排除 BMS 符号的 `language_m φ = true` 条件，因为新签名从类型上不含这些符号。
把公式归纳推广到任意理论扩张与局部上下文；标准模型用原生谓词代替 Mathlib Set。
数目公理模板对任意签名及排序 universe 抽取，Q 的原实例证明重新编译；不是维护两份公理列表。
模板接口只生成语法，不给任意传入项构造附加未经证明的替换自然性。

Stage 2b 是针对当前类型化 AST 新写的翻译及语义证明；复用上游替换、Hilbert 核、
局部上下文 discharge 和可靠性，不复制旧桥的扩张语言或另造推导核。
上游 Henkin 嵌入用作结构递归和规则传输的接口参考，但其固定排序扩张不能直接复用于此桥。

## 验收合同

最终结果以真实命令退出码、源码指纹及公理日志为准。开发中的失败日志保留在仓库外，
不得引用某个旧 `.olean` 或失败构建中的局部成功条目宣布整体通过。
本批联合目标为 `YesMetaZFC.Logic.Arithmetic` 与 `YesMetaZFC.Model.Arithmetic`。
公理审计覆盖本批显式公开定义／归纳类型／定理；语义复核另检查模板槽、模式量词、
局部假设新鲜性、内外部自然数和结论层级。尚未运行全仓 CI。

### Stage 1 历史验收（2026-09-20）

以下仅对应第一批源码指纹；当前共享模板已经重构，应以随后 Stage 2a 验收为准。

- 联合 `lake --wfail build YesMetaZFC.Logic.Arithmetic YesMetaZFC.Model.Arithmetic`：46 jobs，退出码 0。
- 13 个新增 Lean 文件，共 499 行（含注释与空行，不含文档和审计脚本）。
- 对 52 个显式公开定义／归纳类型／定理逐项 `#print axioms`，52 项均取得结果；未计入自动生成的实例／recursor。
- 公理依赖的并集仅为 `propext`、`Classical.choice`、`Quot.sound`；无 `sorryAx` 或新自定义公理。
- 新源码静态扫描无占位证明、unsafe、native_decide 或关闭 linter；完整导入闭包不含 BMS、Mathlib、
  ConstructibleUniverse、SetTheory 或具体 ZFC 模型。源码审计前后 SHA-256 相同。
- 语义验收的机器证据包括：七条公理的任意项实例、`induction_sat_m` 的任意结构对应、
  `induction_rule_m` 的上下文合同，以及全公理模式的 `pa_models_m`，不是只验证若干数值样例。

本地证据位于工作区 `outputs/yesmetazfc-arithmetic/`：`stage1-final-build.log`、
`stage1-axioms.log`、`stage1-audit.json` 与可重跑脚本 `audit_stage1.py`。
这些一次性审计材料不放进正式 Lean 源码目录。以上是算术依赖切片的验证，不代表上游全仓 CI。
### Stage 2a 历史验收（2026-09-20）

- 两个聚合入口联合 `lake --wfail build`：53 jobs，退出码 0，没有 linter 警告。
- 当前算术子库 20 个 Lean 文件、952 行，比第一批净增 453 行；最长文件 136 行。
- 92 个显式公开声明逐项 `#print axioms` 全通过；审计并集仅为 `propext/Classical.choice/Quot.sound`。
- 无占位证明、新自定义公理、unsafe、native_decide 或关闭 linter；53 个导入闭包模块无 BMS、
  Mathlib、ConstructibleUniverse、SetTheory、具体 ZFC 模型。未解析为本仓源码的入口仅 `Lean`。
- 源码在审计前后 SHA-256 一致。没有运行全仓 CI，也没有重新认证旧 BMS 仓库。
- 独立复查 Logic 聚合入口的 36 模块导入闭包，没有任何 Model 模块；对象证明层未反向依赖模型语义。
- 当前证据为 `stage2-verified-build.log`、`stage2-axioms.log`、`stage2-audit.json`；
  用 `python outputs/yesmetazfc-arithmetic/audit_stage1.py stage2` 从父工作区重跑审计。
  脚本保留默认 stage1 输出名，但当前验收必须传 stage2，避免覆盖历史证据。

语义复核的具体边界：

1. 理解正文 `φ : Formula signature_m [] (.num :: Δ)` 的 Δ 是任意混合排序列表，
   AST 的数／集量词不受限制。`insert_sat_m` 对每个候选 X 证明原 φ 的真值不依赖新集合槽。
2. `axiom_m` 仅有七条数目公理、外延、集合归纳与完整理解；全公式归纳确由理解和集合归纳导出。
3. `induction_congr_m` 与最终归纳规则都是 `Derives`；没有借标准模型真值、完备性或反射替代对象证明。
4. 任意模型语义遍历整个内部数域及集域。`induct_m` 仍保留逐点公式定义前提，不可用于任意额外宿主谓词。
5. 标准模型检查涵盖整个理解模式，不是有限样例。元层一致性不等于对象自证一致性，
   双排序一阶语义不自动成为 Full 二阶语义的完备性。

### Stage 2b 当前验收（2026-09-20）

本批完成 PA→Z₂ 的语法／推导翻译及模型约化。Stage 2 的全部五项合同现已满足。

- 联合构建 `lake --wfail build YesMetaZFC.Logic.Arithmetic YesMetaZFC.Model.Arithmetic`：57 jobs，退出码 0，无 linter 警告。
- 当前算术子库 24 个 Lean 文件、1,545 行；本批净增 593 行，最长模块 242 行。
- 142 个显式公开声明公理审计全通过；依赖并集仅 `propext/Classical.choice/Quot.sound`，无占位证明或新自定义公理。
- 57 个模块的完整导入闭包不含 BMS、Mathlib、构造宇宙、SetTheory 或具体 ZFC 模型；外部入口仅 `Lean`。
- 审计前后源码 SHA-256 一致。当前证据为 `stage2b-final-build.log`、`stage2b-axioms.log`、`stage2b-audit.json`。
  在父工作区运行 `python outputs/yesmetazfc-arithmetic/audit_stage1.py stage2b` 重跑当前审计，不覆盖历史批次。
- 没有运行全仓 CI，没有提交或推送，没有改动旧 BMS 源码。

本批语义审查：

1. `context_m` 逐槽保留参数位置，`formula_m` 保留全部逻辑联结词；源数量词不会被译为集合量词。
2. 重命名、bound/free 同时替换、提升、实例化、量词抽象及闭包均有一般定理，不以样例验证代替。
3. `logical_m` 构造每一种原逻辑公理的目标证书；`provable_of_axioms_m` 遍历全部六种 Hilbert 构造。
   `axiom_derives_m` 实际填满 PA 公理像，`derives_m` 保留任意局部上下文。未使用完备性、模型真值反射或新公理。
4. `reduct_m` 对任意 carrier universe 的结构直接保留整个内部数域，`formula_sat_m` 不要求 Z₂ 公理；
   最终 `reduct_models_m` 才使用 Z₂ 模型性和已证明的 PA 公理像。没有偷换成标准自然数。
5. 这是 PA 在 Z₂ 中的正向解释；没有反向保守性、Full 二阶完备性或对象自证一致性声明。

### Stage 3a 验收（2026-09-20）

本批完成一般算术的首个切片，不把整个 Stage 3 标为完成。

| 接口 | 已完成合同 |
| --- | --- |
| `PA.next_weaken_m` | 归纳变量替为后继时保留原项的所有自由参数 |
| `PA.induction_term_m` | 真实公式归纳后在任意项处实例化，局部上下文按新变量弱化 |
| `PA.Addition` | 任意 PA 扩张中的 `succ_add_m`、`add_comm_m`、`add_assoc_m` |
| `PA.Multiplication` | 同范围的 `zero_mul_m`、`mul_one_m`、`one_mul_m` |
| `Model.Arithmetic.PA.Operations` | 上述六条及已有左零加法律在任意 carrier universe 的 PA 模型中成立 |

复用来源：旧 `BMSConstructibleBridge/SecondOrderNumbers.lean` 与
`SecondOrderMultiplication.lean` 的数学归纳路线。没有搬入旧模型假设、纯语言布尔 guard、Mathlib 或 BMS 符号。
前者 SHA-256 为 `c70af63162d9da17353c35fd5599d53ea4d9e3b4c71edd10f92b376fd5c6278f`；
后者为 `d95f8e28ecbb5b94795d1803f78a027e18f37a137048d4adfeff75a661fbf6e0`。
不同于旧库主要提供的语义规律，本批先构造 `Derives`，再通过可靠性获得任意模型结果。
乘法单位律中的左单位律直接公式归纳，不借用尚未实现的一般乘法交换律。

验收证据仍位于父工作区 `outputs/yesmetazfc-arithmetic/`：

- `stage3a-combined-first.log`：两个聚合入口联合构建，61 jobs，退出码 0，零警告。
- `stage3a-axioms.log`／`stage3a-audit.json`：159 个公开声明全通过；依赖并集仅
  `propext/Classical.choice/Quot.sound`，无占位证明、新自定义公理或关闭 linter。
- `stage3a-consumers.lean`／`stage3a-consumers-checked.log`：实际调用 PA→Z₂ 翻译传输新的交换律，
  并在任意 Z₂ 模型数域约化上使用结合律；退出码 0、无诊断输出。测试不进入正式库源文件。
- 当前 27 个 Lean 文件、1,791 行，比 Stage 2b 净增 246 行；最长模块仍为 242 行。
- 61 个模块导入闭包无 BMS、Mathlib、构造宇宙、SetTheory 或具体 ZFC 模型；外部入口仅 Lean。
  审计前后源码指纹一致。复跑审计使用 `audit_stage1.py stage3a`，不要覆盖旧批次记录。
  单独检查 Logic 入口的 42 模块依赖闭包，没有任何 Model 导入。
- 语义复核：归纳对象是具体公式；原参数通过 `weakenFree` 和 `next_weaken_m` 保持；
  输入是任意项，不限定为数码。纯逻辑同余无需 Q，Q 递归方程继续只要求 Q，新增一般规律显式要求 PA。
  任意模型结果只用已证明推导的可靠性，不重做宿主任意谓词归纳。
- 未运行全仓 CI／native 验证，未提交或推送；旧 BMS 源码未修改。

### Stage 3b 验收（2026-09-20）

本批完成一般乘法规律；序关系、最小化与内部编码仍未实现，不将整个 Stage 3 标为完成。

- `PA.Multiplication` 新增 `succ_mul_m`、`mul_comm_m`、`mul_add_m`、`add_mul_m`、`mul_assoc_m`。
  全部结论为任意 PA 扩张、自由参数、局部上下文和输入项下的 `Derives`。
- 四条规律通过真实公式归纳建立；`add_mul_m` 由交换律及已证分配律组合。
  `PA.add_right_comm_m` 组合已有加法规律并实际用于乘法后继步，不再单独归纳。
  新 `mul_right_congr_m` 与已有同余接口一样，不要求 Q 或 PA。
- `Model.Arithmetic.PA.Operations` 新增五条同名任意模型结论，仅消费对象推导的可靠性。
  不对内部数域作宿主 Nat 归纳，不增加标准性、模型存在性或 Z₂ 前提。
- 来源继续采用 Stage 3a 所列 `SecondOrderMultiplication.lean` 的数学路线；其原始 SHA-256 已复查未变。
  迁入后改为句法证明优先，不搬入 donor 的模型背景或 BMS 依赖。
- 两个算术入口的联合构建通过：61 jobs，退出码 0，零警告。首轮证据为 `stage3b-first-build.log`；
  注释修订后的最终证据保存为 `stage3b-final-build.log`，以最终源码指纹为验收对象。
- 当前 27 个 Lean 文件、1,965 行，比 Stage 3a 增加 174 行；最长模块仍为 242 行。
  171 个公开声明的公理审计通过；依赖并集仅 `propext/Classical.choice/Quot.sound`。
  `stage3b-axioms.log`／`stage3b-audit.json` 记录当前指纹，复跑使用 `audit_stage1.py stage3b`。
- `stage3b-consumers.lean`／`stage3b-consumers-checked.log` 实测三项调用：分配律和结合律的 PA→Z₂ 推导传输，
  以及任意 Z₂ 模型数域约化中的乘法结合律。退出码 0，无诊断；这些测试不进入正式库。
- 仍仅验收算术依赖切片，未运行全仓 CI／native，未提交或推送，未修改旧 BMS 仓库。

### Stage 3c 首批验收（2026-09-20）

- `Logic.Arithmetic.Order` 用内部差值存在量词定义 `le_m`，以 `le_m (succ_m s) t` 定义 `lt_m`；
  提供重命名、弱化和存在见证的引入／消去接口。没有扩张语言的非逻辑关系符号。
- `Q.le_refl_m` 只要求 Q；`PA.zero_le_m` 和 `PA.le_trans_m` 要求 PA。
  传递性先后引入两个新鲜内部见证，并用加法结合律合成它们；不限制见证为外部数码。
- `Model.Arithmetic.le_sat_m`／`lt_sat_m` 对任意结构和 bound/free 环境给出精确语义，
  不预设模型的序性质。消去、反对称性、全序性和最小化仍未完成。
- 两个聚合入口联合构建通过：65 jobs、退出码 0、无警告。31 个 Lean 文件共 2,115 行；
  186 个显式公开声明公理审计通过，依赖并集仅 `propext/Classical.choice/Quot.sound`。
  无禁止依赖／占位证明，审计前后源码指纹相同。证据为 `stage3c-final-build.log` 和 `stage3c-audit.json`。
- 可复跑检查已进入 `scripts/check_arithmetic.py`，现有 CI 在全源构建后执行它。
  本地脚本运行通过；另验证遗漏报告、额外公理和 Lean 非零退出码都会拒绝验收。
  脚本检查公开声明的传递公理依赖和分层依赖，不替代数学语义审查。
- 本地全源枚举确认包含新增模块，但完整构建提前中断；不宣称全仓／native CI 已通过。

### Stage 3d 验收（2026-09-20）

- 对象层新增：`PA.Cancellation` 的左右消去和零和定理、`PA.le_antisymm_m`；
  `PA.StrictOrder` 的后继保持／反映、严格序蕴含非严格序、严格传递与不可自返性。
  Q 单独提供 `le_succ_m` 和 `lt_succ_m`，不为这些弱结论要求 PA。
- 模型层新增七条任意 Q 模型运算接口、PA→Q 模型限制、PA 消去与偏序规律。
  `PA.LinearOrder.le_total_m` 用含数量词的实际公式归纳证明全序性。
- `Model.Arithmetic.PA.minimum_m` 对任意有限参数上下文 Δ、公式 φ 和环境 η，
  从 φ 定义的数类非空推出内部最小元。新界变量通过提升重命名插入，证明原参数值不变。
  不消费集合参数、外部良基性或任意宿主谓词归纳；全序性和最小元尚无独立 `Derives` 版本。
- 复用旧库 `SecondOrderOrder.lean` 和 `SecondOrderMinimum.lean` 的数学路线，
  SHA-256 分别为 `2246e4bbe577a9ac4c4d115806d39ba01cb1c03c640f0b0d7873d84bc3a4a817`、
  `2131648443f2965c3e542f13b9368a896b263002fd41aec6e26efa461aa81e44`。
  最小元从固定 Z₂ 集合成员关系推广成任意 PA 公式；没有复制旧类型类、Mathlib 或语言布尔 guard。
- 两个入口联合 `--wfail` 构建通过：72 jobs、退出码 0、无警告；38 个 Lean 文件共 2,587 行。
  224 个显式公开声明公理审计全通过，依赖并集仍仅三项标准公理；源码指纹前后一致。
  证据为 `stage3d-final-build.log`、`stage3d-axioms.log`、`stage3d-audit.json`。
- 验证范围仍为算术切片，尚无全仓 CI 通过结论。首批本地提交为 `acaa16c`；
  上传采用个人 fork 的 `feat/arithmetic-theories` 分支及上游 PR，未直接修改上游主分支。

### 后续：最小化推广与内部编码

核心可作为第一批贡献通过个人 fork 的独立分支提交上游 PR；用户已授权此流程，内部编码不阻塞核心交付。

1. 把可定义最小化推广到 Z₂ 混合数／集参数，并复用已经验证的 PA 数域约化和序规律。
   不把 PA 公式版本误称为包含集合参数的 Z₂ 完整版本。
2. 补全全序性和最小化的对象推导接口；所有归纳保留真实公式、参数和新鲜性。
3. 之后才确定配对／β 编码；模型内部长度不换成宿主 Nat 或有限列表。
   超过未提交 3,000 行门槛前完成当前批次验收并提交；不直接推送上游主分支或自行合并 PR。
