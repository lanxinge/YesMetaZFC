# 算术子库接口与来源

Q、PA、Z₂ 核心、内部有限编码和逐程序原始递归表示已经实现。
本页是接口导航；历史分批记录保留在 Git 历史，扩展边界见 [工作规划](ARITHMETIC_PLAN.md)。

## 导入与分层

- `YesMetaZFC.Logic.Arithmetic`：最小签名、公理模式、对象推导、PA→Z₂ 翻译和程序图编译。
- `YesMetaZFC.Model.Arithmetic`：任意模型语义、标准模型、内部编码、程序总性及 Z₂ 内部函数图。
- 完备性及下列 `Provability` 模块按需独立导入，不进入上述核心入口。
- 所有文件属于同一个 Lake 库、同一 Lean 4.33.1 工具链，没有嵌套桥工程或外部包依赖。
- Logic 不依赖 Model；算术闭包不导入 BMS、Mathlib、构造宇宙或具体集合论模型。
  程序求值的平方根来自工具链自带的 `Init.Data.Nat.Sqrt.Lemmas`。

以下命名空间省略前缀 `YesMetaZFC`。结构和模型性均显式传入，不设全局模型类型类。

## Q、PA、Z₂

| 命名空间 | 主要接口 | 数学范围 |
| --- | --- | --- |
| `Logic.Arithmetic` | `signature_m`、`zero_m/succ_m/add_m/mul_m`、`numeral_m` | 单排序四函数语言；数码为外部有限后继链 |
| `Logic.Arithmetic.Q` | `theory_m`、`derives_m`、`numeral_add_m/numeral_mul_m/numeral_ne_m` | 七条实际公理；任意 Q 扩张和局部上下文 |
| `Logic.Arithmetic.PA` | `theory_m`、`induction_derives_m/induction_rule_m/induction_term_m` | Q 加所有带有限数参数的算术公式归纳 |
| `Logic.Arithmetic.PA` | 加乘交换／结合／分配、消去、序的对象推导 | 真实 `Derives`，保留任意项和局部假设 |
| `Model.Arithmetic` | `standard_m`、`q_models_m/pa_models_m`、`q_consistent_m/pa_consistent_m` | 实际标准模型；一致性结论位于 Lean 元层 |
| `Logic.Arithmetic.Robinson` | `template_m` | Q 与 Z₂ 共用的七条数目公理模板 |
| `Logic.Arithmetic.Z2` | `theory_m`、`comprehension_derives_m`、`induction_derives_m` | 数／集双排序、外延性、集合归纳、完整理解；由此导出全公式归纳 |
| `Model.Arithmetic.Z2` | `comprehension_m`、`induct_m`、`models_m` | 任意混合公式与参数；另有标准 `Nat, Nat → Prop` 模型 |
| `Logic.Arithmetic.PA.Translation` | `formula_m`、`derives_m` | 全部项、公式、替换、绑定与推导向 Z₂ 的实际翻译 |
| `Model.Arithmetic.Z2` | `reduct_m`、`formula_sat_m`、`reduct_models_m` | 保留整个内部数域的 PA 约化及逐公式语义对应 |

Z₂ 采用多排序一阶演算呈现二阶算术。Henkin 完备性不是 Full 二阶完备性；
任意 Z₂ 模型的集域不默认是外部幂集。PA→Z₂ 翻译不宣称对 PA 保守。
标准模型导出的元层一致性不是对象理论自证一致性。

## 内部算术与有限编码

| 模块／命名空间 | 主要接口 | 保留的条件 |
| --- | --- | --- |
| `Model.Arithmetic.PA.LinearOrder` | `le_total_m`、`lt_succ_m`、`le_cases_m` | 任意 PA 模型全数域 |
| `Model.Arithmetic.PA.Minimum`、`Z2.Minimum` | `minimum_m` | 实际算术／混合公式定义的非空数类 |
| `Model.Arithmetic.PA.Division` | `exists_m/unique_m/exists_unique_m` | 显式非零内部除数；图为 `q*d+r=n ∧ r<d` |
| `Model.Arithmetic.PA.Pairing`、`Unpairing` | `surjective_m/injective_m`、`pair_m/unpair_m` | 固定平方分层配对及全内部数域的双向复合 |
| `Model.Arithmetic.PA`、`Z2` | `bound_m` | 每个内部 i<N 的输出唯一；不要求截段外总性 |
| `Model.Arithmetic.PA.Divisibility` | `exists_m/bounded_m` | 内部截段的正共同倍数；无需宿主阶乘 |
| `Model.Arithmetic.PA.Beta` | `total_m/unique_m` | 模数为 `succ ((succ i)*c)`，包括 c=0 的模 1 情况 |
| `Model.Arithmetic.PA.Beta`、`Z2.Beta` | `sequence_m` | 任意内部长度下可定义有限函数的编码；Z₂ 保留集合参数 |
| `Model.Arithmetic.PA.Beta` | `extend_m/singleton_m` | 重新编码旧前缀和新末值，保留全部旧读值 |

配对约定为 m<n 时 n*n+m，否则 m*m+m+n。它与一阶调度中的二进制配对不同，不能混用。
`Logic.Arithmetic.NatPairing` 给出同约定的可执行宿主配对／解码；
`Model.Arithmetic.PrimitiveRecursive.NatPairing` 证明它与标准结构解释一致及两向复合。

`FiniteRange`、`BetaPrefix` 和 `Sequence` 的公式／语义模板已推广到任意签名 universe 与排序。
PA 和 Z₂ 最终入口用各自的真实公式填满归纳义务；抽象规则的条件没有留给最终调用者补证。
所有长度、模数、界和见证都是模型数，不换成宿主 Nat 或列表。

可选对象推导模块：
`Model.Arithmetic.PA.Provability`、`Z2.Provability`、`PA.PairingProvability`、
`PA.BetaProvability`、`Z2.BetaProvability`。
这些由全部原一阶模型中的结论调用已证完备性，不从标准模型真值反射为可证性。

## 原始递归与表示

| 命名空间 | 主要接口 | 结论 |
| --- | --- | --- |
| `Logic.Arithmetic.PrimitiveRecursive` | `code_m`、`run_l/eval_l` | 零、后继、左右投影、配对、复合、原始递归的有限程序与实际计算 |
| 同上 | `primitive_l`、`primitive_m/complete_m` | 显式七构造闭包与程序的双向对应 |
| 同上 | `graph_m` | 结构递归产生原 PA 签名的图公式，任意 bound/free 上下文 |
| `Model.Arithmetic.PA.History` | `graph_sat_m`、`total_m/unique_m` | β 有限历史、真实公式归纳支持的存在性、确定转移的唯一性 |
| `Model.Arithmetic.PrimitiveRecursive` | `graph_sat_m` | 编译图与内部关系逐构造精确对应 |
| 同上 | `exists_unique_m/total_m/unique_m` | 任意 PA 模型中，每个给定程序对每个内部输入有唯一内部输出 |
| 同上 | `numeral_m/numeral_iff_m` | 任意 PA 模型中标准输入的正确数码输出，排除非标准伪输出 |
| 同上 | `relation_standard_m/standard_m` | 标准模型中编译图恰好表示可执行求值；复用一般数码表示 |
| `Model.Arithmetic.PrimitiveRecursive.Provability` | `total_m/unique_m` | PA 中逐程序可推导总性和函数性；允许理论扩张与局部上下文 |
| 同上 | `numeral_m/evaluates_m/rejects_m` | 任意输出项的数码表示等价式、正确结果可证、错误数码结果可反驳 |
| `Model.Arithmetic.Z2.PrimitiveRecursive` | `graph_m/function_m/unique_m` | 原模型内部集域中的全函数图及其外延唯一性 |

递归步使用输入配对 x,(i,y)。外层按宿主有限程序语法归纳，内部步数则由实际历史公式归纳。
此处 `∀ c : code_m` 不是模型内部所有程序码的统一总性／真值断言。
七构造闭包是明确的配对式原始递归呈现，未接 Mathlib `Nat.Primrec` 的跨库桥；
不引入无界最小化，不宣称已经形式化算术层级、RCA₀/ACA₀ 或 BMS 良序性。

## 来源与重构

来源为 [BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean)，
本地 bm4v 工作树基点 `013b0edbb7808bbefa2f2aaa5fc6d700196b3016`。
该树含本地修改，故以下登记实际读取文件的原始字节 SHA-256，而非只引用提交。
文件均位于 `ConstructibleBridge/BMSConstructibleBridge/`。Apache-2.0 通知保留在根目录 NOTICE。

| 来源文件 | SHA-256 |
| --- | --- |
| SecondOrderSyntax.lean | 6204ccd8bf29e924a70c679d55170bc281f663ae8c007bc0933bc76c1af63429 |
| SecondOrderArithmetic.lean | e2afb09cc8318a6c15bbfdf8650dff2f878834da53f6b5a1f70311a8ddc6497e |
| SecondOrderModel.lean | 7e9fb58b74ffc73d4ed40ca04a6cc4570fa602a063b43140cdfc380e822f16b1 |
| SecondOrderNumbers.lean | c70af63162d9da17353c35fd5599d53ea4d9e3b4c71edd10f92b376fd5c6278f |
| SecondOrderMultiplication.lean | d95f8e28ecbb5b94795d1803f78a027e18f37a137048d4adfeff75a661fbf6e0 |
| SecondOrderOrder.lean | 2246e4bbe577a9ac4c4d115806d39ba01cb1c03c640f0b0d7873d84bc3a4a817 |
| SecondOrderMinimum.lean | 2131648443f2965c3e542f13b9368a896b263002fd41aec6e26efa461aa81e44 |
| SecondOrderDivision.lean | 3ff85c3c439e7cc07cb190f17f35bf15bbd5515dcb61aaf331f495113bf7822c |
| SecondOrderPairing.lean | b097b993919532838766d14c4b9191b69e44bcaa5608c642203c5e7381364e1d |
| SecondOrderPairingBounds.lean | 3a4b774eaae005d7a6956fdf173588f939ea18c3db8b57b620c8c8638ebabcc3 |
| SecondOrderUnpairing.lean | 01833e6004d40497955f95aafcb34a9f26126ba9758be5569a27bf963271054d |
| SecondOrderFiniteRange.lean | ff42f6ad108a80f649e367f4bfa6067c7bd24bf5442a6b106d158d97e99e073e |
| SecondOrderBetaSequence.lean | 1ff262a3ccc9fa007cf56d8d6c6dc6fc19218ca7422fa9febdd280b3dd251eec |
| PrimitiveProgram.lean | 62daaca531f13756d0b72a65e7e693bdc774afa20f8050cc103e0679ab881fc3 |
| PrimitiveHistory.lean | 3e1e9a59e44da145cf8351103b5e03be462ba22bedd9e3345ab24fa82ab6c782 |
| PrimitiveFormulas.lean | 6c619059612cacd63f1fe9ce9e8542e46e5178df99ce5831ea100b894cc8611c |

这是按数学职责重建的迁移，不是整目录复制：删除 BMS 专用符号及纯语言布尔 guard，
数码运算降至 Q，数目归纳与编码降至 PA，含集合参数的接口保留 Z₂。
配对、模逆和 β 证明去除 Mathlib 代数实例；标准序列的宿主列表论证改为内部公式归纳。
图公式、可执行求值、标准正确性、任意模型总性和对象可推导性分别提供。
沿用上游 AST、替换、推导核、可靠性和完备性，不维护第二套逻辑系统。
旧 BMS 仓库及其公开接口未修改。

## 验证

当前算术切片：96 个 Lean 文件，5,433 行（含空行及注释），432 个显式公开声明。
Stage 4a 联合构建 152 jobs，退出码 0、无警告；外部调用测试与两套公理审计通过。
公理依赖并集仅 `propext`、`Classical.choice`、`Quot.sound`，禁止标记／依赖为空，审计前后源码哈希一致。
自动生成的 recursor、构造器和私有声明不单列，但其传递依赖仍由公开声明审计覆盖。

仓库内可复跑命令：

```bash
python scripts/lean_cache.py build --native
python scripts/check_arithmetic.py
lake --no-build exe prove_auto_sweep --help
```

CI 枚举全部独立模块（包括可选 Provability），随后执行算术公理审计。
外部开发证据位于工作区 `outputs/yesmetazfc-arithmetic/`：
`stage4a-final-build.log`、`stage4a-consumer.log`、`stage4a-audit.json`、`stage4a-portable-audit.log`。
一次性消费者与失败日志不进入正式库；历史分批证据仍保留在该目录。

全仓／原生构建已在 Windows 上通过：枚举 1,100 个 Lean 模块及其原生对象，
并校验静态库、共享库与扫描器。原有模块复用上游基点的官方 full 缓存，
先在独立基线核对提交、平台、工具链、源码指纹、归档 SHA-256 及全部 no-build 目标；
确认本次未修改上游原有 Lean 源码或构建配置后，只补入缺失产物，不覆盖本地产物。
新增算术证明在本机编译；这不是一次完整冷构建。证据为 `complete-native-cached-build.log`。

扫描器帮助与单目标扫描均正常退出；实际目标 `SetTheory.Ordinal.transitive` 的结果仍是
`not_closed`，不把工具运行成功解释为新增自动证明能力。19 项缓存／发布脚本测试通过。
本地验证不替代 GitHub 多平台 CI；远端工作流仍受维护者的 fork 运行批准控制。
贡献通过现有上游 PR #1，不直接推送上游 main、不自行合并。
