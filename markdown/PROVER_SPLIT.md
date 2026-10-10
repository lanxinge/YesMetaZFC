# 通用证明器拆分与轻量策略

主项目已移出 `prove_auto`，保留 `YesMetaZFC.Tactic` 中的命题派生、全称闭包、
公式闭合性、理论包含和有限公理基模型装配；受控定义约化 `deep_rfl` 保留原领域入口。

## 源码留档

本地留档位于主仓库上一层的 `../YesMetaZFC-prove-auto-archive/`。
`source-before-split.zip` 保存基点 `60d081445e7f9616f666b5ddc9f35407ce959a88`
对应工作区的完整跟踪源码；`removed/` 保存 149 个移出文件。
清单中记录完整快照与逐文件 SHA-256，源码均已逐项比对。

留档包含原证明器的数学依赖与构建配置。移出的源码树本身未包装成独立可构建软件包，
恢复研究应在另一个目录解压完整快照。主仓库的构建、缓存和 CI 不读取留档。

## 当前模块边界

- `Tactic/`：六个轻量策略模块；聚合入口为 `Tactic.lean`。
- `Logic/FirstOrder/FormalSystem/Arithmetic/`：对象编码、内部轨迹、反射与对角化等数学内容。
- `Logic/FirstOrder/FormalSystem/QuineEncoding/Induction`：quotation 构造封闭性归纳。
- `Logic/FirstOrder/FunctionFreeDelta0`：无函数 Δ₀ 片段。
- `Model/FirstOrder/FormulaBinderSemantics`：公式 binder 语义。

101 个数学模块保留原声明、参数和证明，仅迁移模块位置；数学声明的既有命名空间继续使用。
六个策略模块使用 Tactic 命名空间；命题策略的资源选项改为 `derive_prop.maxFuel`、
`derive_prop.maxFacts`。旧模块路径无转发文件。

11 处原策略调用已直接调用原有数学接口或局部证明，包括序数成员、后继和并集唯一性、
共尾度唯一性，以及序列追加的分支事实。全部定理保持原参数与结论。
领域正规化及 HR 注册、集合论 provider、专用 interned 运行时和扫描器目标随证明器移出。

Cantor 正规形基础公式及语义接口拆到 `CantorNormalForm/Basic`；
主体继续包含构造和唯一性证明。此拆分不改变公开数学声明。

## 验证口径

默认入口使用 `lake --wfail build`；`python scripts/lean_cache.py build`
继续检查所有独立 Lean 模块。`--native` 另构建全部模块原生对象、静态库与共享库。
缓存及 CI 的当前目标不含旧扫描器。历史文档里的扫描器数据只对应所记录的旧源码基点。

本次在 Windows、Lean 4.33.1、4 线程下完成以下验证：

- 全部 1750 个 Lean 模块及其原生对象、静态库、共享库构建通过，零错误、零警告。
- 单模块最长已记录耗时 40 秒；所有源模块少于 2000 行，最长为 1995 行。
- 缓存／发布脚本的 19 项测试和算术数据边界的 5 项测试通过。
- 算术审计覆盖 96 个模块、1165 个声明，另检查 439 个公开声明；只见既有标准公理依赖。
- 11 个迁移定理的参数与结论保持原文，公理依赖检查未见 sorryAx 或证明器回放依赖。
  原集合论句法检查的 native_decide 依赖仍保留，详见留档验证日志。
- 101 个数学模块除导入路径外正文保持一致；149 个移出文件逐文件 SHA-256 与快照一致。
- 当前源码无旧证明器调用、属性注册或模块导入，文档链接检查通过；静态库及链接输入未含移出引擎。

扣除模块搬迁，Lean 源码新增 662 行、修改删除 707 行，移出 67440 行，净减少 67485 行。
构建日志、公理审计和源码比较记录位于留档目录的 `validation/`。

## CI 审计端点同步

Kuratowski 配对接口已位于 `YesMetaZFC.SetTheory.Kuratowski`，声明命名空间为
`YesMetaZFC.SetTheory`。力迫审计显式包含此公共模块，并按该命名空间检查
`Pair_d`、`KPair_d`、`kpair_m`、`kpair_convention_l`、`kpair_interpretation_l`。
七组力迫审计、滤子、初等子结构和超幂审计均已通过；原无选择依赖及逐端点公理上界保持不变。
