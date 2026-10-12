# 轻量策略与模块边界

主项目的证明自动化入口为 `YesMetaZFC.Tactic`，提供命题派生、全称闭包、
公式闭合性、理论包含和有限公理基模型装配。受控定义约化 `deep_rfl` 保留领域入口。
策略的调用方式和适用条件见 [ENGINEERING.md](ENGINEERING.md#轻量证明派生)。

## 模块职责

| 目录或模块 | 内容 |
| --- | --- |
| `Tactic/`、`Tactic.lean` | 轻量策略及聚合入口 |
| `Logic/FirstOrder/FormalSystem/Arithmetic/` | 对象编码、内部轨迹、反射与对角化 |
| `Logic/FirstOrder/FormalSystem/QuineEncoding/Induction` | quotation 构造封闭性归纳 |
| `Logic/FirstOrder/FunctionFreeDelta0` | 无函数 Δ₀ 片段 |
| `Model/FirstOrder/FormulaBinderSemantics` | 公式 binder 语义 |

数学声明使用各自既有命名空间；策略使用 `Tactic` 命名空间。
`derive_prop.maxFuel` 和 `derive_prop.maxFacts` 控制命题派生的资源。
通用搜索证明器、调度与注册机制、专用回放运行时和扫描器已移出主项目；
旧模块路径不提供兼容转发。移出过程可查 Git 历史，不作为日常构建前置。

## 验证与审计

使用 `lake --wfail build` 验证默认入口，`python scripts/lean_cache.py build`
检查全部独立 Lean 模块；`--native` 另构建全部原生对象、静态库与共享库。
构建、缓存和 CI 只依赖当前仓库配置，不依赖旧证明器归档或扫描器。

公理与数据边界见 [UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md#当前-lean-公理边界)。
审计模块路径必须指向实际声明所在位置；例如 Kuratowski 配对接口位于
`YesMetaZFC.SetTheory.Kuratowski`，声明命名空间为 `YesMetaZFC.SetTheory`，
由 `scripts/check_forcing.py` 按真实端点检查。
