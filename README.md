# YesMetaZFC

Lean 4 中的一阶逻辑、集合论与元数学形式化项目，仅依赖工具链自带的 Lean / Std。
当前已有裸 ZFC 上的具体 Rosser 独立句：`PureRosser.independent` 仅假定裸 ZFC
一致，推出当前纯隶属闭句及其否定均不可推导；`PureRosser.agreement` 已有实际证明。

## 环境与构建

工具链固定为 **Lean 4.33.1**，见 [lean-toolchain](lean-toolchain)。在项目根目录运行：

```bash
lake --wfail build
bash scripts/check-all.sh
```

全源脚本需要 Bash 4 或以上，覆盖默认入口未导入的独立模块与 `prove_auto_sweep`，
warning 会使检查失败。工具链恢复见 [RESTORE.md](RESTORE.md)。

## 基础设施导航

| 要做的工作 | 入口 |
| --- | --- |
| 找到终局定理与准确的数学结论 | [TROPHIES.md](TROPHIES.md) |
| 复用替换、见证块、Quine、有限序列与自动化证明 | [ENGINEERING.md](ENGINEERING.md) |
| 使用自然数证明证书、当前 quotation、模式或整树检查器 | [NAT_DECODING.md](NAT_DECODING.md) |
| 使用纯定义、内部递归、阶段扩张和原规格 | [ELIMINATION.md](ELIMINATION.md) |
| 查 119 条公理证明、内部模型对应及 Δ₀ 边界 | [UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md) |
| 修改源码时的约束和命名 | [AGENTS.md](AGENTS.md)、[ProofNaming.md](ProofNaming.md) |

文档按接口职责维护；完成的计划不再逐轮追加，过程记录可从 Git 历史查看。
当前重构目标是用底层公共证明消除上层重复义务，使全部代码严格低于 200,000 行。
规模口径及仍可推进的方向集中于 [ENGINEERING.md](ENGINEERING.md)，文档减量不计入代码指标。
