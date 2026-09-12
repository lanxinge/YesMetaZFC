# YesMetaZFC

[中文](README.md) | [English](README.en.md)

**目标是通用的集合论研究平台。**

YesMetaZFC 在 Lean 4 中发展一阶逻辑、集合论与元数学的形式化基础，
围绕对象语言、形式推导、模型语义和证明自动化积累可复用接口，仅依赖工具链自带的 Lean / Std。
当前已完成裸 ZFC 的具体 Rosser 独立句、D1–D3、Löb 与哥德尔第二不完备定理，
以及使用最终纯公式自身完整 AST 编码的带参数固定点和 Tarski 真不可定义定理。
原生小图双模拟商已实际构造出 ZFC 模型，并在 Lean 元层证明裸 ZFC 一致。
标准布尔名称模型也已对任意完备布尔代数构造并核验原 ZFC，包含全部有限参数模式。
Rosser 独立性与哥二不可证性以裸 ZFC 一致为前提；Tarski 语义版覆盖任意裸 ZFC
模型和每组有限参数赋值。准确的公式范围、编码约定与声明见 [TROPHIES.md](markdown/TROPHIES.md)。

## 环境与构建

工具链固定为 **Lean 4.33.1**，见 [lean-toolchain](lean-toolchain)。在项目根目录运行：

```bash
lake --wfail build
bash scripts/check-all.sh
```

全源脚本需要 Python 3.11 或以上，覆盖默认入口未导入的独立模块与 `prove_auto_sweep`，
warning 会使检查失败。工具链恢复见 [RESTORE.md](markdown/RESTORE.md)。
仅检查全部库模块时，运行 `bash scripts/check-all.sh --library-only`。
模型接口及可信依赖见 [model](YesMetaZFC/Model/README.md)；通用入口为 `import YesMetaZFC.Model`，具体入口为 `import YesMetaZFC.Model.SmallGraph` 和 `import YesMetaZFC.Model.Boolean`。

## 获取构建缓存

安装工具链后，在对应提交运行 `python scripts/lean_cache.py get` 获取编辑和证明开发所需缓存；
使用 `python scripts/lean_cache.py get --kind full` 可同时获取原生库与扫描工具。
CI 为 Linux、Windows、Intel Mac 和 Apple Silicon Mac 构建独立缓存，完成后按提交发布。
平台范围、离线恢复和发布条件见 [CACHE.md](markdown/CACHE.md)。

## 基础设施导航

除各级 README 外，仓库文档统一保存在 [markdown/](markdown/)。

| 要做的工作 | 入口 |
| --- | --- |
| 找到终局定理与准确的数学结论 | [TROPHIES.md](markdown/TROPHIES.md) |
| 复用替换、内部反射、固定点、纯语言传输与自动化证明 | [ENGINEERING.md](markdown/ENGINEERING.md) |
| 使用自然数证明证书、源 quotation、纯公式自身编码与整树检查器 | [NAT_DECODING.md](markdown/NAT_DECODING.md) |
| 使用纯定义、内部递归、阶段扩张和原规格 | [ELIMINATION.md](markdown/ELIMINATION.md) |
| 查 119 条公理证明、元数学终点、模型对应及可信依赖核验 | [UNIFIED_VERIFICATION.md](markdown/UNIFIED_VERIFICATION.md) |
| 修改源码时的约束和命名 | [AGENTS.md](markdown/AGENTS.md)、[ProofNaming.md](markdown/ProofNaming.md) |

文档按接口职责维护；完成的计划不再逐轮追加，过程记录可从 Git 历史查看。
当前重构目标是用底层公共证明消除上层重复义务，使全部代码严格低于 200,000 行。
规模口径及仍可推进的方向集中于 [ENGINEERING.md](markdown/ENGINEERING.md)，文档减量不计入代码指标。

## 许可证

本项目的原创代码与随附文档采用 [Apache License 2.0](LICENSE)，署名见 [NOTICE](NOTICE)。
第三方材料如有单独声明，仍遵循其原有许可。
