# 环境恢复与构建

源码以当前 Git 工作区及所选提交为准，仓库为
[lanxinge/YesMetaZFC](https://github.com/lanxinge/YesMetaZFC)。
恢复或切换版本前先检查已有未提交改动，避免用旧源码覆盖当前工作。

## 工具链

工具链由根目录 [lean-toolchain](../lean-toolchain) 固定为 `leanprover/lean4:v4.33.1`。
项目无外部 Lake 包依赖；全源检查和缓存脚本需要 Python 3.11 或以上，无额外 Python 包依赖。

使用 elan 时，在项目根目录运行命令，由它选择项目工具链。手动安装时，将相同版本、
匹配当前平台的工具链 `bin` 加入 `PATH`。确认源码包含 `lakefile.toml`、`lean-toolchain`、
`YesMetaZFC.lean` 和 `YesMetaZFC/`，再检查：

```text
lean --version
lake --version
```

## 构建与核验

```text
lake --wfail build
python scripts/lean_cache.py build
```

第一条构建默认入口；第二条枚举全部独立 Lean 模块，覆盖默认导入图之外的源码。
需要原生对象、静态库和共享库时，运行 `python scripts/lean_cache.py build --native`。
Bash 环境也可使用 `bash scripts/check-all.sh`，它调用同一全源构建实现。
`lake env` 只准备运行环境，不会自动构建依赖。

并行度通过 `LEAN_NUM_THREADS` 配置。需要将 Windows 当前用户的默认值设为 24 时：

```powershell
[Environment]::SetEnvironmentVariable('LEAN_NUM_THREADS', '24', 'User')
$env:LEAN_NUM_THREADS = '24'
```

第一行持久化设置，第二行使当前 PowerShell 立即使用该值；其他已打开的终端或编辑器需重启。
Bash 中可用 `LEAN_NUM_THREADS=24 lake --wfail build` 指定本次构建的并行度。

## 缓存与接口导航

构建缓存须匹配所选源码提交、工具链和平台；下载与离线校验见 [CACHE.md](CACHE.md)。
旧机器路径、容器兼容层和临时下载文件不属于项目恢复要求。

| 工作 | 入口 |
| --- | --- |
| 公共证明接口与检查性能 | [ENGINEERING.md](ENGINEERING.md) |
| 数学成果与准确前提 | [TROPHIES.md](TROPHIES.md) |
| 公理覆盖、模型对应与可信依赖 | [UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md) |
| 证书格式、对象图与纯公式编码 | [NAT_DECODING.md](NAT_DECODING.md) |
| 轻量策略与模块边界 | [PROVER_SPLIT.md](PROVER_SPLIT.md) |

构建和审计结果只对实际运行时的源码有效，不从历史日志推断当前工作区已经通过。
