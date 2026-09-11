# Lean 构建缓存

本项目为固定的源码提交和 Lean 工具链生成两类缓存；每类分别构建五个平台。
下载、校验及恢复使用 Python 3.11 或以上的标准库，无须安装额外 Python 包。

## 缓存内容

| 类型 | 内容 | 适用场景 |
| --- | --- | --- |
| `lean`（默认） | 全部独立模块的 `.olean`、`.ilean`、Lake 跟踪文件，以及默认 `leanArts` 要求的生成 C/LLVM 文件和元数据 | 编辑器、阅读证明、继续形式化开发 |
| `full` | `lean` 的内容，加原生对象文件、静态库、共享库及 `prove_auto_sweep` 可执行程序 | 运行扫描工具、原生链接及完整开发环境 |

两个类型都包含本项目的 `LICENSE` 和 `NOTICE`，以及 `share/YesMetaZFC/third-party/lean4/`
下的工具链 `LICENSE`、`LICENSES`，保留相应第三方组件的许可说明。
不包含 Lean 工具链本体、Git 历史或研究资料。
完整包使用 Lake 默认的 `YesMetaZFC-<target>.tar.gz` 名称；轻量包增加 `-lean` 后缀。

| 平台 | CI 构建环境 | Lean 目标 |
| --- | --- | --- |
| Linux x86-64 | Ubuntu 22.04 | `x86_64-unknown-linux-gnu` |
| Linux ARM64 | Ubuntu 22.04 ARM | `aarch64-unknown-linux-gnu` |
| Windows x86-64 | Windows Server 2022 | `x86_64-w64-windows-gnu` |
| macOS Intel | macOS 15 Intel | `x86_64-apple-darwin` |
| macOS Apple Silicon | macOS 14 ARM | `aarch64-apple-darwin` |

平台从实际 `lean --version` 输出识别，不能跨平台混用。原生工具还要求兼容的系统运行库；
CI 的构建环境不等于对所有更早系统版本的兼容保证。

## 一条命令获取

安装 Git、Python 3.11+ 和 Lean 工具链管理器 elan，克隆仓库并切换到需要的提交后运行：

```bash
python scripts/lean_cache.py get
```

需要扫描程序、静态库和共享库时：

```bash
python scripts/lean_cache.py get --kind full
```

如果系统的 Python 命令名为 `python3`，将示例中的 `python` 替换为 `python3`。
首次调用 Lean 时，elan 按 `lean-toolchain` 安装工具链；缓存不替代这一步。
应在开始修改 Lean 源码或 Lake 配置之前取缓存。

脚本按照当前 Git 提交访问公开 Release `cache-<完整提交 SHA>`，不需要 GitHub 登录。
它先核对源码指纹、Lean 完整版本、目标平台与清单格式，再下载归档并验证 SHA-256。
解包在工作区内的临时目录完成，随后替换 `.lake/build`，以 `lake --no-build` 核对全部
相应目标均已就绪；核对失败会恢复原有构建目录。该检查确认无需重编译，不是重新验证所有证明。

如果这个提交尚未成功发布五个平台的缓存，命令会明确报错，不会用其他提交冒充。
可以等待对应的 [Lean CI](https://github.com/lanxinge/YesMetaZFC/actions/workflows/lean_action_ci.yml)
完成，或运行普通 `lake build` 从源码构建。分支和 PR 的成功构建包也可在对应 Actions 页面下载。

## 离线恢复

从同一次构建下载所需 `.tar.gz` 和同名 `.tar.gz.json`，放在同一目录，再运行：

```bash
python scripts/lean_cache.py restore --kind lean /path/to/YesMetaZFC-<target>-lean.tar.gz
python scripts/lean_cache.py restore --kind full /path/to/YesMetaZFC-<target>.tar.gz
```

源码仍须与清单一致。恢复成功后可以直接打开项目，或用 `lake exe prove_auto_sweep --help`
检查完整包中的扫描工具。

`lakefile.toml` 已配置 `releaseRepo` 和 `preferReleaseBuild`。其他项目将本库作为依赖时，
如果对应提交的缓存标签在本地可见，Lake 可以按其原生 Release 机制获取完整包；例如依赖
`cache-<完整提交 SHA>` 标签。仓库根项目的显式下载仍使用上面的 `get` 命令。

## CI 与长期存放

`.github/workflows/lean_action_ci.yml` 对推送、PR 和手动运行构建五个平台。流程为：

1. 检查缓存脚本，并按平台、工具链和 Lake 配置恢复 CI 增量缓存。
2. 使用 `lake --wfail build` 检查全部独立模块，并构建原生静态库、共享库和扫描工具。
3. 生成两类归档和 JSON 清单，分别实际恢复，并通过 `--no-build` 检查。
4. 保存 CI 增量缓存，上传保留 30 天的 Actions 下载包。
5. 原仓库 `main` 的全部平台通过后，将十个归档、对应清单及 `SHA256SUMS` 发布到同一
   `cache-<提交 SHA>` Release。上传先在草稿中完成，成功后公开；已经公开的同名快照不覆盖。

CI 增量缓存可能被 GitHub 淘汰，Actions 下载包有保留期限。公开 Release 是长期下载入口，
不会因为 Actions 包到期而自动过期。当前配置不会自动清理历史缓存 Release。
只有主分支的发布任务拥有 `contents: write` 权限，PR 构建不会发布缓存。

新配置需要提交并推送后才会在 GitHub 生效；本地构建不会自动启动远端工作流。

## 本地构建与制作缓存

```bash
# 全部独立模块与扫描工具，与原 check-all.sh 的默认范围一致。
python scripts/lean_cache.py build

# 只构建 Lean 模块。
python scripts/lean_cache.py build --library-only

# 加上静态库、共享库和扫描工具。
python scripts/lean_cache.py build --native

# 在干净源码上生成可发布的归档；默认输出到 tmp/lean-cache。
python scripts/lean_cache.py pack --kind lean
python scripts/lean_cache.py pack --kind full
```

`bash scripts/check-all.sh` 仍是全源检查入口，调用同一实现；支持 `--library-only`、
`--native` 和 `--no-build`。默认 `LEAN_NUM_THREADS=4`，可以显式覆盖。

在未提交的开发副本中试验本地打包，可额外传入 `--allow-dirty`。这样的包会标记源码未提交，
可以在相同源码副本中离线恢复，但公开下载和 CI 发布均拒绝它。打包期间若源码变化，同样失败。

脚本测试：`python -m unittest discover -s scripts/tests -v`。测试覆盖版本错配、归档损坏、
路径越界、特殊文件、恢复失败回滚以及发布集合完整性；不会引入 Lean 测试模块。
