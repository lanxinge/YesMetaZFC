# 工作区与工具链指路表

工具链固定为 `leanprover/lean4:v4.33.1`，无外部 Lake 包依赖。
普通 Linux 将工具链 `bin` 加入 `PATH`，确认 `lean --version`、`lake --version` 后构建。

## 规范源码

| 资源 | 位置与用途 |
| --- | --- |
| Git 仓库 | [lanxinge/YesMetaZFC](https://github.com/lanxinge/YesMetaZFC)，主分支 `main` |
| 持续更新的源码包 | [YesMetaZFC-source.zip](https://drive.google.com/file/d/1b9gV-m5sT7DEVhgNNSzsV9ZrkpzYeUID/view)；保持同一文件身份 |
| Drive 源码目录 | `1KFNGtD8yE-rp1Jk4UfH6BTbnpp9cQSEx` |
| 当前容器入口 | `source /workspace/scratch/fb4803f63959/activate-yesmetazfc.sh` |
| 当前工作区 | `/workspace/scratch/fb4803f63959/YesMetaZFC` |
| 当前容器工具链 | `/workspace/scratch/fb4803f63959/toolchains/lean-4.33.1-linux` |

恢复源码应得到 `lakefile.toml`、`lean-toolchain`、`YesMetaZFC.lean` 和 `YesMetaZFC/`。
当前源码包保存 [9045935](https://github.com/lanxinge/YesMetaZFC/commit/9045935fbbe9466cf246cad009acf1de4385d5a2)
之上的完整工作树，包含 D1、D2、任意内部 checked 轨迹反射及 D3，相关修改尚未推送 Git。
该节点有 924 个 Lean 模块；严格构建 921 个任务、全源构建 926 个任务及扫描工具
320 个任务通过。271 个入口的公理依赖审计未超出原有 32 项可信基。
成果入口为 `ReducedProvability.introspection`，详细接口和核验范围见
[TROPHIES.md](TROPHIES.md)、[UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md)。
恢复本节点应使用此源码包；仅检出上述 Git 提交不能恢复未提交的 D3 工作。

## 已有的 Lean Linux 运行时

运行时文件位于 Google Drive **根目录**；仅搜索项目子目录或全文索引可能漏掉二进制文件。
应读取根目录列表或直接按以下文件 ID 获取，不要据检索空结果断言运行时不存在。

| 文件 | Google Drive ID |
| --- | --- |
| 完整 `lean-4.33.1-linux.tar.zst` | `1-suvJyg6JwPsPCZ4H9JtHVbYTRfzCjxA` |
| 分片 `.001` | `1LdEjNO4AoLQtqFtqIOTk-2orUggUWin0` |
| 分片 `.002` | `1LDEmfOSe178i6wvDWR_pRFV8ojgqhFc8` |
| 分片 `.003` | `1-QpRt7Gq2pFdhYiBCRh2971ZYesEpCWt` |

三个分片各 190,135,078 字节，按 `.001`、`.002`、`.003` 顺序拼接为 570,405,234 字节。
完整压缩包 SHA-256：

```text
890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235
```

运行时校验后的 Lean 提交为 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`。
将解压目录的 `bin` 加入 `PATH`，在源码根目录构建；可设 `LEAN_NUM_THREADS=4` 控制并发资源。

在 Work Mode 获取大文件时，可以逐片请求原始下载，然后将返回的完整连接器文件引用
物化到本地。保留返回引用的 `sediment://` 前缀和原文件名；不要将其误当成源码文件身份。

## 容器兼容问题

本次环境的 `/proc/<进程号>/exe` 与进程命名空间存在不一致，运行时定位失败。
工作区使用一个仅将该路径查询改为 `/proc/self/exe` 的 `readlink` 兼容层恢复可执行文件定位。
它不修改 Lean、内核验证或证明内容；普通 Linux 环境无需此兼容层。
兼容层、运行时、下载文件和构建缓存均不进入规范源码包。

## 使用入口

| 要做的工作 | 入口 |
| --- | --- |
| 构建默认完整库 | `lake --wfail build` |
| 覆盖全部独立源模块及扫描工具 | `bash scripts/check-all.sh` |
| 找公共证明和后续重构方向 | [ENGINEERING.md](ENGINEERING.md) |
| 找纯模型、119 条原公理验证与 Rosser 终局 | [UNIFIED_VERIFICATION.md](UNIFIED_VERIFICATION.md) |
| 查证书格式与对象图 | [NAT_DECODING.md](NAT_DECODING.md) |

源码包不包含运行时、兼容层、构建缓存和临时分析；恢复时分别处理这些资源。
