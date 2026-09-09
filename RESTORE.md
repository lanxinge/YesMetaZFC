# YesMetaZFC 工作区恢复

工具链固定为 `leanprover/lean4:v4.33.1`。源码无外部 Lake 包依赖；恢复后先确认
`lean --version` 与 `lake --version`，再运行 `lake --wfail build`。

## 规范源码

持续更新同一个 `YesMetaZFC-source.zip`，解压后根目录包含 `lakefile.toml`、
`lean-toolchain`、`YesMetaZFC.lean` 和 `YesMetaZFC/`。

- 当前基点为自由清理第二轮：806 个 Lean 文件、224,509 行，本轮独立净减 5,006 行。
  Lean 源码与下述 Google Drive 包逐字节相同；Git 发布入口为 `lanxinge/YesMetaZFC` 的
  `main` 分支。本次发布仅额外更新工程文档中的发布状态。
- 早期来源文件身份：`libfile_e921d03ce9e081919cde0a1656667ebd`；本轮未回写该旧包。
- [Google Drive 源码](https://drive.google.com/file/d/1b9gV-m5sT7DEVhgNNSzsV9ZrkpzYeUID/view)。
- Drive 源码目录：`1KFNGtD8yE-rp1Jk4UfH6BTbnpp9cQSEx`。

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

## 验证入口

- 默认完整库：`lake --wfail build`。
- 全部独立源模块及扫描工具：`bash scripts/check-all.sh`。
- 支撑统一验证入口：`PureSupportModels.support_models`、`PureZFCModels.models`。
- 当前 Rosser 已接入 `ReducedNaturalProofPresentation.presentation`，纯配置入口仍为 `PureRosser`。内部 ω、幂集界与轨迹归约入口为 `PureSourceInfinity`、`PureSourceBounds`、`PureNaturalRosserAgreement`。`ReducedRosser.delta0Sentence` 是支撑语言 Δ₀ 等价代表；`PureRosserDelta0` 已证明当前无参数纯闭句非 Δ₀，并构造纯 ∈ 的 Δ₀ 参数矩阵及裸 ZFC 推导等价。`PureSourceMappings`、`PureSourceArithmetic`、`PureSourceCoding` 已完成合法映射求值、内部加乘幂、配数和根编码对应，行归约接口已移除根值前提。最新全源严格构建已通过 808 个任务，扫描工具 320 个任务；`PureSourceLocalTests` 已完成局部行对应，`PureRosser.agreement` 与 `PureRosser.independent` 已闭合。参数定义未声称为 Δ₀。
- 证明范围和剩余数学义务见 `UNIFIED_VERIFICATION.md`。
