# 证明命名迁移基线

本文件记录证明命名迁移前的源码规模，用于比较新命名规范对源码字节量和信息密度的影响。

规范正文见 [ProofNaming.md](ProofNaming.md)。

## 一、基线快照

| 项目 | 数值 |
| --- | ---: |
| 测量日期 | 2026-08-03 |
| 基线提交 | `b442cc5` |
| Git 跟踪的 Lean 源文件 | 379 |
| 原始工作区源码字节数 | 10,716,128 |
| LF 归一化 UTF-8 字节数 | 10,713,547 |
| 换行归一化差值 | 2,581 |
| LF 归一化源码行数 | 222,507 |

### 1.1 统计口径

统计对象为：

```text
git ls-files -- '*.lean'
```

因此：

- 只统计 Git 已跟踪的 `.lean` 文件；
- 不统计 `.lake`、构建产物、缓存和临时文件；
- 原始工作区字节数使用文件实际字节长度；
- 归一化字节数将 `CRLF` 和 `CR` 统一为 `LF`，再按无 BOM UTF-8 计算；
- 后续命名迁移的主比较指标使用 LF 归一化 UTF-8 字节数；
- 源码行数在换行归一化后统计。

选择归一化指标是为了避免单纯的换行格式变化掩盖命名压缩或膨胀。

## 二、目录分布

以下为原始工作区字节数：

| 源码区域 | 文件数 | 字节数 | 行数 |
| --- | ---: | ---: | ---: |
| `YesMetaZFC/Logic` | 165 | 5,718,630 | 119,110 |
| `YesMetaZFC/SetTheory` | 111 | 1,782,391 | 36,540 |
| `YesMetaZFC/Automation` | 94 | 3,194,709 | 66,485 |
| `YesMetaZFC/LargeCardinals` | 3 | 6,125 | 142 |
| 根模块文件 | 6 | 14,273 | 230 |
| **合计** | **379** | **10,716,128** | **222,507** |

根模块文件包括：

```text
YesMetaZFC.lean
YesMetaZFC/Basic.lean
YesMetaZFC/Logic.lean
YesMetaZFC/SetTheory.lean
YesMetaZFC/Automation.lean
YesMetaZFC/LargeCardinals.lean
```

## 三、当前最大文件

| 文件 | 字节数 | 行数 |
| --- | ---: | ---: |
| `YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/CanonicalFormulaTraceLegality.lean` | 364,487 | 6,691 |
| `YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/GodelQuotation/FiniteSequenceSemantics.lean` | 253,444 | 4,314 |
| `YesMetaZFC/Automation/DAGCertificate.lean` | 231,081 | 4,394 |
| `YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/GodelQuotation/QuotationValue.lean` | 221,305 | 4,315 |
| `YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/InternalTheory/CanonicalFormulaTrace.lean` | 190,857 | 4,197 |

大文件暂不作为第一批迁移目标。先从依赖叶子和小型接口迁移，避免在高耦合模块中同时处理命名、调用点和架构边界。

## 四、从下往上的迁移顺序

迁移顺序按依赖关系决定，而不是按文件名或目录名决定。

### 4.1 纯定义叶子

当前扫描到的无导入叶子为：

```text
YesMetaZFC/Logic/Signature.lean
YesMetaZFC/Logic/HigherOrder/Signature.lean
```

这两个文件主要提供签名、类型和结构定义，不包含需要统一层后缀的证明接口。第一阶段只审计其公开名称，不为了形式统一而强行给纯数据类型增加证明层后缀。

### 4.2 第一批证明接口

当前最小的证明接口候选为：

```text
YesMetaZFC/Automation/HostNormalization/CoreRules.lean
```

当前规模：

```text
522 bytes
15 lines
1 个 theorem
```

该文件属于 Lean 宿主层，适合作为 `_l` 命名迁移的第一枚试点。迁移时必须同步检查 `prove_auto` 注册表和全部调用点。

### 4.3 后续低层接口

首批试点稳定后，依赖顺序优先处理：

```text
YesMetaZFC/Logic/FirstOrder/Context.lean
YesMetaZFC/Model/SetTheory/Theory.lean
YesMetaZFC/Logic/FirstOrder/Derivation/Equality.lean
YesMetaZFC/Logic/FirstOrder/Derivation/Structural.lean
```

这些模块分别涉及上下文满足、理论接口和推导基础，适合作为 `_m` 命名和数学单符号局部变量迁移的早期目标。

## 五、后续比较指标

每个迁移批次结束后至少记录：

```text
LF 归一化 UTF-8 总字节数
Lean 源文件数量
源码总行数
本批修改文件的字节变化
本批公开声明名称的字节变化
```

命名迁移的目标不是单纯追求更短的名字，而是同时满足：

1. 层级可以通过末尾 `_l`、`_m`、`_d` 立即识别；
2. 数学对象和命题关系保持可检索；
3. 局部上下文回到数学单符号；
4. 长英文角色名和重复架构前缀减少；
5. 归一化源码字节量长期下降；
6. 定理类型本身仍然承担完整的数学精度。

每次迁移都必须在 `lake build` 成功后更新本文件，并提交新的稳定基线。

## 六、第一批迁移快照

本批按依赖自底向上选择 20 个定义模块，先完成公开证明接口名称及其全仓库调用点迁移。由于调用点分布在上层模块，实际修改范围大于定义模块数量。

| 项目 | 数值 |
| --- | ---: |
| 迁移日期 | 2026-08-03 |
| 定义模块数 | 20 |
| 实际修改的 Lean 文件 | 117 |
| Git 变更新增行数 | 774 |
| Git 变更删除行数 | 774 |
| Lean 文件数 | 379 |
| 原始工作区源码字节数 | 10,712,847 |
| LF 归一化 UTF-8 字节数 | 10,710,266 |
| LF 归一化源码行数 | 222,507 |
| 相对基线的 LF 字节变化 | -3,281 |
| 相对基线的源码行变化 | 0 |

本批形成的主要层后缀接口包括：

- Lean 宿主层：`iff_self_true_l`、`attempt_closed_l`、`bind_attempt_closed_l`、`min_exists_of_wf_l`；
- 对象元理论层：`formula_sat_iff_m`、`eq_refl_m`、`forall_elim_m`、`cut_many_m`、`iff_refl_m`；
- 对象理论层：`foundation_sat_iff_d`、`collection_sat_iff_d`、`separation_sat_iff_d`、`proper_subset_sat_iff_d`。

`lake build` 已完成全部 380 个构建目标。选定的 20 个定义模块中，本批旧证明接口名称已清零；局部上下文变量的数学单符号化将在后续批次按同一依赖顺序继续推进，以避免把变量作用域重构和公开接口迁移混成一次不可审计的大改动。
