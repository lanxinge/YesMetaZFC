# 全阶段共同小模型

阶段索引的共同运算、统一 H(χ) 与 N、提升证书和实际交集 club。

[总索引](../../INDEX.md) · [上级目录](../README.md)

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [IndexedSyntax.lean](IndexedSyntax.lean) | `InternalGenericIndexedSyntax.lean` | 以阶段编号索引的共同泛型选择图 |
| [ClosedSyntax.lean](ClosedSyntax.lean) | `InternalGenericClosedSyntax.lean` | 共同泛型闭包的内部证书 |
| [Indexed.lean](Indexed.lean) | `InternalGenericIndexed.lean` | 所有阶段共用的实际判定与选择图 |
| [IndexedLift.lean](IndexedLift.lean) | `InternalGenericIndexedLift.lean` | 一个内部小模型在全部成员阶段的泛型提升 |
| [ClosedLift.lean](ClosedLift.lean) | `InternalGenericClosedLift.lean` | 对指定闭集 N 的 H(χ) 泛型提升 |
| [IndexedHull.lean](IndexedHull.lean) | `InternalGenericIndexedHull.lean` | 全阶段共用的内部初等小模型 |
| [Basic.lean](Basic.lean) | `InternalGenericFamily.lean` | 整个阶段族的 H(χ) 与共同 N 一键装配 |
| [Syntax.lean](Syntax.lean) | `InternalGenericFamilySyntax.lean` | 全阶段 H(χ) 提升的内部力迫证书 |
| [Forcing.lean](Forcing.lean) | `InternalGenericFamilyForcing.lean` | 从共同小模型到全阶段内部力迫证书 |
| [ClosedForcing.lean](ClosedForcing.lean) | `InternalGenericClosedForcing.lean` | 指定闭集 N 的全阶段内部提升证书 |
| [Trace.lean](Trace.lean) | `InternalGenericTrace.lean` | 同时支持地模型初等性与泛型闭包的交集 club |
