# 规范名称

规范名称的递归、唯一性、求值还原，以及成员、关系、ω 和地函数应用。

[总索引](../../INDEX.md) · [上级目录](../README.md)

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [Syntax.lean](Syntax.lean) | `InternalCheckSyntax.lean` | 规范名称的内部递归图 |
| [Basic.lean](Basic.lean) | `InternalCheck.lean` | 规范名称递归的存在性与唯一性 |
| [Valuation.lean](Valuation.lean) | `InternalCheckVal.lean` | 规范名称解释还原地模型对象 |
| [Model.lean](Model.lean) | `InternalCheckModel.lean` | 从原 ZF 公理取得规范名称递归 |
| [Forcing.lean](Forcing.lean) | `InternalCheckForcing.lean` | 规范名称在泛型商中的忠实性 |
| [Relation.lean](Relation.lean) | `InternalCheckRelation.lean` | 旧成员与关系的规范名称力迫 |
| [Application.lean](Application.lean) | `InternalCheckApplication.lean` | 地函数应用于任意名称 |
| [Order.lean](Order.lean) | `InternalCheckOrder.lean` | 旧预序在规范名称下的实际力迫证书 |
| [Omega.lean](Omega.lean) | `InternalCheckOmega.lean` | 内部 ω 的规范名称力迫 |
| [Realization.lean](Realization.lean) | `InternalCheckRealization.lean` | 规范名称递归的小图地模型实例 |
