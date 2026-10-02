# 地模型嵌入

地对象图编码、规范嵌入，以及有限列、内部语法、序数与共尾集保持。

[总索引](../../INDEX.md) · [上级目录](../README.md)

## 模块

按导入依赖先后排列；原平铺文件名供历史审查记录定位。

| 当前文件 | 原平铺文件 | 内容 |
| --- | --- | --- |
| [Graph.lean](Graph.lean) | `InternalGround.lean` | 地模型对象的无权小图呈现 |
| [Transfer.lean](Transfer.lean) | `GroundTransfer.lean` | 规范名称的地模型嵌入与有界结构保持 |
| [FiniteSequence.lean](FiniteSequence.lean) | `GroundFiniteSequence.lean` | 成员满嵌入保持全部内部有限列 |
| [Syntax.lean](Syntax.lean) | `GroundSyntax.lean` | 规范嵌入下内部语法码的绝对性 |
| [Cofinality.lean](Cofinality.lean) | `GroundCofinality.lean` | 旧集合嵌入下的序数反射与共尾集保持 |
| [NameRank.lean](NameRank.lean) | — | 名称支撑的实际秩图，以及扩张内的逐名称求值图 |
| [Ordinals.lean](Ordinals.lean) | — | 内部归纳证明序数名称值的秩界；`check_map_ordinals_l` 返回全部序数的旧原像 |
| [Collapse.lean](Collapse.lean) | — | 内部关系良基性回拉、坍塌图保持，以及 OD[A] 代码的 HOD[A] 坍塌恢复 |

不增加序数只要求地模型 ZF 和泛型性，不要求弱齐性、外部良基性或可数性。
归纳正文使用扩张中的实际求值图和旧秩图作参数，未把外部求值谓词直接交给内部归纳。

`collapse_hb_recover_l` 消费实际关系及总坍塌图。源模型构造传递值域，目标模型中以
坍塌唯一性识别原对象；不要求编码关系外延，适用于具有重复定义码的 HOD 呈现。
