import YesMetaZFC.SetTheory.InnerModel.OD.Complexity
import YesMetaZFC.SetTheory.InnerModel.OD.Choice
import YesMetaZFC.SetTheory.InnerModel.OD.Order
import YesMetaZFC.SetTheory.InnerModel.OD.RelativeClosure
import YesMetaZFC.SetTheory.InnerModel.OD.Relations

/-! # OD：内部定义、原公式对应与单序数解码

任意（包括非标准）ZF 模型中，内部有限序数参数和内部公式码在 V 层上唯一
定义的对象，恰为原 Project 公式从序数参数唯一可定义的对象。公开类谓词
无参数，单序数解码单值且覆盖 OD，并支持集合分离及传递结构内的相对化。
Σ₂ 公式与原定义等价；每个对象有唯一最小序数代表，所得全局良序的严格初段
是实际集合。OD 参数的唯一可定义闭性保证规范选择集仍属于 OD。
OD[A] 把整个 A 作为固定参数；OD(A) 额外允许模型内部有限 A 参数列。
固定参数版本与原公式从 A 及序数参数唯一可定义等价，两种版本都满足有限定义闭性。
OD[A] 对笛卡尔积及任意原公式关系的集合化封闭；固定序数参数时 OD[A]=OD。
-/
