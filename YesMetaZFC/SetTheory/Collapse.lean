import YesMetaZFC.SetTheory.Collapse.Uniqueness
import YesMetaZFC.SetTheory.Collapse.Transport
import YesMetaZFC.SetTheory.Collapse.Cardinality
import YesMetaZFC.SetTheory.Collapse.RelationExistence
import YesMetaZFC.SetTheory.Collapse.RelationIso
import YesMetaZFC.SetTheory.Collapse.RelationBounded
import YesMetaZFC.SetTheory.Collapse.RelationMap
import YesMetaZFC.SetTheory.Collapse.FunctionSupport

/-! # 模型内部隶属子结构的 Mostowski 坍塌

KPi 中从成员同余条件构造唯一传递坍塌及实际满映射图；源外延时进一步得到双射。
完整原公式沿同一图运输，传递参数的子集被固定，异坐标 Kuratowski 对可回收原坐标。
常零与后继实数在 KP 中实际构造；其正确坍塌解释通过内部有界归纳恢复全部自然数支撑。
函数图及定义域固定时，其有序对成员也逐点固定；两张特殊图由此固定全部零或后继值实数。
ZF 中另提供任意内部集合良基关系的总坍塌图、唯一值及传递值域；非外延关系允许重复值。
关系外延时，`wc_iso_l` 进一步给出到传递值域的实际双射及成员关系同构。
`Wc_iso_d` 是同一同构的 Δ₀ 证书；它直接推出原关系的良基性和外延性，
其传递像由原关系唯一确定，供模型内计算与跨模型识别使用。
`Wc_map_d` 给出任意关系的 Δ₀ 塌缩证书；其图仅需 KP 即可反映背景良基性。
-/
