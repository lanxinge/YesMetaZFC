import YesMetaZFC.SetTheory.Collapse.Uniqueness
import YesMetaZFC.SetTheory.Collapse.Transport
import YesMetaZFC.SetTheory.Collapse.Cardinality
import YesMetaZFC.SetTheory.Collapse.RelationExistence
import YesMetaZFC.SetTheory.Collapse.RelationIso
import YesMetaZFC.SetTheory.Collapse.RelationBounded
import YesMetaZFC.SetTheory.Collapse.RelationMap

/-! # 模型内部隶属子结构的 Mostowski 坍塌

KPi 中构造唯一传递坍塌及实际双射图，传输原公式并固定传递参数的子集。
ZF 中另提供任意内部集合良基关系的总坍塌图、唯一值及传递值域；非外延关系允许重复值。
关系外延时，`wc_iso_l` 进一步给出到传递值域的实际双射及成员关系同构。
`Wc_iso_d` 是同一同构的 Δ₀ 证书；它直接推出原关系的良基性和外延性，
其传递像由原关系唯一确定，供模型内计算与跨模型识别使用。
`Wc_map_d` 给出任意关系的 Δ₀ 塌缩证书；其图仅需 KP 即可反映背景良基性。
-/
