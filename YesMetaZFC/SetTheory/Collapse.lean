import YesMetaZFC.SetTheory.Collapse.Uniqueness
import YesMetaZFC.SetTheory.Collapse.Transport
import YesMetaZFC.SetTheory.Collapse.Cardinality
import YesMetaZFC.SetTheory.Collapse.RelationExistence
import YesMetaZFC.SetTheory.Collapse.RelationIso

/-! # 模型内部隶属子结构的 Mostowski 坍塌

KPi 中构造唯一传递坍塌及实际双射图，传输原公式并固定传递参数的子集。
ZF 中另提供任意内部集合良基关系的总坍塌图、唯一值及传递值域；非外延关系允许重复值。
关系外延时，`wc_iso_l` 进一步给出到传递值域的实际双射及成员关系同构。
-/
