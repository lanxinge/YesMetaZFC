import YesMetaZFC.Model.Zermelo.Model
import YesMetaZFC.Model.Zermelo.Feedback
import YesMetaZFC.Model.Zermelo.HullLimits
import YesMetaZFC.Model.Zermelo.CheckedLift

/-! # 稳定集合树模型与保真升层入口

`model` 是稳定真值背景中的具体模型，`rules` 验证原经典 Hilbert 核，
`models_z` 验证原 Z 理论的全部公理及模式，`z_consistent` 给出原推导的一致性。
依赖断言同时覆盖模型数据、经典规则、全部公理模式与非平凡性。
检查器捕获层继承既有检查核的公理依赖，另在 CheckedLift 中明确审计。
-/

/-- info: 'YesMetaZFC.Model.Zermelo.model' does not depend on any axioms -/
#guard_msgs in
#print axioms YesMetaZFC.Model.Zermelo.model

/-- info: 'YesMetaZFC.Model.Zermelo.rules' does not depend on any axioms -/
#guard_msgs in
#print axioms YesMetaZFC.Model.Zermelo.rules

/-- info: 'YesMetaZFC.Model.Zermelo.models_z' does not depend on any axioms -/
#guard_msgs in
#print axioms YesMetaZFC.Model.Zermelo.models_z

/-- info: 'YesMetaZFC.Model.Zermelo.z_consistent' does not depend on any axioms -/
#guard_msgs in
#print axioms YesMetaZFC.Model.Zermelo.z_consistent

/-- info: 'YesMetaZFC.Model.Zermelo.V.nontrivial' does not depend on any axioms -/
#guard_msgs in
#print axioms YesMetaZFC.Model.Zermelo.V.nontrivial
