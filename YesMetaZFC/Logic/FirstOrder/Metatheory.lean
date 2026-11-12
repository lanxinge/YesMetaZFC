import YesMetaZFC.Logic.FirstOrder.Metatheory.Notation
import YesMetaZFC.Logic.FirstOrder.Metatheory.Basic
import YesMetaZFC.Logic.FirstOrder.Metatheory.Propositional
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Monotonicity
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Prenex
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Reordering
import YesMetaZFC.Logic.FirstOrder.Metatheory.Equality
import YesMetaZFC.Logic.FirstOrder.Metatheory.Equality.Basic
/-!
# 一阶元数理定理入口
该层在 `Derives` 核之上组织可复用的一般元数理定理，不承载具体理论公理，
机械证明可以消费公共自动化，但自动化基础层不反向导入本模块。统一的公式、
LN 操作与推导记号由 `Metatheory.Notation` 导出。
-/
