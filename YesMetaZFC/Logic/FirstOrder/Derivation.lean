import YesMetaZFC.Logic.FirstOrder.Derivation.Core
import YesMetaZFC.Logic.FirstOrder.Derivation.Quantifier
import YesMetaZFC.Model.FirstOrder.Soundness
import YesMetaZFC.Logic.FirstOrder.Derivation.Structural
import YesMetaZFC.Logic.FirstOrder.Derivation.Classical
import YesMetaZFC.Logic.FirstOrder.Derivation.Propositional
import YesMetaZFC.Logic.FirstOrder.Derivation.Consistency
import YesMetaZFC.Logic.FirstOrder.Derivation.Equality
/-!
# 一阶 Derives 证明核入口
这里统一导出新语义核的一阶推导对象、替换语义、结构接口、经典接口、一致性、
等词接口和 soundness 定理。完备性与自动化后端保持在更高层模块。
-/
