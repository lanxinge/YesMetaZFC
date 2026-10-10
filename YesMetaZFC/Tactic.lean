import YesMetaZFC.Tactic.FirstOrderDerives
import YesMetaZFC.Tactic.DerivesClosure
import YesMetaZFC.Tactic.DeriveFreeClosed
import YesMetaZFC.Tactic.TheoryInclusion
import YesMetaZFC.Tactic.FiniteBasisModels

/-!
# 轻量证明派生入口

命题推导、全称闭包、公式闭合性、理论包含及有限公理基模型装配各自消费显式合同。
证明由原推导构造子或普通 Lean 定理组成，策略不依赖通用搜索证明器。
领域受控约化 `deep_rfl` 随 `SetTheory.Definitional` 导入。
-/
