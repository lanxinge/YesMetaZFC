import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Los
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.ProjectionLaws

/-! # 实际内部约化幂

ZF 中对指定的实际函数族收集等价类，构造投影与商关系，证明等价类核及代表元无关性；
仅需集合族含载体、成员有界及有限交的共同细化，不要求对全部背景子集向上封闭。
全部背景内部函数的代表族已在 ZFC 下证明完整内部代码的 Łoś 定理，并自动构造商赋值。
对实际初等嵌入正则 H(χ) 的传递源，`rs_satisfies_l` 已在 ZFC 中证明源内部函数族的
完整内部 Łoś；真值逆像、见证统一化和对角函数均在源中实际构造。
`rs_los_assignment_l` 从实际 ω→G 图自动构造赋值空间、商赋值和全部公式码。
`rs_constant_embedding_l` 实际构造 x↦[cₓ] 的完整初等嵌入；`rs_projection_embedding_l`
从实际测度投影构造 [f]↦[f∘t] 的完整初等单射。恒等、复合和常值交换律均已证明。
有限支撑有向系统及其良基性仍待组装。
-/
