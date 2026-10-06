import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Copy
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.CopyConstant
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Los
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.ProjectionLaws
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.FullProjection
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.FullEmbedding
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceModel

/-! # 实际内部约化幂

ZF 中对指定的实际函数族收集等价类，构造投影与商关系，证明等价类核及代表元无关性；
仅需集合族含载体、成员有界及有限交的共同细化，不要求对全部背景子集向上封闭。
全部背景内部函数的代表族已在 ZFC 下证明完整内部代码的 Łoś 定理，并自动构造商赋值。
对具有实际全内部分离与统一化的传递源，`rs_satisfies_l` 已在 ZF 中证明源内部函数族的
完整内部 Łoś；真值逆像、见证统一化和对角函数均在源中实际构造。
`rs_los_assignment_l` 从实际 ω→G 图自动构造赋值空间、商赋值和全部公式码。
`rs_bounded_model_l` 在相对幂集闭包下构造源内有界函数集、类投影和商关系码；
它只收集源已有的函数，商构造仍使用同一等价类定义。
`rs_constant_embedding_l` 实际构造 x↦[cₓ] 的完整初等嵌入；`rs_projection_embedding_l`
从实际测度投影构造 [f]↦[f∘t] 的完整初等单射。恒等、复合和常值交换律均已证明。
完整函数族的常值与投影初等性也适用于任意关系，包括实际集合谓词的扩张。
`rs_copy_embedding_l` 从两源间的实际初等图及源测度成员对应构造完整初等复制，
图方程为 [f]↦[π(f)]；这里的商赋值代表选择按 ZFC 提供。
有限支撑全系统与完整初等良基极限由 LargeCardinal.ExtenderLimit 装配；
WoodinStrength 对 Vδ 源按指定秩选择长度，返回完整谓词初等嵌入与秩覆盖。
-/
