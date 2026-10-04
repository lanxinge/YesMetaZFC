import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Union
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.AscendingDescent

/-! # 通用内部定向系统与直接极限

`Di_system_d` 用实际集合存储指标、带标号元素及全部过渡映射。
`di_limit_exists_l` 在 ZF 中构造商和极限关系；`di_stage_l` 构造各分量的规范嵌入；
`di_factor_rel_l` 给出关系保持映射的唯一分解。非空极限由 `di_model_exists_l` 编成实际结构。
`di_sigma_wf_l` 在 ZF＋DC 下证明可数定向的良基分量系统有良基极限；
`di_cone_wf_l` 在 ZF 内处理已有实际良基目标的相容锥。
`di_union_l` 自动构造任意定向子结构族，`di_power_limit_l` 给出可数定向判据的实际实例。
`di_wf_of_no_step_l` 把非良基极限转为指标递增的内部下降链。
有限支撑测度族的实际系统与良基极限由 LargeCardinal.ExtenderLimit 提供；极限完整内部初等性尚待证明。
-/
